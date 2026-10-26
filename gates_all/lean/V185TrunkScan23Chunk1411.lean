import V185TrunkScan23Chunk1410

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8358386 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_8358386 : Nat := 118140960795 + 8358386 * 2 ^ 59
def prefixEnd_8358386 : Nat := 4983230072969 + 3 ^ 40 * 8358386 * 2
def baseEnd_8358386 : Nat := 4291869513811040010035489

theorem tailTrace_8358386 : CollatzResearch.WordTrace tailWord_8358386 prefixEnd_8358386 4291869513811040010035489 := by
  unfold tailWord_8358386
  simp only [CollatzResearch.WordTrace]
  refine ⟨76213845574250623881233753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203236921531334997016623341 76213845574250623881233753)
  ·
    refine ⟨57160384180687967910925315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76213845574250623881233753 57160384180687967910925315)
    ·
      refine ⟨85740576271031951866387973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57160384180687967910925315 85740576271031951866387973)
      ·
        refine ⟨16076358050818490974947745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85740576271031951866387973 16076358050818490974947745)
        ·
          refine ⟨12057268538113868231210809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16076358050818490974947745 12057268538113868231210809)
          ·
            refine ⟨9042951403585401173408107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12057268538113868231210809 9042951403585401173408107)
            ·
              refine ⟨13564427105378101760112161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042951403585401173408107 13564427105378101760112161)
              ·
                refine ⟨10173320329033576320084121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13564427105378101760112161 10173320329033576320084121)
                ·
                  refine ⟨7629990246775182240063091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10173320329033576320084121 7629990246775182240063091)
                  ·
                    refine ⟨11444985370162773360094637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7629990246775182240063091 11444985370162773360094637)
                    ·
                      refine ⟨4291869513811040010035489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444985370162773360094637 4291869513811040010035489)
                      ·
                        rfl

theorem cell23_8358386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_8358386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358386 prefixEnd_8358386 := by exact prefixLift 8358386
  have htrace : WordTrace (prefixWord ++ tailWord_8358386) baseStart_8358386 baseEnd_8358386 := by
    simpa [prefixWord, tailWord_8358386, baseEnd_8358386] using wordTrace_append hprefix tailTrace_8358386
  have hstable : (prefixWord ++ tailWord_8358386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358386).length < 2 ^ (prefixWord ++ tailWord_8358386).sum := by decide
  have hdescent : baseEnd_8358386 < baseStart_8358386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358392 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 4, 2, 2]
def baseStart_8358392 : Nat := 118140960795 + 8358392 * 2 ^ 59
def prefixEnd_8358392 : Nat := 4983230072969 + 3 ^ 40 * 8358392 * 2
def baseEnd_8358392 : Nat := 4291872594694966986560461

theorem tailTrace_8358392 : CollatzResearch.WordTrace tailWord_8358392 prefixEnd_8358392 4291872594694966986560461 := by
  unfold tailWord_8358392
  simp only [CollatzResearch.WordTrace]
  refine ⟨152427800567490379274826715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203237067423320505699768953 152427800567490379274826715)
  ·
    refine ⟨228641700851235568912240073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152427800567490379274826715 228641700851235568912240073)
    ·
      refine ⟨171481275638426676684180055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228641700851235568912240073 171481275638426676684180055)
      ·
        refine ⟨257221913457640015026270083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171481275638426676684180055 257221913457640015026270083)
        ·
          refine ⟨385832870186460022539405125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257221913457640015026270083 385832870186460022539405125)
          ·
            refine ⟨72343663159961254226138461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385832870186460022539405125 72343663159961254226138461)
            ·
              refine ⟨27128873684985470334801923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72343663159961254226138461 27128873684985470334801923)
              ·
                refine ⟨40693310527478205502202885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27128873684985470334801923 40693310527478205502202885)
                ·
                  refine ⟨7629995723902163531663041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40693310527478205502202885 7629995723902163531663041)
                  ·
                    refine ⟨5722496792926622648747281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7629995723902163531663041 5722496792926622648747281)
                    ·
                      refine ⟨4291872594694966986560461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722496792926622648747281 4291872594694966986560461)
                      ·
                        rfl

theorem cell23_8358392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_8358392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358392 prefixEnd_8358392 := by exact prefixLift 8358392
  have htrace : WordTrace (prefixWord ++ tailWord_8358392) baseStart_8358392 baseEnd_8358392 := by
    simpa [prefixWord, tailWord_8358392, baseEnd_8358392] using wordTrace_append hprefix tailTrace_8358392
  have hstable : (prefixWord ++ tailWord_8358392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358392).length < 2 ^ (prefixWord ++ tailWord_8358392).sum := by decide
  have hdescent : baseEnd_8358392 < baseStart_8358392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358413 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_8358413 : Nat := 118140960795 + 8358413 * 2 ^ 59
def prefixEnd_8358413 : Nat := 4983230072969 + 3 ^ 40 * 8358413 * 2
def baseEnd_8358413 : Nat := 4291883377788711404397865

theorem tailTrace_8358413 : CollatzResearch.WordTrace tailWord_8358413 prefixEnd_8358413 4291883377788711404397865 := by
  unfold tailWord_8358413
  simp only [CollatzResearch.WordTrace]
  refine ⟨304856367067904679136167893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203237578045269786090778595 304856367067904679136167893)
  ·
    refine ⟨7145071103154015917253935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 304856367067904679136167893 7145071103154015917253935)
    ·
      refine ⟨10717606654731023875880903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7145071103154015917253935 10717606654731023875880903)
      ·
        refine ⟨16076409982096535813821355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10717606654731023875880903 16076409982096535813821355)
        ·
          refine ⟨24114614973144803720732033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16076409982096535813821355 24114614973144803720732033)
          ·
            refine ⟨18085961229858602790549025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24114614973144803720732033 18085961229858602790549025)
            ·
              refine ⟨13564470922393952092911769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18085961229858602790549025 13564470922393952092911769)
              ·
                refine ⟨10173353191795464069683827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13564470922393952092911769 10173353191795464069683827)
                ·
                  refine ⟨15260029787693196104525741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10173353191795464069683827 15260029787693196104525741)
                  ·
                    refine ⟨5722511170384948539197153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15260029787693196104525741 5722511170384948539197153)
                    ·
                      refine ⟨4291883377788711404397865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722511170384948539197153 4291883377788711404397865)
                      ·
                        rfl

theorem cell23_8358413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_8358413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358413 prefixEnd_8358413 := by exact prefixLift 8358413
  have htrace : WordTrace (prefixWord ++ tailWord_8358413) baseStart_8358413 baseEnd_8358413 := by
    simpa [prefixWord, tailWord_8358413, baseEnd_8358413] using wordTrace_append hprefix tailTrace_8358413
  have hstable : (prefixWord ++ tailWord_8358413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358413).length < 2 ^ (prefixWord ++ tailWord_8358413).sum := by decide
  have hdescent : baseEnd_8358413 < baseStart_8358413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358475 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 3, 4]
def baseStart_8358475 : Nat := 118140960795 + 8358475 * 2 ^ 59
def prefixEnd_8358475 : Nat := 4983230072969 + 3 ^ 40 * 8358475 * 2
def baseEnd_8358475 : Nat := 1430638404529763387274193

theorem tailTrace_8358475 : CollatzResearch.WordTrace tailWord_8358475 prefixEnd_8358475 1430638404529763387274193 := by
  unfold tailWord_8358475
  simp only [CollatzResearch.WordTrace]
  refine ⟨304858628393680063724924879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203239085595786709149949919 304858628393680063724924879)
  ·
    refine ⟨457287942590520095587387319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304858628393680063724924879 457287942590520095587387319)
    ·
      refine ⟨685931913885780143381080979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457287942590520095587387319 685931913885780143381080979)
      ·
        refine ⟨1028897870828670215071621469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685931913885780143381080979 1028897870828670215071621469)
        ·
          refine ⟨385836701560751330651858051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1028897870828670215071621469 385836701560751330651858051)
          ·
            refine ⟨578755052341126995977787077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385836701560751330651858051 578755052341126995977787077)
            ·
              refine ⟨108516572313961311745835077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 578755052341126995977787077 108516572313961311745835077)
              ·
                refine ⟨20346857308867745952344077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108516572313961311745835077 20346857308867745952344077)
                ·
                  refine ⟨7630071490825404732129029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20346857308867745952344077 7630071490825404732129029)
                  ·
                    refine ⟨1430638404529763387274193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7630071490825404732129029 1430638404529763387274193)
                    ·
                      rfl

theorem cell23_8358475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 4].length) (baseStart_8358475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358475 prefixEnd_8358475 := by exact prefixLift 8358475
  have htrace : WordTrace (prefixWord ++ tailWord_8358475) baseStart_8358475 baseEnd_8358475 := by
    simpa [prefixWord, tailWord_8358475, baseEnd_8358475] using wordTrace_append hprefix tailTrace_8358475
  have hstable : (prefixWord ++ tailWord_8358475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358475).length < 2 ^ (prefixWord ++ tailWord_8358475).sum := by decide
  have hdescent : baseEnd_8358475 < baseStart_8358475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358482 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_8358482 : Nat := 118140960795 + 8358482 * 2 ^ 59
def prefixEnd_8358482 : Nat := 4983230072969 + 3 ^ 40 * 8358482 * 2
def baseEnd_8358482 : Nat := 4291918807953871634435047

theorem tailTrace_8358482 : CollatzResearch.WordTrace tailWord_8358482 prefixEnd_8358482 4291918807953871634435047 := by
  unfold tailWord_8358482
  simp only [CollatzResearch.WordTrace]
  refine ⟨76214720926163675980107425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203239255803103135946953133 76214720926163675980107425)
  ·
    refine ⟨57161040694622756985080569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76214720926163675980107425 57161040694622756985080569)
    ·
      refine ⟨42870780520967067738810427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57161040694622756985080569 42870780520967067738810427)
      ·
        refine ⟨64306170781450601608215641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42870780520967067738810427 64306170781450601608215641)
        ·
          refine ⟨48229628086087951206161731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64306170781450601608215641 48229628086087951206161731)
          ·
            refine ⟨72344442129131926809242597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48229628086087951206161731 72344442129131926809242597)
            ·
              refine ⟨13564582899212236276732987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72344442129131926809242597 13564582899212236276732987)
              ·
                refine ⟨20346874348818354415099481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13564582899212236276732987 20346874348818354415099481)
                ·
                  refine ⟨15260155761613765811324611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20346874348818354415099481 15260155761613765811324611)
                  ·
                    refine ⟨22890233642420648716986917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15260155761613765811324611 22890233642420648716986917)
                    ·
                      refine ⟨4291918807953871634435047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22890233642420648716986917 4291918807953871634435047)
                      ·
                        rfl

theorem cell23_8358482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_8358482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358482 prefixEnd_8358482 := by exact prefixLift 8358482
  have htrace : WordTrace (prefixWord ++ tailWord_8358482) baseStart_8358482 baseEnd_8358482 := by
    simpa [prefixWord, tailWord_8358482, baseEnd_8358482] using wordTrace_append hprefix tailTrace_8358482
  have hstable : (prefixWord ++ tailWord_8358482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358482).length < 2 ^ (prefixWord ++ tailWord_8358482).sum := by decide
  have hdescent : baseEnd_8358482 < baseStart_8358482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358485 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_8358485 : Nat := 118140960795 + 8358485 * 2 ^ 59
def prefixEnd_8358485 : Nat := 4983230072969 + 3 ^ 40 * 8358485 * 2
def baseEnd_8358485 : Nat := 4291920348395835122697533

theorem tailTrace_8358485 : CollatzResearch.WordTrace tailWord_8358485 prefixEnd_8358485 4291920348395835122697533 := by
  unfold tailWord_8358485
  simp only [CollatzResearch.WordTrace]
  refine ⟨304858993123643835432788909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203239328749095890288525939 304858993123643835432788909)
  ·
    refine ⟨114322122421366438287295841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304858993123643835432788909 114322122421366438287295841)
    ·
      refine ⟨85741591816024828715471881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114322122421366438287295841 85741591816024828715471881)
      ·
        refine ⟨64306193862018621536603911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85741591816024828715471881 64306193862018621536603911)
        ·
          refine ⟨96459290793027932304905867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64306193862018621536603911 96459290793027932304905867)
          ·
            refine ⟨144688936189541898457358801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96459290793027932304905867 144688936189541898457358801)
            ·
              refine ⟨108516702142156423843019101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144688936189541898457358801 108516702142156423843019101)
              ·
                refine ⟨40693763303308658941132163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108516702142156423843019101 40693763303308658941132163)
                ·
                  refine ⟨61040644954962988411698245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40693763303308658941132163 61040644954962988411698245)
                  ·
                    refine ⟨11445120929055560327193421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61040644954962988411698245 11445120929055560327193421)
                    ·
                      refine ⟨4291920348395835122697533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11445120929055560327193421 4291920348395835122697533)
                      ·
                        rfl

theorem cell23_8358485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_8358485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358485 prefixEnd_8358485 := by exact prefixLift 8358485
  have htrace : WordTrace (prefixWord ++ tailWord_8358485) baseStart_8358485 baseEnd_8358485 := by
    simpa [prefixWord, tailWord_8358485, baseEnd_8358485] using wordTrace_append hprefix tailTrace_8358485
  have hstable : (prefixWord ++ tailWord_8358485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358485).length < 2 ^ (prefixWord ++ tailWord_8358485).sum := by decide
  have hdescent : baseEnd_8358485 < baseStart_8358485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358488 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 10]
def baseStart_8358488 : Nat := 118140960795 + 8358488 * 2 ^ 59
def prefixEnd_8358488 : Nat := 4983230072969 + 3 ^ 40 * 8358488 * 2
def baseEnd_8358488 : Nat := 476880209870866512328891

theorem tailTrace_8358488 : CollatzResearch.WordTrace tailWord_8358488 prefixEnd_8358488 476880209870866512328891 := by
  unfold tailWord_8358488
  simp only [CollatzResearch.WordTrace]
  refine ⟨152429551271316483472574059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203239401695088644630098745 152429551271316483472574059)
  ·
    refine ⟨228644326906974725208861089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152429551271316483472574059 228644326906974725208861089)
    ·
      refine ⟨171483245180231043906645817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228644326906974725208861089 171483245180231043906645817)
      ·
        refine ⟨128612433885173282929984363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171483245180231043906645817 128612433885173282929984363)
        ·
          refine ⟨192918650827759924394976545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128612433885173282929984363 192918650827759924394976545)
          ·
            refine ⟨144688988120819943296232409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192918650827759924394976545 144688988120819943296232409)
            ·
              refine ⟨108516741090614957472174307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144688988120819943296232409 108516741090614957472174307)
              ·
                refine ⟨162775111635922436208261461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108516741090614957472174307 162775111635922436208261461)
                ·
                  refine ⟨476880209870866512328891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 162775111635922436208261461 476880209870866512328891)
                  ·
                    rfl

theorem cell23_8358488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 10].length) (baseStart_8358488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358488 prefixEnd_8358488 := by exact prefixLift 8358488
  have htrace : WordTrace (prefixWord ++ tailWord_8358488) baseStart_8358488 baseEnd_8358488 := by
    simpa [prefixWord, tailWord_8358488, baseEnd_8358488] using wordTrace_append hprefix tailTrace_8358488
  have hstable : (prefixWord ++ tailWord_8358488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358488).length < 2 ^ (prefixWord ++ tailWord_8358488).sum := by decide
  have hdescent : baseEnd_8358488 < baseStart_8358488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358530 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_8358530 : Nat := 118140960795 + 8358530 * 2 ^ 59
def prefixEnd_8358530 : Nat := 4983230072969 + 3 ^ 40 * 8358530 * 2
def baseEnd_8358530 : Nat := 1430647818341762482211609

theorem tailTrace_8358530 : CollatzResearch.WordTrace tailWord_8358530 prefixEnd_8358530 1430647818341762482211609 := by
  unfold tailWord_8358530
  simp only [CollatzResearch.WordTrace]
  refine ⟨76215158602120202029544261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203240422938987205412118029 76215158602120202029544261)
  ·
    refine ⟨14290342237897537880539549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76215158602120202029544261 14290342237897537880539549)
    ·
      refine ⟨5358878339211576705202331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14290342237897537880539549 5358878339211576705202331)
      ·
        refine ⟨8038317508817365057803497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358878339211576705202331 8038317508817365057803497)
        ·
          refine ⟨6028738131613023793352623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8038317508817365057803497 6028738131613023793352623)
          ·
            refine ⟨9043107197419535690028935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028738131613023793352623 9043107197419535690028935)
            ·
              refine ⟨13564660796129303535043403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9043107197419535690028935 13564660796129303535043403)
              ·
                refine ⟨20346991194193955302565105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13564660796129303535043403 20346991194193955302565105)
                ·
                  refine ⟨15260243395645466476923829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20346991194193955302565105 15260243395645466476923829)
                  ·
                    refine ⟨1430647818341762482211609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15260243395645466476923829 1430647818341762482211609)
                    ·
                      rfl

theorem cell23_8358530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_8358530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358530 prefixEnd_8358530 := by exact prefixLift 8358530
  have htrace : WordTrace (prefixWord ++ tailWord_8358530) baseStart_8358530 baseEnd_8358530 := by
    simpa [prefixWord, tailWord_8358530, baseEnd_8358530] using wordTrace_append hprefix tailTrace_8358530
  have hstable : (prefixWord ++ tailWord_8358530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358530).length < 2 ^ (prefixWord ++ tailWord_8358530).sum := by decide
  have hdescent : baseEnd_8358530 < baseStart_8358530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358535 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 3, 5]
def baseStart_8358535 : Nat := 118140960795 + 8358535 * 2 ^ 59
def prefixEnd_8358535 : Nat := 4983230072969 + 3 ^ 40 * 8358535 * 2
def baseEnd_8358535 : Nat := 1430648674142853309024101

theorem tailTrace_8358535 : CollatzResearch.WordTrace tailWord_8358535 prefixEnd_8358535 1430648674142853309024101 := by
  unfold tailWord_8358535
  simp only [CollatzResearch.WordTrace]
  refine ⟨304860816773462693972109059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203240544515641795981406039 304860816773462693972109059)
  ·
    refine ⟨457291225160194040958163589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304860816773462693972109059 457291225160194040958163589)
    ·
      refine ⟨85742104717536382679655673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457291225160194040958163589 85742104717536382679655673)
      ·
        refine ⟨64306578538152287009741755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85742104717536382679655673 64306578538152287009741755)
        ·
          refine ⟨96459867807228430514612633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64306578538152287009741755 96459867807228430514612633)
          ·
            refine ⟨72344900855421322885959475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96459867807228430514612633 72344900855421322885959475)
            ·
              refine ⟨108517351283131984328939213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72344900855421322885959475 108517351283131984328939213)
              ·
                refine ⟨40694006731174494123352205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108517351283131984328939213 40694006731174494123352205)
                ·
                  refine ⟨15260252524190435296257077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40694006731174494123352205 15260252524190435296257077)
                  ·
                    refine ⟨1430648674142853309024101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15260252524190435296257077 1430648674142853309024101)
                    ·
                      rfl

theorem cell23_8358535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_8358535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358535 prefixEnd_8358535 := by exact prefixLift 8358535
  have htrace : WordTrace (prefixWord ++ tailWord_8358535) baseStart_8358535 baseEnd_8358535 := by
    simpa [prefixWord, tailWord_8358535, baseEnd_8358535] using wordTrace_append hprefix tailTrace_8358535
  have hstable : (prefixWord ++ tailWord_8358535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358535).length < 2 ^ (prefixWord ++ tailWord_8358535).sum := by decide
  have hdescent : baseEnd_8358535 < baseStart_8358535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358552 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 1, 5]
def baseStart_8358552 : Nat := 118140960795 + 8358552 * 2 ^ 59
def prefixEnd_8358552 : Nat := 4983230072969 + 3 ^ 40 * 8358552 * 2
def baseEnd_8358552 : Nat := 1430651583866562120186575

theorem tailTrace_8358552 : CollatzResearch.WordTrace tailWord_8358552 prefixEnd_8358552 1430651583866562120186575 := by
  unfold tailWord_8358552
  simp only [CollatzResearch.WordTrace]
  refine ⟨152430718407200552937738955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203240957876267403916985273 152430718407200552937738955)
  ·
    refine ⟨228646077610800829406608433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152430718407200552937738955 228646077610800829406608433)
    ·
      refine ⟨171484558208100622054956325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228646077610800829406608433 171484558208100622054956325)
      ·
        refine ⟨32153354664018866635304311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171484558208100622054956325 32153354664018866635304311)
        ·
          refine ⟨48230031996028299952956467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32153354664018866635304311 48230031996028299952956467)
          ·
            refine ⟨72345047994042449929434701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48230031996028299952956467 72345047994042449929434701)
            ·
              refine ⟨27129392997765918723538013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72345047994042449929434701 27129392997765918723538013)
              ·
                refine ⟨10173522374162219521326755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27129392997765918723538013 10173522374162219521326755)
                ·
                  refine ⟨15260283561243329281990133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10173522374162219521326755 15260283561243329281990133)
                  ·
                    refine ⟨1430651583866562120186575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15260283561243329281990133 1430651583866562120186575)
                    ·
                      rfl

theorem cell23_8358552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_8358552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358552 prefixEnd_8358552 := by exact prefixLift 8358552
  have htrace : WordTrace (prefixWord ++ tailWord_8358552) baseStart_8358552 baseEnd_8358552 := by
    simpa [prefixWord, tailWord_8358552, baseEnd_8358552] using wordTrace_append hprefix tailTrace_8358552
  have hstable : (prefixWord ++ tailWord_8358552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358552).length < 2 ^ (prefixWord ++ tailWord_8358552).sum := by decide
  have hdescent : baseEnd_8358552 < baseStart_8358552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358575 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_8358575 : Nat := 118140960795 + 8358575 * 2 ^ 59
def prefixEnd_8358575 : Nat := 4983230072969 + 3 ^ 40 * 8358575 * 2
def baseEnd_8358575 : Nat := 4291966561654739770572119

theorem tailTrace_8358575 : CollatzResearch.WordTrace tailWord_8358575 prefixEnd_8358575 4291966561654739770572119 := by
  unfold tailWord_8358575
  simp only [CollatzResearch.WordTrace]
  refine ⟨304862275693317780803565179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203241517128878520535710119 304862275693317780803565179)
  ·
    refine ⟨457293413539976671205347769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304862275693317780803565179 457293413539976671205347769)
    ·
      refine ⟨342970060154982503404010827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457293413539976671205347769 342970060154982503404010827)
      ·
        refine ⟨514455090232473755106016241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342970060154982503404010827 514455090232473755106016241)
        ·
          refine ⟨385841317674355316329512181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514455090232473755106016241 385841317674355316329512181)
          ·
            refine ⟨36172623531970810905891767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 385841317674355316329512181 36172623531970810905891767)
            ·
              refine ⟨54258935297956216358837651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36172623531970810905891767 54258935297956216358837651)
              ·
                refine ⟨81388402946934324538256477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54258935297956216358837651 81388402946934324538256477)
                ·
                  refine ⟨30520651105100371701846179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81388402946934324538256477 30520651105100371701846179)
                  ·
                    refine ⟨45780976657650557552769269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30520651105100371701846179 45780976657650557552769269)
                    ·
                      refine ⟨4291966561654739770572119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45780976657650557552769269 4291966561654739770572119)
                      ·
                        rfl

theorem cell23_8358575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_8358575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358575 prefixEnd_8358575 := by exact prefixLift 8358575
  have htrace : WordTrace (prefixWord ++ tailWord_8358575) baseStart_8358575 baseEnd_8358575 := by
    simpa [prefixWord, tailWord_8358575, baseEnd_8358575] using wordTrace_append hprefix tailTrace_8358575
  have hstable : (prefixWord ++ tailWord_8358575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358575).length < 2 ^ (prefixWord ++ tailWord_8358575).sum := by decide
  have hdescent : baseEnd_8358575 < baseStart_8358575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358589 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_8358589 : Nat := 118140960795 + 8358589 * 2 ^ 59
def prefixEnd_8358589 : Nat := 4983230072969 + 3 ^ 40 * 8358589 * 2
def baseEnd_8358589 : Nat := 4291973750383902715797055

theorem tailTrace_8358589 : CollatzResearch.WordTrace tailWord_8358589 prefixEnd_8358589 4291973750383902715797055 := by
  unfold tailWord_8358589
  simp only [CollatzResearch.WordTrace]
  refine ⟨304862786315267061194574821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203241857543511374129716547 304862786315267061194574821)
  ·
    refine ⟨57161772434112573973982779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304862786315267061194574821 57161772434112573973982779)
    ·
      refine ⟨85742658651168860960974169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57161772434112573973982779 85742658651168860960974169)
      ·
        refine ⟨64306993988376645720730627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85742658651168860960974169 64306993988376645720730627)
        ·
          refine ⟨96460490982564968581095941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64306993988376645720730627 96460490982564968581095941)
          ·
            refine ⟨18086342059230931608955489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96460490982564968581095941 18086342059230931608955489)
            ·
              refine ⟨13564756544423198706716617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18086342059230931608955489 13564756544423198706716617)
              ·
                refine ⟨10173567408317399030037463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13564756544423198706716617 10173567408317399030037463)
                ·
                  refine ⟨15260351112476098545056195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10173567408317399030037463 15260351112476098545056195)
                  ·
                    refine ⟨22890526668714147817584293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15260351112476098545056195 22890526668714147817584293)
                    ·
                      refine ⟨4291973750383902715797055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22890526668714147817584293 4291973750383902715797055)
                      ·
                        rfl

theorem cell23_8358589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_8358589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358589 prefixEnd_8358589 := by exact prefixLift 8358589
  have htrace : WordTrace (prefixWord ++ tailWord_8358589) baseStart_8358589 baseEnd_8358589 := by
    simpa [prefixWord, tailWord_8358589, baseEnd_8358589] using wordTrace_append hprefix tailTrace_8358589
  have hstable : (prefixWord ++ tailWord_8358589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358589).length < 2 ^ (prefixWord ++ tailWord_8358589).sum := by decide
  have hdescent : baseEnd_8358589 < baseStart_8358589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358655 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 4, 6]
def baseStart_8358655 : Nat := 118140960795 + 8358655 * 2 ^ 59
def prefixEnd_8358655 : Nat := 4983230072969 + 3 ^ 40 * 8358655 * 2
def baseEnd_8358655 : Nat := 1430669213369033152523917

theorem tailTrace_8358655 : CollatzResearch.WordTrace tailWord_8358655 prefixEnd_8358655 1430669213369033152523917 := by
  unfold tailWord_8358655
  simp only [CollatzResearch.WordTrace]
  refine ⟨304865193533027954466477419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203243462355351969644318279 304865193533027954466477419)
  ·
    refine ⟨457297790299541931699716129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304865193533027954466477419 457297790299541931699716129)
    ·
      refine ⟨342973342724656448774787097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457297790299541931699716129 342973342724656448774787097)
      ·
        refine ⟨257230007043492336581090323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342973342724656448774787097 257230007043492336581090323)
        ·
          refine ⟨385845010565238504871635485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257230007043492336581090323 385845010565238504871635485)
          ·
            refine ⟨144691878961964439326863307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385845010565238504871635485 144691878961964439326863307)
            ·
              refine ⟨217037818442946658990294961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144691878961964439326863307 217037818442946658990294961)
              ·
                refine ⟨162778363832209994242721221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217037818442946658990294961 162778363832209994242721221)
                ·
                  refine ⟨30520943218539373920510229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162778363832209994242721221 30520943218539373920510229)
                  ·
                    refine ⟨1430669213369033152523917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30520943218539373920510229 1430669213369033152523917)
                    ·
                      rfl

theorem cell23_8358655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_8358655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358655 prefixEnd_8358655 := by exact prefixLift 8358655
  have htrace : WordTrace (prefixWord ++ tailWord_8358655) baseStart_8358655 baseEnd_8358655 := by
    simpa [prefixWord, tailWord_8358655, baseEnd_8358655] using wordTrace_append hprefix tailTrace_8358655
  have hstable : (prefixWord ++ tailWord_8358655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358655).length < 2 ^ (prefixWord ++ tailWord_8358655).sum := by decide
  have hdescent : baseEnd_8358655 < baseStart_8358655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358674 : List Nat := [3, 2, 4, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_8358674 : Nat := 118140960795 + 8358674 * 2 ^ 59
def prefixEnd_8358674 : Nat := 4983230072969 + 3 ^ 40 * 8358674 * 2
def baseEnd_8358674 : Nat := 4292017396239534883234165

theorem tailTrace_8358674 : CollatzResearch.WordTrace tailWord_8358674 prefixEnd_8358674 4292017396239534883234165 := by
  unfold tailWord_8358674
  simp only [CollatzResearch.WordTrace]
  refine ⟨76216471629989780177854769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203243924346639413807612717 76216471629989780177854769)
  ·
    refine ⟨57162353722492335133391077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76216471629989780177854769 57162353722492335133391077)
    ·
      refine ⟨10717941322967312837510827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57162353722492335133391077 10717941322967312837510827)
      ·
        refine ⟨16076911984450969256266241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10717941322967312837510827 16076911984450969256266241)
        ·
          refine ⟨12057683988338226942199681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16076911984450969256266241 12057683988338226942199681)
          ·
            refine ⟨9043262991253670206649761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12057683988338226942199681 9043262991253670206649761)
            ·
              refine ⟨6782447243440252654987321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9043262991253670206649761 6782447243440252654987321)
              ·
                refine ⟨5086835432580189491240491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6782447243440252654987321 5086835432580189491240491)
                ·
                  refine ⟨7630253148870284236860737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086835432580189491240491 7630253148870284236860737)
                  ·
                    refine ⟨5722689861652713177645553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7630253148870284236860737 5722689861652713177645553)
                    ·
                      refine ⟨4292017396239534883234165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722689861652713177645553 4292017396239534883234165)
                      ·
                        rfl

theorem cell23_8358674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_8358674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358674 prefixEnd_8358674 := by exact prefixLift 8358674
  have htrace : WordTrace (prefixWord ++ tailWord_8358674) baseStart_8358674 baseEnd_8358674 := by
    simpa [prefixWord, tailWord_8358674, baseEnd_8358674] using wordTrace_append hprefix tailTrace_8358674
  have hstable : (prefixWord ++ tailWord_8358674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358674).length < 2 ^ (prefixWord ++ tailWord_8358674).sum := by decide
  have hdescent : baseEnd_8358674 < baseStart_8358674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358682 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_8358682 : Nat := 118140960795 + 8358682 * 2 ^ 59
def prefixEnd_8358682 : Nat := 4983230072969 + 3 ^ 40 * 8358682 * 2
def baseEnd_8358682 : Nat := 4292021504084770851934127

theorem tailTrace_8358682 : CollatzResearch.WordTrace tailWord_8358682 prefixEnd_8358682 4292021504084770851934127 := by
  unfold tailWord_8358682
  simp only [CollatzResearch.WordTrace]
  refine ⟨76216544575982534519427575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203244118869286758718473533 76216544575982534519427575)
  ·
    refine ⟨114324816863973801779141363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76216544575982534519427575 114324816863973801779141363)
    ·
      refine ⟨171487225295960702668712045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114324816863973801779141363 171487225295960702668712045)
      ·
        refine ⟨64307709485985263500767017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171487225295960702668712045 64307709485985263500767017)
        ·
          refine ⟨48230782114488947625575263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64307709485985263500767017 48230782114488947625575263)
          ·
            refine ⟨72346173171733421438362895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48230782114488947625575263 72346173171733421438362895)
            ·
              refine ⟨108519259757600132157544343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72346173171733421438362895 108519259757600132157544343)
              ·
                refine ⟨162778889636400198236316515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108519259757600132157544343 162778889636400198236316515)
                ·
                  refine ⟨244168334454600297354474773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162778889636400198236316515 244168334454600297354474773)
                  ·
                    refine ⟨11445390677559388938491005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 244168334454600297354474773 11445390677559388938491005)
                    ·
                      refine ⟨4292021504084770851934127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11445390677559388938491005 4292021504084770851934127)
                      ·
                        rfl

theorem cell23_8358682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_8358682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358682 prefixEnd_8358682 := by exact prefixLift 8358682
  have htrace : WordTrace (prefixWord ++ tailWord_8358682) baseStart_8358682 baseEnd_8358682 := by
    simpa [prefixWord, tailWord_8358682, baseEnd_8358682] using wordTrace_append hprefix tailTrace_8358682
  have hstable : (prefixWord ++ tailWord_8358682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358682).length < 2 ^ (prefixWord ++ tailWord_8358682).sum := by decide
  have hdescent : baseEnd_8358682 < baseStart_8358682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358696 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_8358696 : Nat := 118140960795 + 8358696 * 2 ^ 59
def prefixEnd_8358696 : Nat := 4983230072969 + 3 ^ 40 * 8358696 * 2
def baseEnd_8358696 : Nat := 4292028692813933797159063

theorem tailTrace_8358696 : CollatzResearch.WordTrace tailWord_8358696 prefixEnd_8358696 4292028692813933797159063 := by
  unfold tailWord_8358696
  simp only [CollatzResearch.WordTrace]
  refine ⟨152433344462939709234359971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203244459283919612312479961 152433344462939709234359971)
  ·
    refine ⟨228650016694409563851539957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152433344462939709234359971 228650016694409563851539957)
    ·
      refine ⟨21435939065100896611081871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228650016694409563851539957 21435939065100896611081871)
      ·
        refine ⟨32153908597651344916622807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21435939065100896611081871 32153908597651344916622807)
        ·
          refine ⟨48230862896477017374934211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32153908597651344916622807 48230862896477017374934211)
          ·
            refine ⟨72346294344715526062401317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48230862896477017374934211 72346294344715526062401317)
            ·
              refine ⟨13564930189634161136700247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72346294344715526062401317 13564930189634161136700247)
              ·
                refine ⟨20347395284451241705050371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13564930189634161136700247 20347395284451241705050371)
                ·
                  refine ⟨30521092926676862557575557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20347395284451241705050371 30521092926676862557575557)
                  ·
                    refine ⟨5722704923751911729545417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30521092926676862557575557 5722704923751911729545417)
                    ·
                      refine ⟨4292028692813933797159063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722704923751911729545417 4292028692813933797159063)
                      ·
                        rfl

theorem cell23_8358696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_8358696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358696 prefixEnd_8358696 := by exact prefixLift 8358696
  have htrace : WordTrace (prefixWord ++ tailWord_8358696) baseStart_8358696 baseEnd_8358696 := by
    simpa [prefixWord, tailWord_8358696, baseEnd_8358696] using wordTrace_append hprefix tailTrace_8358696
  have hstable : (prefixWord ++ tailWord_8358696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358696).length < 2 ^ (prefixWord ++ tailWord_8358696).sum := by decide
  have hdescent : baseEnd_8358696 < baseStart_8358696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358712 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_8358712 : Nat := 118140960795 + 8358712 * 2 ^ 59
def prefixEnd_8358712 : Nat := 4983230072969 + 3 ^ 40 * 8358712 * 2
def baseEnd_8358712 : Nat := 4292036908504405734558989

theorem tailTrace_8358712 : CollatzResearch.WordTrace tailWord_8358712 prefixEnd_8358712 4292036908504405734558989 := by
  unfold tailWord_8358712
  simp only [CollatzResearch.WordTrace]
  refine ⟨152433636246910726600651195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203244848329214302134201593 152433636246910726600651195)
  ·
    refine ⟨228650454370366089900976793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152433636246910726600651195 228650454370366089900976793)
    ·
      refine ⟨171487840777774567425732595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228650454370366089900976793 171487840777774567425732595)
      ·
        refine ⟨257231761166661851138598893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171487840777774567425732595 257231761166661851138598893)
        ·
          refine ⟨96461910437498194176974585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257231761166661851138598893 96461910437498194176974585)
          ·
            refine ⟨72346432828123645632730939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96461910437498194176974585 72346432828123645632730939)
            ·
              refine ⟨108519649242185468449096409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72346432828123645632730939 108519649242185468449096409)
              ·
                refine ⟨81389736931639101336822307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108519649242185468449096409 81389736931639101336822307)
                ·
                  refine ⟨122084605397458652005233461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81389736931639101336822307 122084605397458652005233461)
                  ·
                    refine ⟨11445431756011748625490637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122084605397458652005233461 11445431756011748625490637)
                    ·
                      refine ⟨4292036908504405734558989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11445431756011748625490637 4292036908504405734558989)
                      ·
                        rfl

theorem cell23_8358712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_8358712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358712 prefixEnd_8358712 := by exact prefixLift 8358712
  have htrace : WordTrace (prefixWord ++ tailWord_8358712) baseStart_8358712 baseEnd_8358712 := by
    simpa [prefixWord, tailWord_8358712, baseEnd_8358712] using wordTrace_append hprefix tailTrace_8358712
  have hstable : (prefixWord ++ tailWord_8358712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358712).length < 2 ^ (prefixWord ++ tailWord_8358712).sum := by decide
  have hdescent : baseEnd_8358712 < baseStart_8358712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358717 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_8358717 : Nat := 118140960795 + 8358717 * 2 ^ 59
def prefixEnd_8358717 : Nat := 4983230072969 + 3 ^ 40 * 8358717 * 2
def baseEnd_8358717 : Nat := 4292039475907678214996467

theorem tailTrace_8358717 : CollatzResearch.WordTrace tailWord_8358717 prefixEnd_8358717 4292039475907678214996467 := by
  unfold tailWord_8358717
  simp only [CollatzResearch.WordTrace]
  refine ⟨304867454858803339055234405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203244969905868892703489603 304867454858803339055234405)
  ·
    refine ⟨57162647786025626072856451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304867454858803339055234405 57162647786025626072856451)
    ·
      refine ⟨85743971679038439109284677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57162647786025626072856451 85743971679038439109284677)
      ·
        refine ⟨16076994689819707332990877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85743971679038439109284677 16076994689819707332990877)
        ·
          refine ⟨6028873008682390249871579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16076994689819707332990877 6028873008682390249871579)
          ·
            refine ⟨9043309513023585374807369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028873008682390249871579 9043309513023585374807369)
            ·
              refine ⟨6782482134767689031105527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9043309513023585374807369 6782482134767689031105527)
              ·
                refine ⟨10173723202151533546658291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6782482134767689031105527 10173723202151533546658291)
                ·
                  refine ⟨15260584803227300319987437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10173723202151533546658291 15260584803227300319987437)
                  ·
                    refine ⟨5722719301210237619995289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15260584803227300319987437 5722719301210237619995289)
                    ·
                      refine ⟨4292039475907678214996467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722719301210237619995289 4292039475907678214996467)
                      ·
                        rfl

theorem cell23_8358717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_8358717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358717 prefixEnd_8358717 := by exact prefixLift 8358717
  have htrace : WordTrace (prefixWord ++ tailWord_8358717) baseStart_8358717 baseEnd_8358717 := by
    simpa [prefixWord, tailWord_8358717, baseEnd_8358717] using wordTrace_append hprefix tailTrace_8358717
  have hstable : (prefixWord ++ tailWord_8358717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358717).length < 2 ^ (prefixWord ++ tailWord_8358717).sum := by decide
  have hdescent : baseEnd_8358717 < baseStart_8358717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358719 : List Nat := [1, 1, 2, 2, 5, 1, 1, 5, 5]
def baseStart_8358719 : Nat := 118140960795 + 8358719 * 2 ^ 59
def prefixEnd_8358719 : Nat := 4983230072969 + 3 ^ 40 * 8358719 * 2
def baseEnd_8358719 : Nat := 476893389207665245241273

theorem tailTrace_8358719 : CollatzResearch.WordTrace tailWord_8358719 prefixEnd_8358719 476893389207665245241273 := by
  unfold tailWord_8358719
  simp only [CollatzResearch.WordTrace]
  refine ⟨304867527804796093396807211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203245018536530728931204807 304867527804796093396807211)
  ·
    refine ⟨457301291707194140095210817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304867527804796093396807211 457301291707194140095210817)
    ·
      refine ⟨342975968780395605071408113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457301291707194140095210817 342975968780395605071408113)
      ·
        refine ⟨257231976585296703803556085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342975968780395605071408113 257231976585296703803556085)
        ·
          refine ⟨24115497804871565981583383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257231976585296703803556085 24115497804871565981583383)
          ·
            refine ⟨36173246707307348972375075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24115497804871565981583383 36173246707307348972375075)
            ·
              refine ⟨54259870060961023458562613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36173246707307348972375075 54259870060961023458562613)
              ·
                refine ⟨5086862818215095949240245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54259870060961023458562613 5086862818215095949240245)
                ·
                  refine ⟨476893389207665245241273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5086862818215095949240245 476893389207665245241273)
                  ·
                    rfl

theorem cell23_8358719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 5].length) (baseStart_8358719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358719 prefixEnd_8358719 := by exact prefixLift 8358719
  have htrace : WordTrace (prefixWord ++ tailWord_8358719) baseStart_8358719 baseEnd_8358719 := by
    simpa [prefixWord, tailWord_8358719, baseEnd_8358719] using wordTrace_append hprefix tailTrace_8358719
  have hstable : (prefixWord ++ tailWord_8358719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358719).length < 2 ^ (prefixWord ++ tailWord_8358719).sum := by decide
  have hdescent : baseEnd_8358719 < baseStart_8358719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358752 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_8358752 : Nat := 118140960795 + 8358752 * 2 ^ 59
def prefixEnd_8358752 : Nat := 4983230072969 + 3 ^ 40 * 8358752 * 2
def baseEnd_8358752 : Nat := 4292057447730585578058805

theorem tailTrace_8358752 : CollatzResearch.WordTrace tailWord_8358752 prefixEnd_8358752 4292057447730585578058805 := by
  unfold tailWord_8358752
  simp only [CollatzResearch.WordTrace]
  refine ⟨152434365706838270016379255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203245820942451026688505673 152434365706838270016379255)
  ·
    refine ⟨228651548560257405024568883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152434365706838270016379255 228651548560257405024568883)
    ·
      refine ⟨342977322840386107536853325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228651548560257405024568883 342977322840386107536853325)
      ·
        refine ⟨128616496065144790326319997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342977322840386107536853325 128616496065144790326319997)
        ·
          refine ⟨48231186024429296372369999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128616496065144790326319997 48231186024429296372369999)
          ·
            refine ⟨72346779036643944558554999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48231186024429296372369999 72346779036643944558554999)
            ·
              refine ⟨108520168554965916837832499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72346779036643944558554999 108520168554965916837832499)
              ·
                refine ⟨162780252832448875256748749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108520168554965916837832499 162780252832448875256748749)
                ·
                  refine ⟨61042594812168328221280781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162780252832448875256748749 61042594812168328221280781)
                  ·
                    refine ⟨22890973054563123082980293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61042594812168328221280781 22890973054563123082980293)
                    ·
                      refine ⟨4292057447730585578058805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22890973054563123082980293 4292057447730585578058805)
                      ·
                        rfl

theorem cell23_8358752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_8358752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358752 prefixEnd_8358752 := by exact prefixLift 8358752
  have htrace : WordTrace (prefixWord ++ tailWord_8358752) baseStart_8358752 baseEnd_8358752 := by
    simpa [prefixWord, tailWord_8358752, baseEnd_8358752] using wordTrace_append hprefix tailTrace_8358752
  have hstable : (prefixWord ++ tailWord_8358752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358752).length < 2 ^ (prefixWord ++ tailWord_8358752).sum := by decide
  have hdescent : baseEnd_8358752 < baseStart_8358752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358789 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_8358789 : Nat := 118140960795 + 8358789 * 2 ^ 59
def prefixEnd_8358789 : Nat := 4983230072969 + 3 ^ 40 * 8358789 * 2
def baseEnd_8358789 : Nat := 4292076446514801933296135

theorem tailTrace_8358789 : CollatzResearch.WordTrace tailWord_8358789 prefixEnd_8358789 4292076446514801933296135 := by
  unfold tailWord_8358789
  simp only [CollatzResearch.WordTrace]
  refine ⟨304870080914542495351855421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203246720609694996901236947 304870080914542495351855421)
  ·
    refine ⟨114326280342953435756945783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304870080914542495351855421 114326280342953435756945783)
    ·
      refine ⟨171489420514430153635418675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114326280342953435756945783 171489420514430153635418675)
      ·
        refine ⟨257234130771645230453128013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171489420514430153635418675 257234130771645230453128013)
        ·
          refine ⟨96462799039366961419923005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257234130771645230453128013 96462799039366961419923005)
          ·
            refine ⟨36173549639762610532471127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96462799039366961419923005 36173549639762610532471127)
            ·
              refine ⟨54260324459643915798706691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36173549639762610532471127 54260324459643915798706691)
              ·
                refine ⟨81390486689465873698060037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54260324459643915798706691 81390486689465873698060037)
                ·
                  refine ⟨15260716254274851318386257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81390486689465873698060037 15260716254274851318386257)
                  ·
                    refine ⟨11445537190706138488789693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15260716254274851318386257 11445537190706138488789693)
                    ·
                      refine ⟨4292076446514801933296135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11445537190706138488789693 4292076446514801933296135)
                      ·
                        rfl

theorem cell23_8358789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_8358789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358789 prefixEnd_8358789 := by exact prefixLift 8358789
  have htrace : WordTrace (prefixWord ++ tailWord_8358789) baseStart_8358789 baseEnd_8358789 := by
    simpa [prefixWord, tailWord_8358789, baseEnd_8358789] using wordTrace_append hprefix tailTrace_8358789
  have hstable : (prefixWord ++ tailWord_8358789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358789).length < 2 ^ (prefixWord ++ tailWord_8358789).sum := by decide
  have hdescent : baseEnd_8358789 < baseStart_8358789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358796 : List Nat := [2, 2, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_8358796 : Nat := 118140960795 + 8358796 * 2 ^ 59
def prefixEnd_8358796 : Nat := 4983230072969 + 3 ^ 40 * 8358796 * 2
def baseEnd_8358796 : Nat := 1430693346959794468636201

theorem tailTrace_8358796 : CollatzResearch.WordTrace tailWord_8358796 prefixEnd_8358796 1430693346959794468636201 := by
  unfold tailWord_8358796
  simp only [CollatzResearch.WordTrace]
  refine ⟨152435168112758567773680121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203246890817011423698240161 152435168112758567773680121)
  ·
    refine ⟨114326376084568925830260091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152435168112758567773680121 114326376084568925830260091)
    ·
      refine ⟨171489564126853388745390137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114326376084568925830260091 171489564126853388745390137)
      ·
        refine ⟨128617173095140041559042603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171489564126853388745390137 128617173095140041559042603)
        ·
          refine ⟨192925759642710062338563905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128617173095140041559042603 192925759642710062338563905)
          ·
            refine ⟨144694319732032546753922929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192925759642710062338563905 144694319732032546753922929)
            ·
              refine ⟨108520739799024410065442197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144694319732032546753922929 108520739799024410065442197)
              ·
                refine ⟨5086909678079269221817603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108520739799024410065442197 5086909678079269221817603)
                ·
                  refine ⟨7630364517118903832726405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086909678079269221817603 7630364517118903832726405)
                  ·
                    refine ⟨1430693346959794468636201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7630364517118903832726405 1430693346959794468636201)
                    ·
                      rfl

theorem cell23_8358796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_8358796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358796 prefixEnd_8358796 := by exact prefixLift 8358796
  have htrace : WordTrace (prefixWord ++ tailWord_8358796) baseStart_8358796 baseEnd_8358796 := by
    simpa [prefixWord, tailWord_8358796, baseEnd_8358796] using wordTrace_append hprefix tailTrace_8358796
  have hstable : (prefixWord ++ tailWord_8358796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358796).length < 2 ^ (prefixWord ++ tailWord_8358796).sum := by decide
  have hdescent : baseEnd_8358796 < baseStart_8358796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358823 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_8358823 : Nat := 118140960795 + 8358823 * 2 ^ 59
def prefixEnd_8358823 : Nat := 4983230072969 + 3 ^ 40 * 8358823 * 2
def baseEnd_8358823 : Nat := 4292093904857054800270979

theorem tailTrace_8358823 : CollatzResearch.WordTrace tailWord_8358823 prefixEnd_8358823 4292093904857054800270979 := by
  unfold tailWord_8358823
  simp only [CollatzResearch.WordTrace]
  refine ⟨304871320996419319158593123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203247547330946212772395415 304871320996419319158593123)
  ·
    refine ⟨457306981494628978737889685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304871320996419319158593123 457306981494628978737889685)
    ·
      refine ⟨21436264757560733378338579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 457306981494628978737889685 21436264757560733378338579)
      ·
        refine ⟨32154397136341100067507869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21436264757560733378338579 32154397136341100067507869)
        ·
          refine ⟨12057898926127912525315451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32154397136341100067507869 12057898926127912525315451)
          ·
            refine ⟨18086848389191868787973177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057898926127912525315451 18086848389191868787973177)
            ·
              refine ⟨13565136291893901590979883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18086848389191868787973177 13565136291893901590979883)
              ·
                refine ⟨20347704437840852386469825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13565136291893901590979883 20347704437840852386469825)
                ·
                  refine ⟨15260778328380639289852369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20347704437840852386469825 15260778328380639289852369)
                  ·
                    refine ⟨11445583746285479467389277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15260778328380639289852369 11445583746285479467389277)
                    ·
                      refine ⟨4292093904857054800270979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11445583746285479467389277 4292093904857054800270979)
                      ·
                        rfl

theorem cell23_8358823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_8358823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358823 prefixEnd_8358823 := by exact prefixLift 8358823
  have htrace : WordTrace (prefixWord ++ tailWord_8358823) baseStart_8358823 baseEnd_8358823 := by
    simpa [prefixWord, tailWord_8358823, baseEnd_8358823] using wordTrace_append hprefix tailTrace_8358823
  have hstable : (prefixWord ++ tailWord_8358823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358823).length < 2 ^ (prefixWord ++ tailWord_8358823).sum := by decide
  have hdescent : baseEnd_8358823 < baseStart_8358823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358839 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 1, 5]
def baseStart_8358839 : Nat := 118140960795 + 8358839 * 2 ^ 59
def prefixEnd_8358839 : Nat := 4983230072969 + 3 ^ 40 * 8358839 * 2
def baseEnd_8358839 : Nat := 1430700706849175579223635

theorem tailTrace_8358839 : CollatzResearch.WordTrace tailWord_8358839 prefixEnd_8358839 1430700706849175579223635 := by
  unfold tailWord_8358839
  simp only [CollatzResearch.WordTrace]
  refine ⟨304871904564361353891175571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203247936376240902594117047 304871904564361353891175571)
  ·
    refine ⟨457307856846542030836763357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304871904564361353891175571 457307856846542030836763357)
    ·
      refine ⟨171490446317453261563786259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457307856846542030836763357 171490446317453261563786259)
      ·
        refine ⟨257235669476179892345679389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171490446317453261563786259 257235669476179892345679389)
        ·
          refine ⟨96463376053567459629629771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257235669476179892345679389 96463376053567459629629771)
          ·
            refine ⟨144695064080351189444444657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96463376053567459629629771 144695064080351189444444657)
            ·
              refine ⟨108521298060263392083333493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144695064080351189444444657 108521298060263392083333493)
              ·
                refine ⟨10173871693149693007812515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108521298060263392083333493 10173871693149693007812515)
                ·
                  refine ⟨15260807539724539511718773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10173871693149693007812515 15260807539724539511718773)
                  ·
                    refine ⟨1430700706849175579223635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15260807539724539511718773 1430700706849175579223635)
                    ·
                      rfl

theorem cell23_8358839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_8358839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358839 prefixEnd_8358839 := by exact prefixLift 8358839
  have htrace : WordTrace (prefixWord ++ tailWord_8358839) baseStart_8358839 baseEnd_8358839 := by
    simpa [prefixWord, tailWord_8358839, baseEnd_8358839] using wordTrace_append hprefix tailTrace_8358839
  have hstable : (prefixWord ++ tailWord_8358839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358839).length < 2 ^ (prefixWord ++ tailWord_8358839).sum := by decide
  have hdescent : baseEnd_8358839 < baseStart_8358839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358854 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_8358854 : Nat := 118140960795 + 8358854 * 2 ^ 59
def prefixEnd_8358854 : Nat := 4983230072969 + 3 ^ 40 * 8358854 * 2
def baseEnd_8358854 : Nat := 4292109822757344178983337

theorem tailTrace_8358854 : CollatzResearch.WordTrace tailWord_8358854 prefixEnd_8358854 4292109822757344178983337 := by
  unfold tailWord_8358854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527264114353344107905363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203248301106204674301981077 9527264114353344107905363)
  ·
    refine ⟨14290896171530016161858045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9527264114353344107905363 14290896171530016161858045)
    ·
      refine ⟨5359086064323756060696767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14290896171530016161858045 5359086064323756060696767)
      ·
        refine ⟨8038629096485634091045151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5359086064323756060696767 8038629096485634091045151)
        ·
          refine ⟨12057943644728451136567727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8038629096485634091045151 12057943644728451136567727)
          ·
            refine ⟨18086915467092676704851591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057943644728451136567727 18086915467092676704851591)
            ·
              refine ⟨27130373200639015057277387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18086915467092676704851591 27130373200639015057277387)
              ·
                refine ⟨40695559800958522585916081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27130373200639015057277387 40695559800958522585916081)
                ·
                  refine ⟨30521669850718891939437061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40695559800958522585916081 30521669850718891939437061)
                  ·
                    refine ⟨5722813097009792238644449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30521669850718891939437061 5722813097009792238644449)
                    ·
                      refine ⟨4292109822757344178983337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722813097009792238644449 4292109822757344178983337)
                      ·
                        rfl

theorem cell23_8358854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_8358854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358854 prefixEnd_8358854 := by exact prefixLift 8358854
  have htrace : WordTrace (prefixWord ++ tailWord_8358854) baseStart_8358854 baseEnd_8358854 := by
    simpa [prefixWord, tailWord_8358854, baseEnd_8358854] using wordTrace_append hprefix tailTrace_8358854
  have hstable : (prefixWord ++ tailWord_8358854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358854).length < 2 ^ (prefixWord ++ tailWord_8358854).sum := by decide
  have hdescent : baseEnd_8358854 < baseStart_8358854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358859 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 4]
def baseStart_8358859 : Nat := 118140960795 + 8358859 * 2 ^ 59
def prefixEnd_8358859 : Nat := 4983230072969 + 3 ^ 40 * 8358859 * 2
def baseEnd_8358859 : Nat := 4292112390160616659420813

theorem tailTrace_8358859 : CollatzResearch.WordTrace tailWord_8358859 prefixEnd_8358859 4292112390160616659420813 := by
  unfold tailWord_8358859
  simp only [CollatzResearch.WordTrace]
  refine ⟨304872634024288897306903631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203248422682859264871269087 304872634024288897306903631)
  ·
    refine ⟨457308951036433345960355447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304872634024288897306903631 457308951036433345960355447)
    ·
      refine ⟨685963426554650018940533171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457308951036433345960355447 685963426554650018940533171)
      ·
        refine ⟨1028945139831975028410799757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685963426554650018940533171 1028945139831975028410799757)
        ·
          refine ⟨385854427436990635654049909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1028945139831975028410799757 385854427436990635654049909)
          ·
            refine ⟨36173852572217872092567179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 385854427436990635654049909 36173852572217872092567179)
            ·
              refine ⟨54260778858326808138850769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36173852572217872092567179 54260778858326808138850769)
              ·
                refine ⟨40695584143745106104138077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54260778858326808138850769 40695584143745106104138077)
                ·
                  refine ⟨15260844053904414789051779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40695584143745106104138077 15260844053904414789051779)
                  ·
                    refine ⟨22891266080856622183577669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15260844053904414789051779 22891266080856622183577669)
                    ·
                      refine ⟨4292112390160616659420813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22891266080856622183577669 4292112390160616659420813)
                      ·
                        rfl

theorem cell23_8358859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 4].length) (baseStart_8358859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358859 prefixEnd_8358859 := by exact prefixLift 8358859
  have htrace : WordTrace (prefixWord ++ tailWord_8358859) baseStart_8358859 baseEnd_8358859 := by
    simpa [prefixWord, tailWord_8358859, baseEnd_8358859] using wordTrace_append hprefix tailTrace_8358859
  have hstable : (prefixWord ++ tailWord_8358859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358859).length < 2 ^ (prefixWord ++ tailWord_8358859).sum := by decide
  have hdescent : baseEnd_8358859 < baseStart_8358859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358870 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_8358870 : Nat := 118140960795 + 8358870 * 2 ^ 59
def prefixEnd_8358870 : Nat := 4983230072969 + 3 ^ 40 * 8358870 * 2
def baseEnd_8358870 : Nat := 4292118038447816116383263

theorem tailTrace_8358870 : CollatzResearch.WordTrace tailWord_8358870 prefixEnd_8358870 4292118038447816116383263 := by
  unfold tailWord_8358870
  simp only [CollatzResearch.WordTrace]
  refine ⟨19054564701703065386597129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203248690151499364123702709 19054564701703065386597129)
  ·
    refine ⟨14290923526277299039947847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19054564701703065386597129 14290923526277299039947847)
    ·
      refine ⟨21436385289415948559921771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14290923526277299039947847 21436385289415948559921771)
      ·
        refine ⟨32154577934123922839882657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21436385289415948559921771 32154577934123922839882657)
        ·
          refine ⟨24115933450592942129911993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32154577934123922839882657 24115933450592942129911993)
          ·
            refine ⟨18086950087944706597433995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24115933450592942129911993 18086950087944706597433995)
            ·
              refine ⟨27130425131917059896150993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18086950087944706597433995 27130425131917059896150993)
              ·
                refine ⟨20347818848937794922113245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27130425131917059896150993 20347818848937794922113245)
                ·
                  refine ⟨7630432068351673095792467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20347818848937794922113245 7630432068351673095792467)
                  ·
                    refine ⟨11445648102527509643688701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7630432068351673095792467 11445648102527509643688701)
                    ·
                      refine ⟨4292118038447816116383263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11445648102527509643688701 4292118038447816116383263)
                      ·
                        rfl

theorem cell23_8358870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_8358870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358870 prefixEnd_8358870 := by exact prefixLift 8358870
  have htrace : WordTrace (prefixWord ++ tailWord_8358870) baseStart_8358870 baseEnd_8358870 := by
    simpa [prefixWord, tailWord_8358870, baseEnd_8358870] using wordTrace_append hprefix tailTrace_8358870
  have hstable : (prefixWord ++ tailWord_8358870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358870).length < 2 ^ (prefixWord ++ tailWord_8358870).sum := by decide
  have hdescent : baseEnd_8358870 < baseStart_8358870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358979 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 4]
def baseStart_8358979 : Nat := 118140960795 + 8358979 * 2 ^ 59
def prefixEnd_8358979 : Nat := 4983230072969 + 3 ^ 40 * 8358979 * 2
def baseEnd_8358979 : Nat := 4292174007839156189920261

theorem tailTrace_8358979 : CollatzResearch.WordTrace tailWord_8358979 prefixEnd_8358979 4292174007839156189920261 := by
  unfold tailWord_8358979
  simp only [CollatzResearch.WordTrace]
  refine ⟨304877010783854157801271991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203251340522569438534181327 304877010783854157801271991)
  ·
    refine ⟨457315516175781236701907987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304877010783854157801271991 457315516175781236701907987)
    ·
      refine ⟨685973274263671855052861981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457315516175781236701907987 685973274263671855052861981)
      ·
        refine ⟨257239977848876945644823243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 685973274263671855052861981 257239977848876945644823243)
        ·
          refine ⟨385859966773315418467234865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257239977848876945644823243 385859966773315418467234865)
          ·
            refine ⟨289394975079986563850426149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385859966773315418467234865 289394975079986563850426149)
            ·
              refine ⟨54261557827497480721954903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289394975079986563850426149 54261557827497480721954903)
              ·
                refine ⟨81392336741246221082932355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54261557827497480721954903 81392336741246221082932355)
                ·
                  refine ⟨122088505111869331624398533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81392336741246221082932355 122088505111869331624398533)
                  ·
                    refine ⟨22891594708475499679574725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122088505111869331624398533 22891594708475499679574725)
                    ·
                      refine ⟨4292174007839156189920261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22891594708475499679574725 4292174007839156189920261)
                      ·
                        rfl

theorem cell23_8358979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_8358979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358979 prefixEnd_8358979 := by exact prefixLift 8358979
  have htrace : WordTrace (prefixWord ++ tailWord_8358979) baseStart_8358979 baseEnd_8358979 := by
    simpa [prefixWord, tailWord_8358979, baseEnd_8358979] using wordTrace_append hprefix tailTrace_8358979
  have hstable : (prefixWord ++ tailWord_8358979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358979).length < 2 ^ (prefixWord ++ tailWord_8358979).sum := by decide
  have hdescent : baseEnd_8358979 < baseStart_8358979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359033 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 3]
def baseStart_8359033 : Nat := 118140960795 + 8359033 * 2 ^ 59
def prefixEnd_8359033 : Nat := 4983230072969 + 3 ^ 40 * 8359033 * 2
def baseEnd_8359033 : Nat := 4292201735794498978645013

theorem tailTrace_8359033 : CollatzResearch.WordTrace tailWord_8359033 prefixEnd_8359033 4292201735794498978645013 := by
  unfold tailWord_8359033
  simp only [CollatzResearch.WordTrace]
  refine ⟨304878980325658525023737753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203252653550439016682491835 304878980325658525023737753)
  ·
    refine ⟨228659235244243893767803315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304878980325658525023737753 228659235244243893767803315)
    ·
      refine ⟨342988852866365840651704973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228659235244243893767803315 342988852866365840651704973)
      ·
        refine ⟨128620819824887190244389365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342988852866365840651704973 128620819824887190244389365)
        ·
          refine ⟨12058201858583174085411503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128620819824887190244389365 12058201858583174085411503)
          ·
            refine ⟨18087302787874761128117255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12058201858583174085411503 18087302787874761128117255)
            ·
              refine ⟨27130954181812141692175883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18087302787874761128117255 27130954181812141692175883)
              ·
                refine ⟨40696431272718212538263825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27130954181812141692175883 40696431272718212538263825)
                ·
                  refine ⟨30522323454538659403697869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40696431272718212538263825 30522323454538659403697869)
                  ·
                    refine ⟨11445871295451997276386701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30522323454538659403697869 11445871295451997276386701)
                    ·
                      refine ⟨4292201735794498978645013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11445871295451997276386701 4292201735794498978645013)
                      ·
                        rfl

theorem cell23_8359033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_8359033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359033 prefixEnd_8359033 := by exact prefixLift 8359033
  have htrace : WordTrace (prefixWord ++ tailWord_8359033) baseStart_8359033 baseEnd_8359033 := by
    simpa [prefixWord, tailWord_8359033, baseEnd_8359033] using wordTrace_append hprefix tailTrace_8359033
  have hstable : (prefixWord ++ tailWord_8359033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359033).length < 2 ^ (prefixWord ++ tailWord_8359033).sum := by decide
  have hdescent : baseEnd_8359033 < baseStart_8359033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359056 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_8359056 : Nat := 118140960795 + 8359056 * 2 ^ 59
def prefixEnd_8359056 : Nat := 4983230072969 + 3 ^ 40 * 8359056 * 2
def baseEnd_8359056 : Nat := 4292213545849552388657407

theorem tailTrace_8359056 : CollatzResearch.WordTrace tailWord_8359056 prefixEnd_8359056 4292213545849552388657407 := by
  unfold tailWord_8359056
  simp only [CollatzResearch.WordTrace]
  refine ⟨152439909602287599975912511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203253212803050133301216681 152439909602287599975912511)
  ·
    refine ⟨228659864403431399963868767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152439909602287599975912511 228659864403431399963868767)
    ·
      refine ⟨342989796605147099945803151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228659864403431399963868767 342989796605147099945803151)
      ·
        refine ⟨514484694907720649918704727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342989796605147099945803151 514484694907720649918704727)
        ·
          refine ⟨771727042361580974878057091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514484694907720649918704727 771727042361580974878057091)
          ·
            refine ⟨1157590563542371462317085637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771727042361580974878057091 1157590563542371462317085637)
            ·
              refine ⟨217048230664194649184453557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1157590563542371462317085637 217048230664194649184453557)
              ·
                refine ⟨20348271624768248361042521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217048230664194649184453557 20348271624768248361042521)
                ·
                  refine ⟨15261203718576186270781891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20348271624768248361042521 15261203718576186270781891)
                  ·
                    refine ⟨22891805577864279406172837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15261203718576186270781891 22891805577864279406172837)
                    ·
                      refine ⟨4292213545849552388657407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22891805577864279406172837 4292213545849552388657407)
                      ·
                        rfl

theorem cell23_8359056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_8359056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359056 prefixEnd_8359056 := by exact prefixLift 8359056
  have htrace : WordTrace (prefixWord ++ tailWord_8359056) baseStart_8359056 baseEnd_8359056 := by
    simpa [prefixWord, tailWord_8359056, baseEnd_8359056] using wordTrace_append hprefix tailTrace_8359056
  have hstable : (prefixWord ++ tailWord_8359056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359056).length < 2 ^ (prefixWord ++ tailWord_8359056).sum := by decide
  have hdescent : baseEnd_8359056 < baseStart_8359056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359073 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_8359073 : Nat := 118140960795 + 8359073 * 2 ^ 59
def prefixEnd_8359073 : Nat := 4983230072969 + 3 ^ 40 * 8359073 * 2
def baseEnd_8359073 : Nat := 4292222275020678822144829

theorem tailTrace_8359073 : CollatzResearch.WordTrace tailWord_8359073 prefixEnd_8359073 4292222275020678822144829 := by
  unfold tailWord_8359073
  simp only [CollatzResearch.WordTrace]
  refine ⟨304880439245513611855193873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203253626163675741236795915 304880439245513611855193873)
  ·
    refine ⟨228660329434135208891395405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304880439245513611855193873 228660329434135208891395405)
    ·
      refine ⟨85747623537800703334273277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228660329434135208891395405 85747623537800703334273277)
      ·
        refine ⟨32155358826675263750352479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85747623537800703334273277 32155358826675263750352479)
        ·
          refine ⟨48233038240012895625528719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32155358826675263750352479 48233038240012895625528719)
          ·
            refine ⟨72349557360019343438293079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48233038240012895625528719 72349557360019343438293079)
            ·
              refine ⟨108524336040029015157439619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72349557360019343438293079 108524336040029015157439619)
              ·
                refine ⟨162786504060043522736159429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108524336040029015157439619 162786504060043522736159429)
                ·
                  refine ⟨30522469511258160513029893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162786504060043522736159429 30522469511258160513029893)
                  ·
                    refine ⟨5722963033360905096193105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30522469511258160513029893 5722963033360905096193105)
                    ·
                      refine ⟨4292222275020678822144829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722963033360905096193105 4292222275020678822144829)
                      ·
                        rfl

theorem cell23_8359073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_8359073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359073 prefixEnd_8359073 := by exact prefixLift 8359073
  have htrace : WordTrace (prefixWord ++ tailWord_8359073) baseStart_8359073 baseEnd_8359073 := by
    simpa [prefixWord, tailWord_8359073, baseEnd_8359073] using wordTrace_append hprefix tailTrace_8359073
  have hstable : (prefixWord ++ tailWord_8359073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359073).length < 2 ^ (prefixWord ++ tailWord_8359073).sum := by decide
  have hdescent : baseEnd_8359073 < baseStart_8359073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359140 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_8359140 : Nat := 118140960795 + 8359140 * 2 ^ 59
def prefixEnd_8359140 : Nat := 4983230072969 + 3 ^ 40 * 8359140 * 2
def baseEnd_8359140 : Nat := 4292256678224530060007021

theorem tailTrace_8359140 : CollatzResearch.WordTrace tailWord_8359140 prefixEnd_8359140 4292256678224530060007021 := by
  unfold tailWord_8359140
  simp only [CollatzResearch.WordTrace]
  refine ⟨152441441468135441148941437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203255255290847254865255249 152441441468135441148941437)
  ·
    refine ⟨57165540550550790430853039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152441441468135441148941437 57165540550550790430853039)
    ·
      refine ⟨85748310825826185646279559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57165540550550790430853039 85748310825826185646279559)
      ·
        refine ⟨128622466238739278469419339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85748310825826185646279559 128622466238739278469419339)
        ·
          refine ⟨192933699358108917704129009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128622466238739278469419339 192933699358108917704129009)
          ·
            refine ⟨144700274518581688278096757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192933699358108917704129009 144700274518581688278096757)
            ·
              refine ⟨13565650736117033276071571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144700274518581688278096757 13565650736117033276071571)
              ·
                refine ⟨20348476104175549914107357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13565650736117033276071571 20348476104175549914107357)
                ·
                  refine ⟨7630678539065831217790259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20348476104175549914107357 7630678539065831217790259)
                  ·
                    refine ⟨11446017808598746826685389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7630678539065831217790259 11446017808598746826685389)
                    ·
                      refine ⟨4292256678224530060007021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11446017808598746826685389 4292256678224530060007021)
                      ·
                        rfl

theorem cell23_8359140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_8359140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359140 prefixEnd_8359140 := by exact prefixLift 8359140
  have htrace : WordTrace (prefixWord ++ tailWord_8359140) baseStart_8359140 baseEnd_8359140 := by
    simpa [prefixWord, tailWord_8359140, baseEnd_8359140] using wordTrace_append hprefix tailTrace_8359140
  have hstable : (prefixWord ++ tailWord_8359140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359140).length < 2 ^ (prefixWord ++ tailWord_8359140).sum := by decide
  have hdescent : baseEnd_8359140 < baseStart_8359140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359203 : List Nat := [1, 1, 1, 4, 2, 5, 1, 8]
def baseStart_8359203 : Nat := 118140960795 + 8359203 * 2 ^ 59
def prefixEnd_8359203 : Nat := 4983230072969 + 3 ^ 40 * 8359203 * 2
def baseEnd_8359203 : Nat := 158973667685398641241453

theorem tailTrace_8359203 : CollatzResearch.WordTrace tailWord_8359203 prefixEnd_8359203 158973667685398641241453 := by
  unfold tailWord_8359203
  simp only [CollatzResearch.WordTrace]
  refine ⟨304885180735042644057426263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203256787156695096038284175 304885180735042644057426263)
  ·
    refine ⟨457327771102563966086139395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304885180735042644057426263 457327771102563966086139395)
    ·
      refine ⟨685991656653845949129209093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457327771102563966086139395 685991656653845949129209093)
      ·
        refine ⟨128623435622596115461726705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 685991656653845949129209093 128623435622596115461726705)
        ·
          refine ⟨96467576716947086596295029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128623435622596115461726705 96467576716947086596295029)
          ·
            refine ⟨9043835317213789368402659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96467576716947086596295029 9043835317213789368402659)
            ·
              refine ⟨13565752975820684052603989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9043835317213789368402659 13565752975820684052603989)
              ·
                refine ⟨158973667685398641241453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13565752975820684052603989 158973667685398641241453)
                ·
                  rfl

theorem cell23_8359203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 8].length) (baseStart_8359203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359203 prefixEnd_8359203 := by exact prefixLift 8359203
  have htrace : WordTrace (prefixWord ++ tailWord_8359203) baseStart_8359203 baseEnd_8359203 := by
    simpa [prefixWord, tailWord_8359203, baseEnd_8359203] using wordTrace_append hprefix tailTrace_8359203
  have hstable : (prefixWord ++ tailWord_8359203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359203).length < 2 ^ (prefixWord ++ tailWord_8359203).sum := by decide
  have hdescent : baseEnd_8359203 < baseStart_8359203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359210 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_8359210 : Nat := 118140960795 + 8359210 * 2 ^ 59
def prefixEnd_8359210 : Nat := 4983230072969 + 3 ^ 40 * 8359210 * 2
def baseEnd_8359210 : Nat := 4292292621870344786131699

theorem tailTrace_8359210 : CollatzResearch.WordTrace tailWord_8359210 prefixEnd_8359210 4292292621870344786131699 := by
  unfold tailWord_8359210
  simp only [CollatzResearch.WordTrace]
  refine ⟨76221359011504321063232771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203256957364011522835287389 76221359011504321063232771)
  ·
    refine ⟨114332038517256481594849157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76221359011504321063232771 114332038517256481594849157)
    ·
      refine ⟨21437257221985590299034217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114332038517256481594849157 21437257221985590299034217)
      ·
        refine ⟨16077942916489192724275663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21437257221985590299034217 16077942916489192724275663)
        ·
          refine ⟨24116914374733789086413495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16077942916489192724275663 24116914374733789086413495)
          ·
            refine ⟨36175371562100683629620243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24116914374733789086413495 36175371562100683629620243)
            ·
              refine ⟨54263057343151025444430365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36175371562100683629620243 54263057343151025444430365)
              ·
                refine ⟨20348646503681634541661387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54263057343151025444430365 20348646503681634541661387)
                ·
                  refine ⟨30522969755522451812492081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20348646503681634541661387 30522969755522451812492081)
                  ·
                    refine ⟨22892227316641838859369061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30522969755522451812492081 22892227316641838859369061)
                    ·
                      refine ⟨4292292621870344786131699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22892227316641838859369061 4292292621870344786131699)
                      ·
                        rfl

theorem cell23_8359210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_8359210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359210 prefixEnd_8359210 := by exact prefixLift 8359210
  have htrace : WordTrace (prefixWord ++ tailWord_8359210) baseStart_8359210 baseEnd_8359210 := by
    simpa [prefixWord, tailWord_8359210, baseEnd_8359210] using wordTrace_append hprefix tailTrace_8359210
  have hstable : (prefixWord ++ tailWord_8359210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359210).length < 2 ^ (prefixWord ++ tailWord_8359210).sum := by decide
  have hdescent : baseEnd_8359210 < baseStart_8359210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359216 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 2, 7]
def baseStart_8359216 : Nat := 118140960795 + 8359216 * 2 ^ 59
def prefixEnd_8359216 : Nat := 4983230072969 + 3 ^ 40 * 8359216 * 2
def baseEnd_8359216 : Nat := 1430765234251423920885557

theorem tailTrace_8359216 : CollatzResearch.WordTrace tailWord_8359216 prefixEnd_8359216 1430765234251423920885557 := by
  unfold tailWord_8359216
  simp only [CollatzResearch.WordTrace]
  refine ⟨152442827441997773638824751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203257103255997031518433001 152442827441997773638824751)
  ·
    refine ⟨228664241162996660458237127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152442827441997773638824751 228664241162996660458237127)
    ·
      refine ⟨342996361744494990687355691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228664241162996660458237127 342996361744494990687355691)
      ·
        refine ⟨514494542616742486031033537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342996361744494990687355691 514494542616742486031033537)
        ·
          refine ⟨385870906962556864523275153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514494542616742486031033537 385870906962556864523275153)
          ·
            refine ⟨289403180221917648392456365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385870906962556864523275153 289403180221917648392456365)
            ·
              refine ⟨108526192583219118147171137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289403180221917648392456365 108526192583219118147171137)
              ·
                refine ⟨81394644437414338610378353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108526192583219118147171137 81394644437414338610378353)
                ·
                  refine ⟨61045983328060753957783765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81394644437414338610378353 61045983328060753957783765)
                  ·
                    refine ⟨1430765234251423920885557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61045983328060753957783765 1430765234251423920885557)
                    ·
                      rfl

theorem cell23_8359216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_8359216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359216 prefixEnd_8359216 := by exact prefixLift 8359216
  have htrace : WordTrace (prefixWord ++ tailWord_8359216) baseStart_8359216 baseEnd_8359216 := by
    simpa [prefixWord, tailWord_8359216, baseEnd_8359216] using wordTrace_append hprefix tailTrace_8359216
  have hstable : (prefixWord ++ tailWord_8359216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359216).length < 2 ^ (prefixWord ++ tailWord_8359216).sum := by decide
  have hdescent : baseEnd_8359216 < baseStart_8359216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359220 : List Nat := [2, 5, 1, 1, 1, 1, 5, 7]
def baseStart_8359220 : Nat := 118140960795 + 8359220 * 2 ^ 59
def prefixEnd_8359220 : Nat := 4983230072969 + 3 ^ 40 * 8359220 * 2
def baseEnd_8359220 : Nat := 158973990988032953592839

theorem tailTrace_8359220 : CollatzResearch.WordTrace tailWord_8359220 prefixEnd_8359220 158973990988032953592839 := by
  unfold tailWord_8359220
  simp only [CollatzResearch.WordTrace]
  refine ⟨152442900387990527980397557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203257200517320703973863409 152442900387990527980397557)
  ·
    refine ⟨14291521911374111998162271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152442900387990527980397557 14291521911374111998162271)
    ·
      refine ⟨21437282867061167997243407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14291521911374111998162271 21437282867061167997243407)
      ·
        refine ⟨32155924300591751995865111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21437282867061167997243407 32155924300591751995865111)
        ·
          refine ⟨48233886450887627993797667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32155924300591751995865111 48233886450887627993797667)
          ·
            refine ⟨72350829676331441990696501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48233886450887627993797667 72350829676331441990696501)
            ·
              refine ⟨6782890282156072686627797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72350829676331441990696501 6782890282156072686627797)
              ·
                refine ⟨158973990988032953592839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6782890282156072686627797 158973990988032953592839)
                ·
                  rfl

theorem cell23_8359220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 7].length) (baseStart_8359220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359220 prefixEnd_8359220 := by exact prefixLift 8359220
  have htrace : WordTrace (prefixWord ++ tailWord_8359220) baseStart_8359220 baseEnd_8359220 := by
    simpa [prefixWord, tailWord_8359220, baseEnd_8359220] using wordTrace_append hprefix tailTrace_8359220
  have hstable : (prefixWord ++ tailWord_8359220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359220).length < 2 ^ (prefixWord ++ tailWord_8359220).sum := by decide
  have hdescent : baseEnd_8359220 < baseStart_8359220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359230 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_8359230 : Nat := 118140960795 + 8359230 * 2 ^ 59
def prefixEnd_8359230 : Nat := 4983230072969 + 3 ^ 40 * 8359230 * 2
def baseEnd_8359230 : Nat := 4292302891483434707881607

theorem tailTrace_8359230 : CollatzResearch.WordTrace tailWord_8359230 prefixEnd_8359230 4292302891483434707881607 := by
  unfold tailWord_8359230
  simp only [CollatzResearch.WordTrace]
  refine ⟨38110770688243103458582393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203257443670629885112439429 38110770688243103458582393)
  ·
    refine ⟨28583078016182327593936795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38110770688243103458582393 28583078016182327593936795)
    ·
      refine ⟨42874617024273491390905193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28583078016182327593936795 42874617024273491390905193)
      ·
        refine ⟨32155962768205118543178895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42874617024273491390905193 32155962768205118543178895)
        ·
          refine ⟨48233944152307677814768343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32155962768205118543178895 48233944152307677814768343)
          ·
            refine ⟨72350916228461516722152515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48233944152307677814768343 72350916228461516722152515)
            ·
              refine ⟨108526374342692275083228773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72350916228461516722152515 108526374342692275083228773)
              ·
                refine ⟨20348695189254801578105395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108526374342692275083228773 20348695189254801578105395)
                ·
                  refine ⟨30523042783882202367158093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20348695189254801578105395 30523042783882202367158093)
                  ·
                    refine ⟨11446141043955825887684285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30523042783882202367158093 11446141043955825887684285)
                    ·
                      refine ⟨4292302891483434707881607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11446141043955825887684285 4292302891483434707881607)
                      ·
                        rfl

theorem cell23_8359230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_8359230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359230 prefixEnd_8359230 := by exact prefixLift 8359230
  have htrace : WordTrace (prefixWord ++ tailWord_8359230) baseStart_8359230 baseEnd_8359230 := by
    simpa [prefixWord, tailWord_8359230, baseEnd_8359230] using wordTrace_append hprefix tailTrace_8359230
  have hstable : (prefixWord ++ tailWord_8359230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359230).length < 2 ^ (prefixWord ++ tailWord_8359230).sum := by decide
  have hdescent : baseEnd_8359230 < baseStart_8359230 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359261 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_8359261 : Nat := 118140960795 + 8359261 * 2 ^ 59
def prefixEnd_8359261 : Nat := 4983230072969 + 3 ^ 40 * 8359261 * 2
def baseEnd_8359261 : Nat := 4292318809383724086593965

theorem tailTrace_8359261 : CollatzResearch.WordTrace tailWord_8359261 prefixEnd_8359261 4292318809383724086593965 := by
  unfold tailWord_8359261
  simp only [CollatzResearch.WordTrace]
  refine ⟨304887296168832519963037637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203258197445888346642025091 304887296168832519963037637)
  ·
    refine ⟨57166368031656097493069557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304887296168832519963037637 57166368031656097493069557)
    ·
      refine ⟨5359347002967759139975271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57166368031656097493069557 5359347002967759139975271)
      ·
        refine ⟨8039020504451638709962907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5359347002967759139975271 8039020504451638709962907)
        ·
          refine ⟨12058530756677458064944361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8039020504451638709962907 12058530756677458064944361)
          ·
            refine ⟨9043898067508093548708271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12058530756677458064944361 9043898067508093548708271)
            ·
              refine ⟨13565847101262140323062407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9043898067508093548708271 13565847101262140323062407)
              ·
                refine ⟨20348770651893210484593611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13565847101262140323062407 20348770651893210484593611)
                ·
                  refine ⟨30523155977839815726890417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20348770651893210484593611 30523155977839815726890417)
                  ·
                    refine ⟨22892366983379861795167813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30523155977839815726890417 22892366983379861795167813)
                    ·
                      refine ⟨4292318809383724086593965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22892366983379861795167813 4292318809383724086593965)
                      ·
                        rfl

theorem cell23_8359261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_8359261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359261 prefixEnd_8359261 := by exact prefixLift 8359261
  have htrace : WordTrace (prefixWord ++ tailWord_8359261) baseStart_8359261 baseEnd_8359261 := by
    simpa [prefixWord, tailWord_8359261, baseEnd_8359261] using wordTrace_append hprefix tailTrace_8359261
  have hstable : (prefixWord ++ tailWord_8359261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359261).length < 2 ^ (prefixWord ++ tailWord_8359261).sum := by decide
  have hdescent : baseEnd_8359261 < baseStart_8359261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359264 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 2, 1, 3]
def baseStart_8359264 : Nat := 118140960795 + 8359264 * 2 ^ 59
def prefixEnd_8359264 : Nat := 4983230072969 + 3 ^ 40 * 8359264 * 2
def baseEnd_8359264 : Nat := 4292320349825687574856451

theorem tailTrace_8359264 : CollatzResearch.WordTrace tailWord_8359264 prefixEnd_8359264 4292320349825687574856451 := by
  unfold tailWord_8359264
  simp only [CollatzResearch.WordTrace]
  refine ⟨152443702793910825737698423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203258270391881100983597897 152443702793910825737698423)
  ·
    refine ⟨228665554190866238606547635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152443702793910825737698423 228665554190866238606547635)
    ·
      refine ⟨342998331286299357909821453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228665554190866238606547635 342998331286299357909821453)
      ·
        refine ⟨128624374232362259216183045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342998331286299357909821453 128624374232362259216183045)
        ·
          refine ⟨24117070168567923603034321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128624374232362259216183045 24117070168567923603034321)
          ·
            refine ⟨18087802626425942702275741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24117070168567923603034321 18087802626425942702275741)
            ·
              refine ⟨6782925984909728513353403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18087802626425942702275741 6782925984909728513353403)
              ·
                refine ⟨10174388977364592770030105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6782925984909728513353403 10174388977364592770030105)
                ·
                  refine ⟨7630791733023444577522579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10174388977364592770030105 7630791733023444577522579)
                  ·
                    refine ⟨11446187599535166866283869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7630791733023444577522579 11446187599535166866283869)
                    ·
                      refine ⟨4292320349825687574856451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11446187599535166866283869 4292320349825687574856451)
                      ·
                        rfl

theorem cell23_8359264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_8359264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359264 prefixEnd_8359264 := by exact prefixLift 8359264
  have htrace : WordTrace (prefixWord ++ tailWord_8359264) baseStart_8359264 baseEnd_8359264 := by
    simpa [prefixWord, tailWord_8359264, baseEnd_8359264] using wordTrace_append hprefix tailTrace_8359264
  have hstable : (prefixWord ++ tailWord_8359264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359264).length < 2 ^ (prefixWord ++ tailWord_8359264).sum := by decide
  have hdescent : baseEnd_8359264 < baseStart_8359264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359321 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 2, 2, 2]
def baseStart_8359321 : Nat := 118140960795 + 8359321 * 2 ^ 59
def prefixEnd_8359321 : Nat := 4983230072969 + 3 ^ 40 * 8359321 * 2
def baseEnd_8359321 : Nat := 4292349618222993851843689

theorem tailTrace_8359321 : CollatzResearch.WordTrace tailWord_8359321 prefixEnd_8359321 4292349618222993851843689 := by
  unfold tailWord_8359321
  simp only [CollatzResearch.WordTrace]
  refine ⟨304889484548615150210221817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203259656365743433473481211 304889484548615150210221817)
  ·
    refine ⟨228667113411461362657666363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304889484548615150210221817 228667113411461362657666363)
    ·
      refine ⟨343000670117192043986499545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228667113411461362657666363 343000670117192043986499545)
      ·
        refine ⟨257250502587894032989874659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343000670117192043986499545 257250502587894032989874659)
        ·
          refine ⟨385875753881841049484811989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257250502587894032989874659 385875753881841049484811989)
          ·
            refine ⟨9043962981605649597300281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 385875753881841049484811989 9043962981605649597300281)
            ·
              refine ⟨6782972236204237197975211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9043962981605649597300281 6782972236204237197975211)
              ·
                refine ⟨10174458354306355796962817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6782972236204237197975211 10174458354306355796962817)
                ·
                  refine ⟨7630843765729766847722113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10174458354306355796962817 7630843765729766847722113)
                  ·
                    refine ⟨5723132824297325135791585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7630843765729766847722113 5723132824297325135791585)
                    ·
                      refine ⟨4292349618222993851843689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723132824297325135791585 4292349618222993851843689)
                      ·
                        rfl

theorem cell23_8359321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_8359321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359321 prefixEnd_8359321 := by exact prefixLift 8359321
  have htrace : WordTrace (prefixWord ++ tailWord_8359321) baseStart_8359321 baseEnd_8359321 := by
    simpa [prefixWord, tailWord_8359321, baseEnd_8359321] using wordTrace_append hprefix tailTrace_8359321
  have hstable : (prefixWord ++ tailWord_8359321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359321).length < 2 ^ (prefixWord ++ tailWord_8359321).sum := by decide
  have hdescent : baseEnd_8359321 < baseStart_8359321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359343 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_8359343 : Nat := 118140960795 + 8359343 * 2 ^ 59
def prefixEnd_8359343 : Nat := 4983230072969 + 3 ^ 40 * 8359343 * 2
def baseEnd_8359343 : Nat := 4292360914797392765768587

theorem tailTrace_8359343 : CollatzResearch.WordTrace tailWord_8359343 prefixEnd_8359343 4292360914797392765768587 := by
  unfold tailWord_8359343
  simp only [CollatzResearch.WordTrace]
  refine ⟨304890286954535447967522683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203260191303023631978348455 304890286954535447967522683)
  ·
    refine ⟨457335430431803171951284025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304890286954535447967522683 457335430431803171951284025)
    ·
      refine ⟨343001572823852378963463019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457335430431803171951284025 343001572823852378963463019)
      ·
        refine ⟨514502359235778568445194529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343001572823852378963463019 514502359235778568445194529)
        ·
          refine ⟨385876769426833926333895897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514502359235778568445194529 385876769426833926333895897)
          ·
            refine ⟨289407577070125444750421923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385876769426833926333895897 289407577070125444750421923)
            ·
              refine ⟨434111365605188167125632885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289407577070125444750421923 434111365605188167125632885)
              ·
                refine ⟨40697940525486390668028083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 434111365605188167125632885 40697940525486390668028083)
                ·
                  refine ⟨61046910788229586002042125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40697940525486390668028083 61046910788229586002042125)
                  ·
                    refine ⟨22892591545586094750765797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61046910788229586002042125 22892591545586094750765797)
                    ·
                      refine ⟨4292360914797392765768587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22892591545586094750765797 4292360914797392765768587)
                      ·
                        rfl

theorem cell23_8359343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_8359343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359343 prefixEnd_8359343 := by exact prefixLift 8359343
  have htrace : WordTrace (prefixWord ++ tailWord_8359343) baseStart_8359343 baseEnd_8359343 := by
    simpa [prefixWord, tailWord_8359343, baseEnd_8359343] using wordTrace_append hprefix tailTrace_8359343
  have hstable : (prefixWord ++ tailWord_8359343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359343).length < 2 ^ (prefixWord ++ tailWord_8359343).sum := by decide
  have hdescent : baseEnd_8359343 < baseStart_8359343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359360 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_8359360 : Nat := 118140960795 + 8359360 * 2 ^ 59
def prefixEnd_8359360 : Nat := 4983230072969 + 3 ^ 40 * 8359360 * 2
def baseEnd_8359360 : Nat := 4292369643968519199256009

theorem tailTrace_8359360 : CollatzResearch.WordTrace tailWord_8359360 prefixEnd_8359360 4292369643968519199256009 := by
  unfold tailWord_8359360
  simp only [CollatzResearch.WordTrace]
  refine ⟨152445453497736929935445767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203260604663649239913927689 152445453497736929935445767)
  ·
    refine ⟨228668180246605394903168651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152445453497736929935445767 228668180246605394903168651)
    ·
      refine ⟨343002270369908092354752977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228668180246605394903168651 343002270369908092354752977)
      ·
        refine ⟨257251702777431069266064733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343002270369908092354752977 257251702777431069266064733)
        ·
          refine ⟨96469388541536650974774275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257251702777431069266064733 96469388541536650974774275)
          ·
            refine ⟨144704082812304976462161413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96469388541536650974774275 144704082812304976462161413)
            ·
              refine ⟨27132015527307183086655265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144704082812304976462161413 27132015527307183086655265)
              ·
                refine ⟨20349011645480387314991449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27132015527307183086655265 20349011645480387314991449)
                ·
                  refine ⟨15261758734110290486243587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20349011645480387314991449 15261758734110290486243587)
                  ·
                    refine ⟨22892638101165435729365381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15261758734110290486243587 22892638101165435729365381)
                    ·
                      refine ⟨4292369643968519199256009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22892638101165435729365381 4292369643968519199256009)
                      ·
                        rfl

theorem cell23_8359360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_8359360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359360 prefixEnd_8359360 := by exact prefixLift 8359360
  have htrace : WordTrace (prefixWord ++ tailWord_8359360) baseStart_8359360 baseEnd_8359360 := by
    simpa [prefixWord, tailWord_8359360, baseEnd_8359360] using wordTrace_append hprefix tailTrace_8359360
  have hstable : (prefixWord ++ tailWord_8359360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359360).length < 2 ^ (prefixWord ++ tailWord_8359360).sum := by decide
  have hdescent : baseEnd_8359360 < baseStart_8359360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359397 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_8359397 : Nat := 118140960795 + 8359397 * 2 ^ 59
def prefixEnd_8359397 : Nat := 4983230072969 + 3 ^ 40 * 8359397 * 2
def baseEnd_8359397 : Nat := 4292388642752735554493339

theorem tailTrace_8359397 : CollatzResearch.WordTrace tailWord_8359397 prefixEnd_8359397 4292388642752735554493339 := by
  unfold tailWord_8359397
  simp only [CollatzResearch.WordTrace]
  refine ⟨304892256496339815189988445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203261504330893210126658963 304892256496339815189988445)
  ·
    refine ⟨114334596186127430696245667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304892256496339815189988445 114334596186127430696245667)
    ·
      refine ⟨171501894279191146044368501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114334596186127430696245667 171501894279191146044368501)
      ·
        refine ⟨16078302588674169941659547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171501894279191146044368501 16078302588674169941659547)
        ·
          refine ⟨24117453883011254912489321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16078302588674169941659547 24117453883011254912489321)
          ·
            refine ⟨18088090412258441184366991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24117453883011254912489321 18088090412258441184366991)
            ·
              refine ⟨27132135618387661776550487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18088090412258441184366991 27132135618387661776550487)
              ·
                refine ⟨40698203427581492664825731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27132135618387661776550487 40698203427581492664825731)
                ·
                  refine ⟨61047305141372238997238597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40698203427581492664825731 61047305141372238997238597)
                  ·
                    refine ⟨11446369714007294811982237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61047305141372238997238597 11446369714007294811982237)
                    ·
                      refine ⟨4292388642752735554493339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11446369714007294811982237 4292388642752735554493339)
                      ·
                        rfl

theorem cell23_8359397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_8359397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359397 prefixEnd_8359397 := by exact prefixLift 8359397
  have htrace : WordTrace (prefixWord ++ tailWord_8359397) baseStart_8359397 baseEnd_8359397 := by
    simpa [prefixWord, tailWord_8359397, baseEnd_8359397] using wordTrace_append hprefix tailTrace_8359397
  have hstable : (prefixWord ++ tailWord_8359397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359397).length < 2 ^ (prefixWord ++ tailWord_8359397).sum := by decide
  have hdescent : baseEnd_8359397 < baseStart_8359397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359423 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_8359423 : Nat := 118140960795 + 8359423 * 2 ^ 59
def prefixEnd_8359423 : Nat := 4983230072969 + 3 ^ 40 * 8359423 * 2
def baseEnd_8359423 : Nat := 4292401993249752452768219

theorem tailTrace_8359423 : CollatzResearch.WordTrace tailWord_8359423 prefixEnd_8359423 4292401993249752452768219 := by
  unfold tailWord_8359423
  simp only [CollatzResearch.WordTrace]
  refine ⟨304893204794245621630434923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203262136529497081086956615 304893204794245621630434923)
  ·
    refine ⟨457339807191368432445652385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304893204794245621630434923 457339807191368432445652385)
    ·
      refine ⟨343004855393526324334239289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457339807191368432445652385 343004855393526324334239289)
      ·
        refine ⟨257253641545144743250679467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343004855393526324334239289 257253641545144743250679467)
        ·
          refine ⟨385880462317717114876019201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257253641545144743250679467 385880462317717114876019201)
          ·
            refine ⟨289410346738287836157014401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385880462317717114876019201 289410346738287836157014401)
            ·
              refine ⟨217057760053715877117760801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289410346738287836157014401 217057760053715877117760801)
              ·
                refine ⟨162793320040286907838320601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217057760053715877117760801 162793320040286907838320601)
                ·
                  refine ⟨122094990030215180878740451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162793320040286907838320601 122094990030215180878740451)
                  ·
                    refine ⟨183142485045322771318110677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122094990030215180878740451 183142485045322771318110677)
                    ·
                      refine ⟨4292401993249752452768219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183142485045322771318110677 4292401993249752452768219)
                      ·
                        rfl

theorem cell23_8359423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_8359423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359423 prefixEnd_8359423 := by exact prefixLift 8359423
  have htrace : WordTrace (prefixWord ++ tailWord_8359423) baseStart_8359423 baseEnd_8359423 := by
    simpa [prefixWord, tailWord_8359423, baseEnd_8359423] using wordTrace_append hprefix tailTrace_8359423
  have hstable : (prefixWord ++ tailWord_8359423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359423).length < 2 ^ (prefixWord ++ tailWord_8359423).sum := by decide
  have hdescent : baseEnd_8359423 < baseStart_8359423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359477 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_8359477 : Nat := 118140960795 + 8359477 * 2 ^ 59
def prefixEnd_8359477 : Nat := 4983230072969 + 3 ^ 40 * 8359477 * 2
def baseEnd_8359477 : Nat := 1430809907068365080497657

theorem tailTrace_8359477 : CollatzResearch.WordTrace tailWord_8359477 prefixEnd_8359477 1430809907068365080497657 := by
  unfold tailWord_8359477
  simp only [CollatzResearch.WordTrace]
  refine ⟨304895174336049988852900685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203263449557366659235267123 304895174336049988852900685)
  ·
    refine ⟨114335690376018745819837757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304895174336049988852900685 114335690376018745819837757)
    ·
      refine ⟨42875883891007029682439159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114335690376018745819837757 42875883891007029682439159)
      ·
        refine ⟨64313825836510544523658739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42875883891007029682439159 64313825836510544523658739)
        ·
          refine ⟨96470738754765816785488109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64313825836510544523658739 96470738754765816785488109)
          ·
            refine ⟨36176527033037181294558041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96470738754765816785488109 36176527033037181294558041)
            ·
              refine ⟨27132395274777885970918531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36176527033037181294558041 27132395274777885970918531)
              ·
                refine ⟨40698592912166828956377797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27132395274777885970918531 40698592912166828956377797)
                ·
                  refine ⟨7630986171031280429320837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40698592912166828956377797 7630986171031280429320837)
                  ·
                    refine ⟨1430809907068365080497657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7630986171031280429320837 1430809907068365080497657)
                    ·
                      rfl

theorem cell23_8359477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_8359477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359477 prefixEnd_8359477 := by exact prefixLift 8359477
  have htrace : WordTrace (prefixWord ++ tailWord_8359477) baseStart_8359477 baseEnd_8359477 := by
    simpa [prefixWord, tailWord_8359477, baseEnd_8359477] using wordTrace_append hprefix tailTrace_8359477
  have hstable : (prefixWord ++ tailWord_8359477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359477).length < 2 ^ (prefixWord ++ tailWord_8359477).sum := by decide
  have hdescent : baseEnd_8359477 < baseStart_8359477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359478 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_8359478 : Nat := 118140960795 + 8359478 * 2 ^ 59
def prefixEnd_8359478 : Nat := 4983230072969 + 3 ^ 40 * 8359478 * 2
def baseEnd_8359478 : Nat := 4292430234685749737580467

theorem tailTrace_8359478 : CollatzResearch.WordTrace tailWord_8359478 prefixEnd_8359478 4292430234685749737580467 := by
  unfold tailWord_8359478
  simp only [CollatzResearch.WordTrace]
  refine ⟨19055950675565397876480443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203263473872697577349124725 19055950675565397876480443)
  ·
    refine ⟨28583926013348096814720665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19055950675565397876480443 28583926013348096814720665)
    ·
      refine ⟨21437944510011072611040499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28583926013348096814720665 21437944510011072611040499)
      ·
        refine ⟨32156916765016608916560749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21437944510011072611040499 32156916765016608916560749)
        ·
          refine ⟨12058843786881228343710281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32156916765016608916560749 12058843786881228343710281)
          ·
            refine ⟨9044132840160921257782711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12058843786881228343710281 9044132840160921257782711)
            ·
              refine ⟨13566199260241381886674067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9044132840160921257782711 13566199260241381886674067)
              ·
                refine ⟨20349298890362072830011101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13566199260241381886674067 20349298890362072830011101)
                ·
                  refine ⟨7630987083885777311254163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20349298890362072830011101 7630987083885777311254163)
                  ·
                    refine ⟨11446480625828665966881245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7630987083885777311254163 11446480625828665966881245)
                    ·
                      refine ⟨4292430234685749737580467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11446480625828665966881245 4292430234685749737580467)
                      ·
                        rfl

theorem cell23_8359478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_8359478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359478 prefixEnd_8359478 := by exact prefixLift 8359478
  have htrace : WordTrace (prefixWord ++ tailWord_8359478) baseStart_8359478 baseEnd_8359478 := by
    simpa [prefixWord, tailWord_8359478, baseEnd_8359478] using wordTrace_append hprefix tailTrace_8359478
  have hstable : (prefixWord ++ tailWord_8359478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359478).length < 2 ^ (prefixWord ++ tailWord_8359478).sum := by decide
  have hdescent : baseEnd_8359478 < baseStart_8359478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359480 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_8359480 : Nat := 118140960795 + 8359480 * 2 ^ 59
def prefixEnd_8359480 : Nat := 4983230072969 + 3 ^ 40 * 8359480 * 2
def baseEnd_8359480 : Nat := 4292431261647058729755457

theorem tailTrace_8359480 : CollatzResearch.WordTrace tailWord_8359480 prefixEnd_8359480 4292431261647058729755457 := by
  unfold tailWord_8359480
  simp only [CollatzResearch.WordTrace]
  refine ⟨152447641877519560182629947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203263522503359413576839929 152447641877519560182629947)
  ·
    refine ⟨228671462816279340273944921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152447641877519560182629947 228671462816279340273944921)
    ·
      refine ⟨171503597112209505205458691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228671462816279340273944921 171503597112209505205458691)
      ·
        refine ⟨257255395668314257808188037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171503597112209505205458691 257255395668314257808188037)
        ·
          refine ⟨48235386687808923339035257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257255395668314257808188037 48235386687808923339035257)
          ·
            refine ⟨36176540015856692504276443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48235386687808923339035257 36176540015856692504276443)
            ·
              refine ⟨54264810023785038756414665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36176540015856692504276443 54264810023785038756414665)
              ·
                refine ⟨40698607517838779067310999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54264810023785038756414665 40698607517838779067310999)
                ·
                  refine ⟨61047911276758168600966499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40698607517838779067310999 61047911276758168600966499)
                  ·
                    refine ⟨91571866915137252901449749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61047911276758168600966499 91571866915137252901449749)
                    ·
                      refine ⟨4292431261647058729755457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91571866915137252901449749 4292431261647058729755457)
                      ·
                        rfl

theorem cell23_8359480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_8359480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359480 prefixEnd_8359480 := by exact prefixLift 8359480
  have htrace : WordTrace (prefixWord ++ tailWord_8359480) baseStart_8359480 baseEnd_8359480 := by
    simpa [prefixWord, tailWord_8359480, baseEnd_8359480] using wordTrace_append hprefix tailTrace_8359480
  have hstable : (prefixWord ++ tailWord_8359480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359480).length < 2 ^ (prefixWord ++ tailWord_8359480).sum := by decide
  have hdescent : baseEnd_8359480 < baseStart_8359480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359667 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 3]
def baseStart_8359667 : Nat := 118140960795 + 8359667 * 2 ^ 59
def prefixEnd_8359667 : Nat := 4983230072969 + 3 ^ 40 * 8359667 * 2
def baseEnd_8359667 : Nat := 4292527282529449498117097

theorem tailTrace_8359667 : CollatzResearch.WordTrace tailWord_8359667 prefixEnd_8359667 4292527282529449498117097 := by
  unfold tailWord_8359667
  simp only [CollatzResearch.WordTrace]
  refine ⟨304902104205361651302317255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203268069470241100868211503 304902104205361651302317255)
  ·
    refine ⟨457353156308042476953475883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304902104205361651302317255 457353156308042476953475883)
    ·
      refine ⟨686029734462063715430213825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457353156308042476953475883 686029734462063715430213825)
      ·
        refine ⟨514522300846547786572660369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686029734462063715430213825 514522300846547786572660369)
        ·
          refine ⟨385891725634910839929495277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514522300846547786572660369 385891725634910839929495277)
          ·
            refine ⟨144709397113091564973560729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385891725634910839929495277 144709397113091564973560729)
            ·
              refine ⟨108532047834818673730170547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144709397113091564973560729 108532047834818673730170547)
              ·
                refine ⟨162798071752228010595255821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108532047834818673730170547 162798071752228010595255821)
                ·
                  refine ⟨61049276907085503973220933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162798071752228010595255821 61049276907085503973220933)
                  ·
                    refine ⟨11446739420078531994978925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61049276907085503973220933 11446739420078531994978925)
                    ·
                      refine ⟨4292527282529449498117097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11446739420078531994978925 4292527282529449498117097)
                      ·
                        rfl

theorem cell23_8359667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_8359667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359667 prefixEnd_8359667 := by exact prefixLift 8359667
  have htrace : WordTrace (prefixWord ++ tailWord_8359667) baseStart_8359667 baseEnd_8359667 := by
    simpa [prefixWord, tailWord_8359667, baseEnd_8359667] using wordTrace_append hprefix tailTrace_8359667
  have hstable : (prefixWord ++ tailWord_8359667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359667).length < 2 ^ (prefixWord ++ tailWord_8359667).sum := by decide
  have hdescent : baseEnd_8359667 < baseStart_8359667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359751 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 1, 5]
def baseStart_8359751 : Nat := 118140960795 + 8359751 * 2 ^ 59
def prefixEnd_8359751 : Nat := 4983230072969 + 3 ^ 40 * 8359751 * 2
def baseEnd_8359751 : Nat := 1430856804968142389822237

theorem tailTrace_8359751 : CollatzResearch.WordTrace tailWord_8359751 prefixEnd_8359751 1430856804968142389822237 := by
  unfold tailWord_8359751
  simp only [CollatzResearch.WordTrace]
  refine ⟨304905167937057333648375107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203270111958038222432250071 304905167937057333648375107)
  ·
    refine ⟨457357751905586000472562661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304905167937057333648375107 457357751905586000472562661)
    ·
      refine ⟨85754578482297375088605499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457357751905586000472562661 85754578482297375088605499)
      ·
        refine ⟨128631867723446062632908249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85754578482297375088605499 128631867723446062632908249)
        ·
          refine ⟨96473900792584546974681187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128631867723446062632908249 96473900792584546974681187)
          ·
            refine ⟨144710851188876820462021781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96473900792584546974681187 144710851188876820462021781)
            ·
              refine ⟨6783321149478600959157271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144710851188876820462021781 6783321149478600959157271)
              ·
                refine ⟨10174981724217901438735907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783321149478600959157271 10174981724217901438735907)
                ·
                  refine ⟨15262472586326852158103861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10174981724217901438735907 15262472586326852158103861)
                  ·
                    refine ⟨1430856804968142389822237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15262472586326852158103861 1430856804968142389822237)
                    ·
                      rfl

theorem cell23_8359751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_8359751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359751 prefixEnd_8359751 := by exact prefixLift 8359751
  have htrace : WordTrace (prefixWord ++ tailWord_8359751) baseStart_8359751 baseEnd_8359751 := by
    simpa [prefixWord, tailWord_8359751, baseEnd_8359751] using wordTrace_append hprefix tailTrace_8359751
  have hstable : (prefixWord ++ tailWord_8359751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359751).length < 2 ^ (prefixWord ++ tailWord_8359751).sum := by decide
  have hdescent : baseEnd_8359751 < baseStart_8359751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359777 : List Nat := [1, 2, 3, 1, 1, 1, 4, 10]
def baseStart_8359777 : Nat := 118140960795 + 8359777 * 2 ^ 59
def prefixEnd_8359777 : Nat := 4983230072969 + 3 ^ 40 * 8359777 * 2
def baseEnd_8359777 : Nat := 158984583903757187694133

theorem tailTrace_8359777 : CollatzResearch.WordTrace tailWord_8359777 prefixEnd_8359777 158984583903757187694133 := by
  unfold tailWord_8359777
  simp only [CollatzResearch.WordTrace]
  refine ⟨304906116234963140088821585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203270744156642093392547723 304906116234963140088821585)
  ·
    refine ⟨228679587176222355066616189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304906116234963140088821585 228679587176222355066616189)
    ·
      refine ⟨85754845191083383149981071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228679587176222355066616189 85754845191083383149981071)
      ·
        refine ⟨128632267786625074724971607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85754845191083383149981071 128632267786625074724971607)
        ·
          refine ⟨192948401679937612087457411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128632267786625074724971607 192948401679937612087457411)
          ·
            refine ⟨289422602519906418131186117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192948401679937612087457411 289422602519906418131186117)
            ·
              refine ⟨54266737972482453399597397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289422602519906418131186117 54266737972482453399597397)
              ·
                refine ⟨158984583903757187694133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54266737972482453399597397 158984583903757187694133)
                ·
                  rfl

theorem cell23_8359777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 10].length) (baseStart_8359777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359777 prefixEnd_8359777 := by exact prefixLift 8359777
  have htrace : WordTrace (prefixWord ++ tailWord_8359777) baseStart_8359777 baseEnd_8359777 := by
    simpa [prefixWord, tailWord_8359777, baseEnd_8359777] using wordTrace_append hprefix tailTrace_8359777
  have hstable : (prefixWord ++ tailWord_8359777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359777).length < 2 ^ (prefixWord ++ tailWord_8359777).sum := by decide
  have hdescent : baseEnd_8359777 < baseStart_8359777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359784 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_8359784 : Nat := 118140960795 + 8359784 * 2 ^ 59
def prefixEnd_8359784 : Nat := 4983230072969 + 3 ^ 40 * 8359784 * 2
def baseEnd_8359784 : Nat := 4292587359766025540354059

theorem tailTrace_8359784 : CollatzResearch.WordTrace tailWord_8359784 prefixEnd_8359784 4292587359766025540354059 := by
  unfold tailWord_8359784
  simp only [CollatzResearch.WordTrace]
  refine ⟨152453185772968890142163203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203270914363958520189550937 152453185772968890142163203)
  ·
    refine ⟨228679778659453335213244805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152453185772968890142163203 228679778659453335213244805)
    ·
      refine ⟨42877458498647500352483401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228679778659453335213244805 42877458498647500352483401)
      ·
        refine ⟨32158093873985625264362551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42877458498647500352483401 32158093873985625264362551)
        ·
          refine ⟨48237140810978437896543827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32158093873985625264362551 48237140810978437896543827)
          ·
            refine ⟨72355711216467656844815741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48237140810978437896543827 72355711216467656844815741)
            ·
              refine ⟨27133391706175371316805903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72355711216467656844815741 27133391706175371316805903)
              ·
                refine ⟨40700087559263056975208855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27133391706175371316805903 40700087559263056975208855)
                ·
                  refine ⟨61050131338894585462813283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40700087559263056975208855 61050131338894585462813283)
                  ·
                    refine ⟨91575197008341878194219925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61050131338894585462813283 91575197008341878194219925)
                    ·
                      refine ⟨4292587359766025540354059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91575197008341878194219925 4292587359766025540354059)
                      ·
                        rfl

theorem cell23_8359784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_8359784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359784 prefixEnd_8359784 := by exact prefixLift 8359784
  have htrace : WordTrace (prefixWord ++ tailWord_8359784) baseStart_8359784 baseEnd_8359784 := by
    simpa [prefixWord, tailWord_8359784, baseEnd_8359784] using wordTrace_append hprefix tailTrace_8359784
  have hstable : (prefixWord ++ tailWord_8359784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359784).length < 2 ^ (prefixWord ++ tailWord_8359784).sum := by decide
  have hdescent : baseEnd_8359784 < baseStart_8359784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359788 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 3, 2, 2]
def baseStart_8359788 : Nat := 118140960795 + 8359788 * 2 ^ 59
def prefixEnd_8359788 : Nat := 4983230072969 + 3 ^ 40 * 8359788 * 2
def baseEnd_8359788 : Nat := 4292589413688643524704041

theorem tailTrace_8359788 : CollatzResearch.WordTrace tailWord_8359788 prefixEnd_8359788 4292589413688643524704041 := by
  unfold tailWord_8359788
  simp only [CollatzResearch.WordTrace]
  refine ⟨152453258718961644483736009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203271011625282192644981345 152453258718961644483736009)
  ·
    refine ⟨114339944039221233362802007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152453258718961644483736009 114339944039221233362802007)
    ·
      refine ⟨171509916058831850044203011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114339944039221233362802007 171509916058831850044203011)
      ·
        refine ⟨257264874088247775066304517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171509916058831850044203011 257264874088247775066304517)
        ·
          refine ⟨48237163891546457824932097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257264874088247775066304517 48237163891546457824932097)
          ·
            refine ⟨36177872918659843368699073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48237163891546457824932097 36177872918659843368699073)
            ·
              refine ⟨27133404688994882526524305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36177872918659843368699073 27133404688994882526524305)
              ·
                refine ⟨20350053516746161894893229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27133404688994882526524305 20350053516746161894893229)
                ·
                  refine ⟨7631270068779810710584961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20350053516746161894893229 7631270068779810710584961)
                  ·
                    refine ⟨5723452551584858032938721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7631270068779810710584961 5723452551584858032938721)
                    ·
                      refine ⟨4292589413688643524704041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723452551584858032938721 4292589413688643524704041)
                      ·
                        rfl

theorem cell23_8359788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_8359788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359788 prefixEnd_8359788 := by exact prefixLift 8359788
  have htrace : WordTrace (prefixWord ++ tailWord_8359788) baseStart_8359788 baseEnd_8359788 := by
    simpa [prefixWord, tailWord_8359788, baseEnd_8359788] using wordTrace_append hprefix tailTrace_8359788
  have hstable : (prefixWord ++ tailWord_8359788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359788).length < 2 ^ (prefixWord ++ tailWord_8359788).sum := by decide
  have hdescent : baseEnd_8359788 < baseStart_8359788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359807 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 1, 9]
def baseStart_8359807 : Nat := 118140960795 + 8359807 * 2 ^ 59
def prefixEnd_8359807 : Nat := 4983230072969 + 3 ^ 40 * 8359807 * 2
def baseEnd_8359807 : Nat := 1430866389940359650122151

theorem tailTrace_8359807 : CollatzResearch.WordTrace tailWord_8359807 prefixEnd_8359807 1430866389940359650122151 := by
  unfold tailWord_8359807
  simp only [CollatzResearch.WordTrace]
  refine ⟨304907210424854455212413675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203271473616569636808275783 304907210424854455212413675)
  ·
    refine ⟨457360815637281682818620513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304907210424854455212413675 457360815637281682818620513)
    ·
      refine ⟨343020611727961262113965385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457360815637281682818620513 343020611727961262113965385)
      ·
        refine ⟨257265458795970946585474039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343020611727961262113965385 257265458795970946585474039)
        ·
          refine ⟨385898188193956419878211059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257265458795970946585474039 385898188193956419878211059)
          ·
            refine ⟨578847282290934629817316589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385898188193956419878211059 578847282290934629817316589)
            ·
              refine ⟨217067730859100486181493721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 578847282290934629817316589 217067730859100486181493721)
              ·
                refine ⟨162800798144325364636120291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217067730859100486181493721 162800798144325364636120291)
                ·
                  refine ⟨244201197216488046954180437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162800798144325364636120291 244201197216488046954180437)
                  ·
                    refine ⟨1430866389940359650122151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 244201197216488046954180437 1430866389940359650122151)
                    ·
                      rfl

theorem cell23_8359807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_8359807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359807 prefixEnd_8359807 := by exact prefixLift 8359807
  have htrace : WordTrace (prefixWord ++ tailWord_8359807) baseStart_8359807 baseEnd_8359807 := by
    simpa [prefixWord, tailWord_8359807, baseEnd_8359807] using wordTrace_append hprefix tailTrace_8359807
  have hstable : (prefixWord ++ tailWord_8359807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359807).length < 2 ^ (prefixWord ++ tailWord_8359807).sum := by decide
  have hdescent : baseEnd_8359807 < baseStart_8359807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359827 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 10]
def baseStart_8359827 : Nat := 118140960795 + 8359827 * 2 ^ 59
def prefixEnd_8359827 : Nat := 4983230072969 + 3 ^ 40 * 8359827 * 2
def baseEnd_8359827 : Nat := 4292609439434168872116361

theorem tailTrace_8359827 : CollatzResearch.WordTrace tailWord_8359827 prefixEnd_8359827 4292609439434168872116361 := by
  unfold tailWord_8359827
  simp only [CollatzResearch.WordTrace]
  refine ⟨304907939884781998628141735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203271959923187999085427823 304907939884781998628141735)
  ·
    refine ⟨457361909827172997942212603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304907939884781998628141735 457361909827172997942212603)
    ·
      refine ⟨686042864740759496913318905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457361909827172997942212603 686042864740759496913318905)
      ·
        refine ⟨514532148555569622684989179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686042864740759496913318905 514532148555569622684989179)
        ·
          refine ⟨771798222833354434027483769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514532148555569622684989179 771798222833354434027483769)
          ·
            refine ⟨578848667125015825520612827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771798222833354434027483769 578848667125015825520612827)
            ·
              refine ⟨868273000687523738280919241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578848667125015825520612827 868273000687523738280919241)
              ·
                refine ⟨651204750515642803710689431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868273000687523738280919241 651204750515642803710689431)
                ·
                  refine ⟨976807125773464205566034147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651204750515642803710689431 976807125773464205566034147)
                  ·
                    refine ⟨1465210688660196308349051221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 976807125773464205566034147 1465210688660196308349051221)
                    ·
                      refine ⟨4292609439434168872116361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1465210688660196308349051221 4292609439434168872116361)
                      ·
                        rfl

theorem cell23_8359827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_8359827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359827 prefixEnd_8359827 := by exact prefixLift 8359827
  have htrace : WordTrace (prefixWord ++ tailWord_8359827) baseStart_8359827 baseEnd_8359827 := by
    simpa [prefixWord, tailWord_8359827, baseEnd_8359827] using wordTrace_append hprefix tailTrace_8359827
  have hstable : (prefixWord ++ tailWord_8359827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359827).length < 2 ^ (prefixWord ++ tailWord_8359827).sum := by decide
  have hdescent : baseEnd_8359827 < baseStart_8359827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359832 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 2, 4]
def baseStart_8359832 : Nat := 118140960795 + 8359832 * 2 ^ 59
def prefixEnd_8359832 : Nat := 4983230072969 + 3 ^ 40 * 8359832 * 2
def baseEnd_8359832 : Nat := 1430870668945813784184613

theorem tailTrace_8359832 : CollatzResearch.WordTrace tailWord_8359832 prefixEnd_8359832 1430870668945813784184613 := by
  unfold tailWord_8359832
  simp only [CollatzResearch.WordTrace]
  refine ⟨152454061124881942241036875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203272081499842589654715833 152454061124881942241036875)
  ·
    refine ⟨228681091687322913361555313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152454061124881942241036875 228681091687322913361555313)
    ·
      refine ⟨171510818765492185021166485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228681091687322913361555313 171510818765492185021166485)
      ·
        refine ⟨8039569629632446172867179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171510818765492185021166485 8039569629632446172867179)
        ·
          refine ⟨12059354444448669259300769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8039569629632446172867179 12059354444448669259300769)
          ·
            refine ⟨9044515833336501944475577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12059354444448669259300769 9044515833336501944475577)
            ·
              refine ⟨6783386875002376458356683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9044515833336501944475577 6783386875002376458356683)
              ·
                refine ⟨10175080312503564687535025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783386875002376458356683 10175080312503564687535025)
                ·
                  refine ⟨7631310234377673515651269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10175080312503564687535025 7631310234377673515651269)
                  ·
                    refine ⟨1430870668945813784184613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7631310234377673515651269 1430870668945813784184613)
                    ·
                      rfl

theorem cell23_8359832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_8359832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359832 prefixEnd_8359832 := by exact prefixLift 8359832
  have htrace : WordTrace (prefixWord ++ tailWord_8359832) baseStart_8359832 baseEnd_8359832 := by
    simpa [prefixWord, tailWord_8359832, baseEnd_8359832] using wordTrace_append hprefix tailTrace_8359832
  have hstable : (prefixWord ++ tailWord_8359832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359832).length < 2 ^ (prefixWord ++ tailWord_8359832).sum := by decide
  have hdescent : baseEnd_8359832 < baseStart_8359832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359842 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_8359842 : Nat := 118140960795 + 8359842 * 2 ^ 59
def prefixEnd_8359842 : Nat := 4983230072969 + 3 ^ 40 * 8359842 * 2
def baseEnd_8359842 : Nat := 4292617141643986313428793

theorem tailTrace_8359842 : CollatzResearch.WordTrace tailWord_8359842 prefixEnd_8359842 4292617141643986313428793 := by
  unfold tailWord_8359842
  simp only [CollatzResearch.WordTrace]
  refine ⟨76227121744931914047484445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203272324653151770793291853 76227121744931914047484445)
  ·
    refine ⟨28585170654349467767806667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76227121744931914047484445 28585170654349467767806667)
    ·
      refine ⟨42877755981524201651710001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28585170654349467767806667 42877755981524201651710001)
      ·
        refine ⟨32158316986143151238782501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42877755981524201651710001 32158316986143151238782501)
        ·
          refine ⟨6029684434901840857271719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32158316986143151238782501 6029684434901840857271719)
          ·
            refine ⟨9044526652352761285907579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029684434901840857271719 9044526652352761285907579)
            ·
              refine ⟨13566789978529141928861369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9044526652352761285907579 13566789978529141928861369)
              ·
                refine ⟨10175092483896856446646027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13566789978529141928861369 10175092483896856446646027)
                ·
                  refine ⟨15262638725845284669969041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10175092483896856446646027 15262638725845284669969041)
                  ·
                    refine ⟨11446979044383963502476781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15262638725845284669969041 11446979044383963502476781)
                    ·
                      refine ⟨4292617141643986313428793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11446979044383963502476781 4292617141643986313428793)
                      ·
                        rfl

theorem cell23_8359842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_8359842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359842 prefixEnd_8359842 := by exact prefixLift 8359842
  have htrace : WordTrace (prefixWord ++ tailWord_8359842) baseStart_8359842 baseEnd_8359842 := by
    simpa [prefixWord, tailWord_8359842, baseEnd_8359842] using wordTrace_append hprefix tailTrace_8359842
  have hstable : (prefixWord ++ tailWord_8359842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359842).length < 2 ^ (prefixWord ++ tailWord_8359842).sum := by decide
  have hdescent : baseEnd_8359842 < baseStart_8359842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359864 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_8359864 : Nat := 118140960795 + 8359864 * 2 ^ 59
def prefixEnd_8359864 : Nat := 4983230072969 + 3 ^ 40 * 8359864 * 2
def baseEnd_8359864 : Nat := 4292628438218385227353691

theorem tailTrace_8359864 : CollatzResearch.WordTrace tailWord_8359864 prefixEnd_8359864 4292628438218385227353691 := by
  unfold tailWord_8359864
  simp only [CollatzResearch.WordTrace]
  refine ⟨152454644692823976973619323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203272859590431969298159097 152454644692823976973619323)
  ·
    refine ⟨228681967039235965460428985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152454644692823976973619323 228681967039235965460428985)
    ·
      refine ⟨171511475279426974095321739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228681967039235965460428985 171511475279426974095321739)
      ·
        refine ⟨257267212919140461142982609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171511475279426974095321739 257267212919140461142982609)
        ·
          refine ⟨192950409689355345857236957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257267212919140461142982609 192950409689355345857236957)
          ·
            refine ⟨72356403633508254696463859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192950409689355345857236957 72356403633508254696463859)
            ·
              refine ⟨108534605450262382044695789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72356403633508254696463859 108534605450262382044695789)
              ·
                refine ⟨40700477043848393266760921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108534605450262382044695789 40700477043848393266760921)
                ·
                  refine ⟨30525357782886294950070691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40700477043848393266760921 30525357782886294950070691)
                  ·
                    refine ⟨45788036674329442425106037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30525357782886294950070691 45788036674329442425106037)
                    ·
                      refine ⟨4292628438218385227353691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45788036674329442425106037 4292628438218385227353691)
                      ·
                        rfl

theorem cell23_8359864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_8359864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359864 prefixEnd_8359864 := by exact prefixLift 8359864
  have htrace : WordTrace (prefixWord ++ tailWord_8359864) baseStart_8359864 baseEnd_8359864 := by
    simpa [prefixWord, tailWord_8359864, baseEnd_8359864] using wordTrace_append hprefix tailTrace_8359864
  have hstable : (prefixWord ++ tailWord_8359864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359864).length < 2 ^ (prefixWord ++ tailWord_8359864).sum := by decide
  have hdescent : baseEnd_8359864 < baseStart_8359864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359865 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 1, 3, 2]
def baseStart_8359865 : Nat := 118140960795 + 8359865 * 2 ^ 59
def prefixEnd_8359865 : Nat := 4983230072969 + 3 ^ 40 * 8359865 * 2
def baseEnd_8359865 : Nat := 4292628951699039723441187

theorem tailTrace_8359865 : CollatzResearch.WordTrace tailWord_8359865 prefixEnd_8359865 4292628951699039723441187 := by
  unfold tailWord_8359865
  simp only [CollatzResearch.WordTrace]
  refine ⟨304909325858644331118025049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203272883905762887412016699 304909325858644331118025049)
  ·
    refine ⟨228681994393983248338518787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304909325858644331118025049 228681994393983248338518787)
    ·
      refine ⟨343022991590974872507778181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228681994393983248338518787 343022991590974872507778181)
      ·
        refine ⟨64316810923307788595208409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343022991590974872507778181 64316810923307788595208409)
        ·
          refine ⟨48237608192480841446406307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64316810923307788595208409 48237608192480841446406307)
          ·
            refine ⟨72356412288721262169609461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48237608192480841446406307 72356412288721262169609461)
            ·
              refine ⟨6783413652067618328400887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72356412288721262169609461 6783413652067618328400887)
              ·
                refine ⟨10175120478101427492601331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783413652067618328400887 10175120478101427492601331)
                ·
                  refine ⟨15262680717152141238901997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10175120478101427492601331 15262680717152141238901997)
                  ·
                    refine ⟨5723505268932052964588249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15262680717152141238901997 5723505268932052964588249)
                    ·
                      refine ⟨4292628951699039723441187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723505268932052964588249 4292628951699039723441187)
                      ·
                        rfl

theorem cell23_8359865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_8359865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359865 prefixEnd_8359865 := by exact prefixLift 8359865
  have htrace : WordTrace (prefixWord ++ tailWord_8359865) baseStart_8359865 baseEnd_8359865 := by
    simpa [prefixWord, tailWord_8359865, baseEnd_8359865] using wordTrace_append hprefix tailTrace_8359865
  have hstable : (prefixWord ++ tailWord_8359865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359865).length < 2 ^ (prefixWord ++ tailWord_8359865).sum := by decide
  have hdescent : baseEnd_8359865 < baseStart_8359865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359918 : List Nat := [4, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_8359918 : Nat := 118140960795 + 8359918 * 2 ^ 59
def prefixEnd_8359918 : Nat := 4983230072969 + 3 ^ 40 * 8359918 * 2
def baseEnd_8359918 : Nat := 476961796241525335119827

theorem tailTrace_8359918 : CollatzResearch.WordTrace tailWord_8359918 prefixEnd_8359918 476961796241525335119827 := by
  unfold tailWord_8359918
  simp only [CollatzResearch.WordTrace]
  refine ⟨38113907365931540146213051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203274172618301547446469605 38113907365931540146213051)
  ·
    refine ⟨57170861048897310219319577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38113907365931540146213051 57170861048897310219319577)
    ·
      refine ⟨42878145786672982664489683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57170861048897310219319577 42878145786672982664489683)
      ·
        refine ⟨64317218680009473996734525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42878145786672982664489683 64317218680009473996734525)
        ·
          refine ⟨24118957005003552748775447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64317218680009473996734525 24118957005003552748775447)
          ·
            refine ⟨36178435507505329123163171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24118957005003552748775447 36178435507505329123163171)
            ·
              refine ⟨54267653261257993684744757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36178435507505329123163171 54267653261257993684744757)
              ·
                refine ⟨5087592493242936907944821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54267653261257993684744757 5087592493242936907944821)
                ·
                  refine ⟨476961796241525335119827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5087592493242936907944821 476961796241525335119827)
                  ·
                    rfl

theorem cell23_8359918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_8359918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359918 prefixEnd_8359918 := by exact prefixLift 8359918
  have htrace : WordTrace (prefixWord ++ tailWord_8359918) baseStart_8359918 baseEnd_8359918 := by
    simpa [prefixWord, tailWord_8359918, baseEnd_8359918] using wordTrace_append hprefix tailTrace_8359918
  have hstable : (prefixWord ++ tailWord_8359918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359918).length < 2 ^ (prefixWord ++ tailWord_8359918).sum := by decide
  have hdescent : baseEnd_8359918 < baseStart_8359918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8359971 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 3]
def baseStart_8359971 : Nat := 118140960795 + 8359971 * 2 ^ 59
def prefixEnd_8359971 : Nat := 4983230072969 + 3 ^ 40 * 8359971 * 2
def baseEnd_8359971 : Nat := 4292683380648416308715699

theorem tailTrace_8359971 : CollatzResearch.WordTrace tailWord_8359971 prefixEnd_8359971 4292683380648416308715699 := by
  unfold tailWord_8359971
  simp only [CollatzResearch.WordTrace]
  refine ⟨304913191996260311221383767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203275461330840207480922511 304913191996260311221383767)
  ·
    refine ⟨457369787994390466832075651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304913191996260311221383767 457369787994390466832075651)
    ·
      refine ⟨686054681991585700248113477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457369787994390466832075651 686054681991585700248113477)
      ·
        refine ⟨128635252873422318796521277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 686054681991585700248113477 128635252873422318796521277)
        ·
          refine ⟨48238219827533369548695479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128635252873422318796521277 48238219827533369548695479)
          ·
            refine ⟨72357329741300054323043219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48238219827533369548695479 72357329741300054323043219)
            ·
              refine ⟨108535994611950081484564829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72357329741300054323043219 108535994611950081484564829)
              ·
                refine ⟨40700997979481280556711811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108535994611950081484564829 40700997979481280556711811)
                ·
                  refine ⟨61051496969221920835067717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40700997979481280556711811 61051496969221920835067717)
                  ·
                    refine ⟨11447155681729110156575197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61051496969221920835067717 11447155681729110156575197)
                    ·
                      refine ⟨4292683380648416308715699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11447155681729110156575197 4292683380648416308715699)
                      ·
                        rfl

theorem cell23_8359971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_8359971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8359971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8359971 prefixEnd_8359971 := by exact prefixLift 8359971
  have htrace : WordTrace (prefixWord ++ tailWord_8359971) baseStart_8359971 baseEnd_8359971 := by
    simpa [prefixWord, tailWord_8359971, baseEnd_8359971] using wordTrace_append hprefix tailTrace_8359971
  have hstable : (prefixWord ++ tailWord_8359971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8359971).length < 2 ^ (prefixWord ++ tailWord_8359971).sum := by decide
  have hdescent : baseEnd_8359971 < baseStart_8359971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8359971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360022 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_8360022 : Nat := 118140960795 + 8360022 * 2 ^ 59
def prefixEnd_8360022 : Nat := 4983230072969 + 3 ^ 40 * 8360022 * 2
def baseEnd_8360022 : Nat := 4292709568161795609177965

theorem tailTrace_8360022 : CollatzResearch.WordTrace tailWord_8360022 prefixEnd_8360022 4292709568161795609177965 := by
  unfold tailWord_8360022
  simp only [CollatzResearch.WordTrace]
  refine ⟨19057190757442221683218145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203276701412717031287660213 19057190757442221683218145)
  ·
    refine ⟨14292893068081666262413609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19057190757442221683218145 14292893068081666262413609)
    ·
      refine ⟨10719669801061249696810207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14292893068081666262413609 10719669801061249696810207)
      ·
        refine ⟨16079504701591874545215311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10719669801061249696810207 16079504701591874545215311)
        ·
          refine ⟨24119257052387811817822967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16079504701591874545215311 24119257052387811817822967)
          ·
            refine ⟨36178885578581717726734451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24119257052387811817822967 36178885578581717726734451)
            ·
              refine ⟨54268328367872576590101677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36178885578581717726734451 54268328367872576590101677)
              ·
                refine ⟨20350623137952216221288129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54268328367872576590101677 20350623137952216221288129)
                ·
                  refine ⟨15262967353464162165966097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20350623137952216221288129 15262967353464162165966097)
                  ·
                    refine ⟨11447225515098121624474573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15262967353464162165966097 11447225515098121624474573)
                    ·
                      refine ⟨4292709568161795609177965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11447225515098121624474573 4292709568161795609177965)
                      ·
                        rfl

theorem cell23_8360022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_8360022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360022 prefixEnd_8360022 := by exact prefixLift 8360022
  have htrace : WordTrace (prefixWord ++ tailWord_8360022) baseStart_8360022 baseEnd_8360022 := by
    simpa [prefixWord, tailWord_8360022, baseEnd_8360022] using wordTrace_append hprefix tailTrace_8360022
  have hstable : (prefixWord ++ tailWord_8360022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360022).length < 2 ^ (prefixWord ++ tailWord_8360022).sum := by decide
  have hdescent : baseEnd_8360022 < baseStart_8360022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360045 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_8360045 : Nat := 118140960795 + 8360045 * 2 ^ 59
def prefixEnd_8360045 : Nat := 4983230072969 + 3 ^ 40 * 8360045 * 2
def baseEnd_8360045 : Nat := 4292721378216849019190359

theorem tailTrace_8360045 : CollatzResearch.WordTrace tailWord_8360045 prefixEnd_8360045 4292721378216849019190359 := by
  unfold tailWord_8360045
  simp only [CollatzResearch.WordTrace]
  refine ⟨304915890997992221859577589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203277260665328147906385059 304915890997992221859577589)
  ·
    refine ⟨28585864781061770799335399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304915890997992221859577589 28585864781061770799335399)
    ·
      refine ⟨42878797171592656199003099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28585864781061770799335399 42878797171592656199003099)
      ·
        refine ⟨64318195757388984298504649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42878797171592656199003099 64318195757388984298504649)
        ·
          refine ⟨48238646818041738223878487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64318195757388984298504649 48238646818041738223878487)
          ·
            refine ⟨72357970227062607335817731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48238646818041738223878487 72357970227062607335817731)
            ·
              refine ⟨108536955340593911003726597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72357970227062607335817731 108536955340593911003726597)
              ·
                refine ⟨20350679126361358313198737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108536955340593911003726597 20350679126361358313198737)
                ·
                  refine ⟨15263009344771018734899053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20350679126361358313198737 15263009344771018734899053)
                  ·
                    refine ⟨5723628504289132025587145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15263009344771018734899053 5723628504289132025587145)
                    ·
                      refine ⟨4292721378216849019190359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723628504289132025587145 4292721378216849019190359)
                      ·
                        rfl

theorem cell23_8360045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_8360045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360045 prefixEnd_8360045 := by exact prefixLift 8360045
  have htrace : WordTrace (prefixWord ++ tailWord_8360045) baseStart_8360045 baseEnd_8360045 := by
    simpa [prefixWord, tailWord_8360045, baseEnd_8360045] using wordTrace_append hprefix tailTrace_8360045
  have hstable : (prefixWord ++ tailWord_8360045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360045).length < 2 ^ (prefixWord ++ tailWord_8360045).sum := by decide
  have hdescent : baseEnd_8360045 < baseStart_8360045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360068 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_8360068 : Nat := 118140960795 + 8360068 * 2 ^ 59
def prefixEnd_8360068 : Nat := 4983230072969 + 3 ^ 40 * 8360068 * 2
def baseEnd_8360068 : Nat := 1430911062757300809734251

theorem tailTrace_8360068 : CollatzResearch.WordTrace tailWord_8360068 prefixEnd_8360068 1430911062757300809734251 := by
  unfold tailWord_8360068
  simp only [CollatzResearch.WordTrace]
  refine ⟨152458364938454448393832429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203277819917939264525109905 152458364938454448393832429)
  ·
    refine ⟨57171886851920418147687161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152458364938454448393832429 57171886851920418147687161)
    ·
      refine ⟨42878915138940313610765371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57171886851920418147687161 42878915138940313610765371)
      ·
        refine ⟨64318372708410470416148057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42878915138940313610765371 64318372708410470416148057)
        ·
          refine ⟨48238779531307852812111043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64318372708410470416148057 48238779531307852812111043)
          ·
            refine ⟨72358169296961779218166565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48238779531307852812111043 72358169296961779218166565)
            ·
              refine ⟨13567156743180333603406231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72358169296961779218166565 13567156743180333603406231)
              ·
                refine ⟨20350735114770500405109347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13567156743180333603406231 20350735114770500405109347)
                ·
                  refine ⟨30526102672155750607664021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20350735114770500405109347 30526102672155750607664021)
                  ·
                    refine ⟨1430911062757300809734251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30526102672155750607664021 1430911062757300809734251)
                    ·
                      rfl

theorem cell23_8360068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_8360068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360068 prefixEnd_8360068 := by exact prefixLift 8360068
  have htrace : WordTrace (prefixWord ++ tailWord_8360068) baseStart_8360068 baseEnd_8360068 := by
    simpa [prefixWord, tailWord_8360068, baseEnd_8360068] using wordTrace_append hprefix tailTrace_8360068
  have hstable : (prefixWord ++ tailWord_8360068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360068).length < 2 ^ (prefixWord ++ tailWord_8360068).sum := by decide
  have hdescent : baseEnd_8360068 < baseStart_8360068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360071 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_8360071 : Nat := 118140960795 + 8360071 * 2 ^ 59
def prefixEnd_8360071 : Nat := 4983230072969 + 3 ^ 40 * 8360071 * 2
def baseEnd_8360071 : Nat := 4292734728713865917465239

theorem tailTrace_8360071 : CollatzResearch.WordTrace tailWord_8360071 prefixEnd_8360071 4292734728713865917465239 := by
  unfold tailWord_8360071
  simp only [CollatzResearch.WordTrace]
  refine ⟨304916839295898028300024067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203277892863932018866682711 304916839295898028300024067)
  ·
    refine ⟨457375258943847042450036101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304916839295898028300024067 457375258943847042450036101)
    ·
      refine ⟨85757861051971320459381769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457375258943847042450036101 85757861051971320459381769)
      ·
        refine ⟨64318395788978490344536327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85757861051971320459381769 64318395788978490344536327)
        ·
          refine ⟨96477593683467735516804491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64318395788978490344536327 96477593683467735516804491)
          ·
            refine ⟨144716390525201603275206737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96477593683467735516804491 144716390525201603275206737)
            ·
              refine ⟨108537292893901202456405053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144716390525201603275206737 108537292893901202456405053)
              ·
                refine ⟨40701484835212950921151895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108537292893901202456405053 40701484835212950921151895)
                ·
                  refine ⟨61052227252819426381727843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40701484835212950921151895 61052227252819426381727843)
                  ·
                    refine ⟨91578340879229139572591765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61052227252819426381727843 91578340879229139572591765)
                    ·
                      refine ⟨4292734728713865917465239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91578340879229139572591765 4292734728713865917465239)
                      ·
                        rfl

theorem cell23_8360071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_8360071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360071 prefixEnd_8360071 := by exact prefixLift 8360071
  have htrace : WordTrace (prefixWord ++ tailWord_8360071) baseStart_8360071 baseEnd_8360071 := by
    simpa [prefixWord, tailWord_8360071, baseEnd_8360071] using wordTrace_append hprefix tailTrace_8360071
  have hstable : (prefixWord ++ tailWord_8360071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360071).length < 2 ^ (prefixWord ++ tailWord_8360071).sum := by decide
  have hdescent : baseEnd_8360071 < baseStart_8360071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360098 : List Nat := [3, 3, 1, 3, 1, 2, 10]
def baseStart_8360098 : Nat := 118140960795 + 8360098 * 2 ^ 59
def prefixEnd_8360098 : Nat := 4983230072969 + 3 ^ 40 * 8360098 * 2
def baseEnd_8360098 : Nat := 52996896206068361874415

theorem tailTrace_8360098 : CollatzResearch.WordTrace tailWord_8360098 prefixEnd_8360098 52996896206068361874415 := by
  unfold tailWord_8360098
  simp only [CollatzResearch.WordTrace]
  refine ⟨76229456016700052977814237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203278549377866807940837965 76229456016700052977814237)
  ·
    refine ⟨28586046006262519866680339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76229456016700052977814237 28586046006262519866680339)
    ·
      refine ⟨42879069009393779800020509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28586046006262519866680339 42879069009393779800020509)
      ·
        refine ⟨16079650878522667425007691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42879069009393779800020509 16079650878522667425007691)
        ·
          refine ⟨24119476317784001137511537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16079650878522667425007691 24119476317784001137511537)
          ·
            refine ⟨18089607238338000853133653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24119476317784001137511537 18089607238338000853133653)
            ·
              refine ⟨52996896206068361874415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18089607238338000853133653 52996896206068361874415)
              ·
                rfl

theorem cell23_8360098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 10].length) (baseStart_8360098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360098 prefixEnd_8360098 := by exact prefixLift 8360098
  have htrace : WordTrace (prefixWord ++ tailWord_8360098) baseStart_8360098 baseEnd_8360098 := by
    simpa [prefixWord, tailWord_8360098, baseEnd_8360098] using wordTrace_append hprefix tailTrace_8360098
  have hstable : (prefixWord ++ tailWord_8360098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360098).length < 2 ^ (prefixWord ++ tailWord_8360098).sum := by decide
  have hdescent : baseEnd_8360098 < baseStart_8360098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360109 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_8360109 : Nat := 118140960795 + 8360109 * 2 ^ 59
def prefixEnd_8360109 : Nat := 4983230072969 + 3 ^ 40 * 8360109 * 2
def baseEnd_8360109 : Nat := 4292754240978736768790065

theorem tailTrace_8360109 : CollatzResearch.WordTrace tailWord_8360109 prefixEnd_8360109 4292754240978736768790065 := by
  unfold tailWord_8360109
  simp only [CollatzResearch.WordTrace]
  refine ⟨304918225269760360789907381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203278816846506907193271587 304918225269760360789907381)
  ·
    refine ⟨28586083619040033824053817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304918225269760360789907381 28586083619040033824053817)
    ·
      refine ⟨21439562714280025368040363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28586083619040033824053817 21439562714280025368040363)
      ·
        refine ⟨32159344071420038052060545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21439562714280025368040363 32159344071420038052060545)
        ·
          refine ⟨24119508053565028539045409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32159344071420038052060545 24119508053565028539045409)
          ·
            refine ⟨18089631040173771404284057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24119508053565028539045409 18089631040173771404284057)
            ·
              refine ⟨13567223280130328553213043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18089631040173771404284057 13567223280130328553213043)
              ·
                refine ⟨20350834920195492829819565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13567223280130328553213043 20350834920195492829819565)
                ·
                  refine ⟨7631563095073309811182337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20350834920195492829819565 7631563095073309811182337)
                  ·
                    refine ⟨5723672321304982358386753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7631563095073309811182337 5723672321304982358386753)
                    ·
                      refine ⟨4292754240978736768790065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723672321304982358386753 4292754240978736768790065)
                      ·
                        rfl

theorem cell23_8360109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_8360109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360109 prefixEnd_8360109 := by exact prefixLift 8360109
  have htrace : WordTrace (prefixWord ++ tailWord_8360109) baseStart_8360109 baseEnd_8360109 := by
    simpa [prefixWord, tailWord_8360109, baseEnd_8360109] using wordTrace_append hprefix tailTrace_8360109
  have hstable : (prefixWord ++ tailWord_8360109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360109).length < 2 ^ (prefixWord ++ tailWord_8360109).sum := by decide
  have hdescent : baseEnd_8360109 < baseStart_8360109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360129 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_8360129 : Nat := 118140960795 + 8360129 * 2 ^ 59
def prefixEnd_8360129 : Nat := 4983230072969 + 3 ^ 40 * 8360129 * 2
def baseEnd_8360129 : Nat := 4292764510591826690539973

theorem tailTrace_8360129 : CollatzResearch.WordTrace tailWord_8360129 prefixEnd_8360129 4292764510591826690539973 := by
  unfold tailWord_8360129
  simp only [CollatzResearch.WordTrace]
  refine ⟨304918954729687904205635441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203279303153125269470423627 304918954729687904205635441)
  ·
    refine ⟨228689216047265928154226581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304918954729687904205635441 228689216047265928154226581)
    ·
      refine ⟨10719807002215590382229371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228689216047265928154226581 10719807002215590382229371)
      ·
        refine ⟨16079710503323385573344057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10719807002215590382229371 16079710503323385573344057)
        ·
          refine ⟨12059782877492539180008043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16079710503323385573344057 12059782877492539180008043)
          ·
            refine ⟨18089674316238808770012065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12059782877492539180008043 18089674316238808770012065)
            ·
              refine ⟨13567255737179106577509049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18089674316238808770012065 13567255737179106577509049)
              ·
                refine ⟨10175441802884329933131787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13567255737179106577509049 10175441802884329933131787)
                ·
                  refine ⟨15263162704326494899697681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10175441802884329933131787 15263162704326494899697681)
                  ·
                    refine ⟨11447372028244871174773261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15263162704326494899697681 11447372028244871174773261)
                    ·
                      refine ⟨4292764510591826690539973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11447372028244871174773261 4292764510591826690539973)
                      ·
                        rfl

theorem cell23_8360129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_8360129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360129 prefixEnd_8360129 := by exact prefixLift 8360129
  have htrace : WordTrace (prefixWord ++ tailWord_8360129) baseStart_8360129 baseEnd_8360129 := by
    simpa [prefixWord, tailWord_8360129, baseEnd_8360129] using wordTrace_append hprefix tailTrace_8360129
  have hstable : (prefixWord ++ tailWord_8360129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360129).length < 2 ^ (prefixWord ++ tailWord_8360129).sum := by decide
  have hdescent : baseEnd_8360129 < baseStart_8360129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360131 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 4]
def baseStart_8360131 : Nat := 118140960795 + 8360131 * 2 ^ 59
def prefixEnd_8360131 : Nat := 4983230072969 + 3 ^ 40 * 8360131 * 2
def baseEnd_8360131 : Nat := 4292765537553135682714963

theorem tailTrace_8360131 : CollatzResearch.WordTrace tailWord_8360131 prefixEnd_8360131 4292765537553135682714963 := by
  unfold tailWord_8360131
  simp only [CollatzResearch.WordTrace]
  refine ⟨304919027675680658547208247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203279351783787105698138831 304919027675680658547208247)
  ·
    refine ⟨457378541513520987820812371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304919027675680658547208247 457378541513520987820812371)
    ·
      refine ⟨686067812270281481731218557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457378541513520987820812371 686067812270281481731218557)
      ·
        refine ⟨257275429601355555649206959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686067812270281481731218557 257275429601355555649206959)
        ·
          refine ⟨385913144402033333473810439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257275429601355555649206959 385913144402033333473810439)
          ·
            refine ⟨578869716603050000210715659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385913144402033333473810439 578869716603050000210715659)
            ·
              refine ⟨868304574904575000316073489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578869716603050000210715659 868304574904575000316073489)
              ·
                refine ⟨651228431178431250237055117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868304574904575000316073489 651228431178431250237055117)
                ·
                  refine ⟨244210661691911718838895669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651228431178431250237055117 244210661691911718838895669)
                  ·
                    refine ⟨22894749533616723641146469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244210661691911718838895669 22894749533616723641146469)
                    ·
                      refine ⟨4292765537553135682714963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22894749533616723641146469 4292765537553135682714963)
                      ·
                        rfl

theorem cell23_8360131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_8360131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360131 prefixEnd_8360131 := by exact prefixLift 8360131
  have htrace : WordTrace (prefixWord ++ tailWord_8360131) baseStart_8360131 baseEnd_8360131 := by
    simpa [prefixWord, tailWord_8360131, baseEnd_8360131] using wordTrace_append hprefix tailTrace_8360131
  have hstable : (prefixWord ++ tailWord_8360131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360131).length < 2 ^ (prefixWord ++ tailWord_8360131).sum := by decide
  have hdescent : baseEnd_8360131 < baseStart_8360131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360152 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 1, 3, 2]
def baseStart_8360152 : Nat := 118140960795 + 8360152 * 2 ^ 59
def prefixEnd_8360152 : Nat := 4983230072969 + 3 ^ 40 * 8360152 * 2
def baseEnd_8360152 : Nat := 4292776320646880100552367

theorem tailTrace_8360152 : CollatzResearch.WordTrace tailWord_8360152 prefixEnd_8360152 4292776320646880100552367 := by
  unfold tailWord_8360152
  simp only [CollatzResearch.WordTrace]
  refine ⟨152459896804302289566861355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203279862405736386089148473 152459896804302289566861355)
  ·
    refine ⟨228689845206453434350292033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152459896804302289566861355 228689845206453434350292033)
    ·
      refine ⟨171517383904840075762719025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228689845206453434350292033 171517383904840075762719025)
      ·
        refine ⟨128638037928630056822039269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171517383904840075762719025 128638037928630056822039269)
        ·
          refine ⟨24119632111618135654132363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128638037928630056822039269 24119632111618135654132363)
          ·
            refine ⟨36179448167427203481198545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24119632111618135654132363 36179448167427203481198545)
            ·
              refine ⟨27134586125570402610898909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36179448167427203481198545 27134586125570402610898909)
              ·
                refine ⟨10175469797088900979087091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27134586125570402610898909 10175469797088900979087091)
                ·
                  refine ⟨15263204695633351468630637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10175469797088900979087091 15263204695633351468630637)
                  ·
                    refine ⟨5723701760862506800736489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15263204695633351468630637 5723701760862506800736489)
                    ·
                      refine ⟨4292776320646880100552367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723701760862506800736489 4292776320646880100552367)
                      ·
                        rfl

theorem cell23_8360152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_8360152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360152 prefixEnd_8360152 := by exact prefixLift 8360152
  have htrace : WordTrace (prefixWord ++ tailWord_8360152) baseStart_8360152 baseEnd_8360152 := by
    simpa [prefixWord, tailWord_8360152, baseEnd_8360152] using wordTrace_append hprefix tailTrace_8360152
  have hstable : (prefixWord ++ tailWord_8360152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360152).length < 2 ^ (prefixWord ++ tailWord_8360152).sum := by decide
  have hdescent : baseEnd_8360152 < baseStart_8360152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360199 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_8360199 : Nat := 118140960795 + 8360199 * 2 ^ 59
def prefixEnd_8360199 : Nat := 4983230072969 + 3 ^ 40 * 8360199 * 2
def baseEnd_8360199 : Nat := 4292800454237641416664651

theorem tailTrace_8360199 : CollatzResearch.WordTrace tailWord_8360199 prefixEnd_8360199 4292800454237641416664651 := by
  unfold tailWord_8360199
  simp only [CollatzResearch.WordTrace]
  refine ⟨304921507839434306160683651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203281005226289537440455767 304921507839434306160683651)
  ·
    refine ⟨457382261759151459241025477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304921507839434306160683651 457382261759151459241025477)
    ·
      refine ⟨85759174079840898607692277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457382261759151459241025477 85759174079840898607692277)
      ·
        refine ⟨8039922569985084244471151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85759174079840898607692277 8039922569985084244471151)
        ·
          refine ⟨12059883854977626366706727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8039922569985084244471151 12059883854977626366706727)
          ·
            refine ⟨18089825782466439550060091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12059883854977626366706727 18089825782466439550060091)
            ·
              refine ⟨27134738673699659325090137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18089825782466439550060091 27134738673699659325090137)
              ·
                refine ⟨20351054005274744493817603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27134738673699659325090137 20351054005274744493817603)
                ·
                  refine ⟨30526581007912116740726405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20351054005274744493817603 30526581007912116740726405)
                  ·
                    refine ⟨5723733938983521888886201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30526581007912116740726405 5723733938983521888886201)
                    ·
                      refine ⟨4292800454237641416664651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723733938983521888886201 4292800454237641416664651)
                      ·
                        rfl

theorem cell23_8360199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_8360199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360199 prefixEnd_8360199 := by exact prefixLift 8360199
  have htrace : WordTrace (prefixWord ++ tailWord_8360199) baseStart_8360199 baseEnd_8360199 := by
    simpa [prefixWord, tailWord_8360199, baseEnd_8360199] using wordTrace_append hprefix tailTrace_8360199
  have hstable : (prefixWord ++ tailWord_8360199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360199).length < 2 ^ (prefixWord ++ tailWord_8360199).sum := by decide
  have hdescent : baseEnd_8360199 < baseStart_8360199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360225 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_8360225 : Nat := 118140960795 + 8360225 * 2 ^ 59
def prefixEnd_8360225 : Nat := 4983230072969 + 3 ^ 40 * 8360225 * 2
def baseEnd_8360225 : Nat := 4292813804734658314939531

theorem tailTrace_8360225 : CollatzResearch.WordTrace tailWord_8360225 prefixEnd_8360225 4292813804734658314939531 := by
  unfold tailWord_8360225
  simp only [CollatzResearch.WordTrace]
  refine ⟨304922456137340112601130129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203281637424893408400753419 304922456137340112601130129)
  ·
    refine ⟨228691842103005084450847597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304922456137340112601130129 228691842103005084450847597)
    ·
      refine ⟨85759440788626906669067849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228691842103005084450847597 85759440788626906669067849)
      ·
        refine ⟨64319580591470180001800887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85759440788626906669067849 64319580591470180001800887)
        ·
          refine ⟨96479370887205270002701331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64319580591470180001800887 96479370887205270002701331)
          ·
            refine ⟨144719056330807905004051997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96479370887205270002701331 144719056330807905004051997)
            ·
              refine ⟨54269646124052964376519499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144719056330807905004051997 54269646124052964376519499)
              ·
                refine ⟨81404469186079446564779249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54269646124052964376519499 81404469186079446564779249)
                ·
                  refine ⟨61053351889559584923584437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81404469186079446564779249 61053351889559584923584437)
                  ·
                    refine ⟨5723751739646211086586041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61053351889559584923584437 5723751739646211086586041)
                    ·
                      refine ⟨4292813804734658314939531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723751739646211086586041 4292813804734658314939531)
                      ·
                        rfl

theorem cell23_8360225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_8360225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360225 prefixEnd_8360225 := by exact prefixLift 8360225
  have htrace : WordTrace (prefixWord ++ tailWord_8360225) baseStart_8360225 baseEnd_8360225 := by
    simpa [prefixWord, tailWord_8360225, baseEnd_8360225] using wordTrace_append hprefix tailTrace_8360225
  have hstable : (prefixWord ++ tailWord_8360225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360225).length < 2 ^ (prefixWord ++ tailWord_8360225).sum := by decide
  have hdescent : baseEnd_8360225 < baseStart_8360225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360232 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_8360232 : Nat := 118140960795 + 8360232 * 2 ^ 59
def prefixEnd_8360232 : Nat := 4983230072969 + 3 ^ 40 * 8360232 * 2
def baseEnd_8360232 : Nat := 4292817399099239787551999

theorem tailTrace_8360232 : CollatzResearch.WordTrace tailWord_8360232 prefixEnd_8360232 4292817399099239787551999 := by
  unfold tailWord_8360232
  simp only [CollatzResearch.WordTrace]
  refine ⟨152461355724157376398317475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203281807632209835197756633 152461355724157376398317475)
  ·
    refine ⟨228692033586236064597476213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152461355724157376398317475 228692033586236064597476213)
    ·
      refine ⟨21439878148709631056013395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228692033586236064597476213 21439878148709631056013395)
      ·
        refine ⟨32159817223064446584020093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21439878148709631056013395 32159817223064446584020093)
        ·
          refine ⟨12059931458649167469007535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32159817223064446584020093 12059931458649167469007535)
          ·
            refine ⟨18089897187973751203511303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12059931458649167469007535 18089897187973751203511303)
            ·
              refine ⟨27134845781960626805266955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18089897187973751203511303 27134845781960626805266955)
              ·
                refine ⟨40702268672940940207900433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27134845781960626805266955 40702268672940940207900433)
                ·
                  refine ⟨30526701504705705155925325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40702268672940940207900433 30526701504705705155925325)
                  ·
                    refine ⟨11447513064264639433471997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30526701504705705155925325 11447513064264639433471997)
                    ·
                      refine ⟨4292817399099239787551999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11447513064264639433471997 4292817399099239787551999)
                      ·
                        rfl

theorem cell23_8360232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_8360232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360232 prefixEnd_8360232 := by exact prefixLift 8360232
  have htrace : WordTrace (prefixWord ++ tailWord_8360232) baseStart_8360232 baseEnd_8360232 := by
    simpa [prefixWord, tailWord_8360232, baseEnd_8360232] using wordTrace_append hprefix tailTrace_8360232
  have hstable : (prefixWord ++ tailWord_8360232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360232).length < 2 ^ (prefixWord ++ tailWord_8360232).sum := by decide
  have hdescent : baseEnd_8360232 < baseStart_8360232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360255 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 1, 6, 2]
def baseStart_8360255 : Nat := 118140960795 + 8360255 * 2 ^ 59
def prefixEnd_8360255 : Nat := 4983230072969 + 3 ^ 40 * 8360255 * 2
def baseEnd_8360255 : Nat := 4292829209154293197564393

theorem tailTrace_8360255 : CollatzResearch.WordTrace tailWord_8360255 prefixEnd_8360255 4292829209154293197564393 := by
  unfold tailWord_8360255
  simp only [CollatzResearch.WordTrace]
  refine ⟨304923550327231427724722219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203282366884820951816481479 304923550327231427724722219)
  ·
    refine ⟨457385325490847141587083329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304923550327231427724722219 457385325490847141587083329)
    ·
      refine ⟨343038994118135356190312497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457385325490847141587083329 343038994118135356190312497)
      ·
        refine ⟨257279245588601517142734373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343038994118135356190312497 257279245588601517142734373)
        ·
          refine ⟨48239858547862784464262695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257279245588601517142734373 48239858547862784464262695)
          ·
            refine ⟨72359787821794176696394043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48239858547862784464262695 72359787821794176696394043)
            ·
              refine ⟨108539681732691265044591065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72359787821794176696394043 108539681732691265044591065)
              ·
                refine ⟨81404761299518448783443299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108539681732691265044591065 81404761299518448783443299)
                ·
                  refine ⟨122107141949277673175164949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81404761299518448783443299 122107141949277673175164949)
                  ·
                    refine ⟨5723772278872390930085857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122107141949277673175164949 5723772278872390930085857)
                    ·
                      refine ⟨4292829209154293197564393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723772278872390930085857 4292829209154293197564393)
                      ·
                        rfl

theorem cell23_8360255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_8360255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360255 prefixEnd_8360255 := by exact prefixLift 8360255
  have htrace : WordTrace (prefixWord ++ tailWord_8360255) baseStart_8360255 baseEnd_8360255 := by
    simpa [prefixWord, tailWord_8360255, baseEnd_8360255] using wordTrace_append hprefix tailTrace_8360255
  have hstable : (prefixWord ++ tailWord_8360255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360255).length < 2 ^ (prefixWord ++ tailWord_8360255).sum := by decide
  have hdescent : baseEnd_8360255 < baseStart_8360255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360268 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_8360268 : Nat := 118140960795 + 8360268 * 2 ^ 59
def prefixEnd_8360268 : Nat := 4983230072969 + 3 ^ 40 * 8360268 * 2
def baseEnd_8360268 : Nat := 4292835884402801646701833

theorem tailTrace_8360268 : CollatzResearch.WordTrace tailWord_8360268 prefixEnd_8360268 4292835884402801646701833 := by
  unfold tailWord_8360268
  simp only [CollatzResearch.WordTrace]
  refine ⟨152462012238092165472472729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203282682984122887296630305 152462012238092165472472729)
  ·
    refine ⟨114346509178569124104354547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152462012238092165472472729 114346509178569124104354547)
    ·
      refine ⟨171519763767853686156531821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114346509178569124104354547 171519763767853686156531821)
      ·
        refine ⟨64319911412945132308699433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171519763767853686156531821 64319911412945132308699433)
        ·
          refine ⟨48239933559708849231524575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64319911412945132308699433 48239933559708849231524575)
          ·
            refine ⟨72359900339563273847286863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48239933559708849231524575 72359900339563273847286863)
            ·
              refine ⟨108539850509344910770930295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72359900339563273847286863 108539850509344910770930295)
              ·
                refine ⟨162809775764017366156395443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108539850509344910770930295 162809775764017366156395443)
                ·
                  refine ⟨244214663646026049234593165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162809775764017366156395443 244214663646026049234593165)
                  ·
                    refine ⟨91580498867259768462972437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244214663646026049234593165 91580498867259768462972437)
                    ·
                      refine ⟨4292835884402801646701833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91580498867259768462972437 4292835884402801646701833)
                      ·
                        rfl

theorem cell23_8360268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_8360268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360268 prefixEnd_8360268 := by exact prefixLift 8360268
  have htrace : WordTrace (prefixWord ++ tailWord_8360268) baseStart_8360268 baseEnd_8360268 := by
    simpa [prefixWord, tailWord_8360268, baseEnd_8360268] using wordTrace_append hprefix tailTrace_8360268
  have hstable : (prefixWord ++ tailWord_8360268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360268).length < 2 ^ (prefixWord ++ tailWord_8360268).sum := by decide
  have hdescent : baseEnd_8360268 < baseStart_8360268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360332 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 4, 3, 2]
def baseStart_8360332 : Nat := 118140960795 + 8360332 * 2 ^ 59
def prefixEnd_8360332 : Nat := 4983230072969 + 3 ^ 40 * 8360332 * 2
def baseEnd_8360332 : Nat := 4292868747164689396301539

theorem tailTrace_8360332 : CollatzResearch.WordTrace tailWord_8360332 prefixEnd_8360332 4292868747164689396301539 := by
  unfold tailWord_8360332
  simp only [CollatzResearch.WordTrace]
  refine ⟨152463179373976234937637625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203284239165301646583516833 152463179373976234937637625)
  ·
    refine ⟨114347384530482176203228219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152463179373976234937637625 114347384530482176203228219)
    ·
      refine ⟨171521076795723264304842329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114347384530482176203228219 171521076795723264304842329)
      ·
        refine ⟨128640807596792448228631747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171521076795723264304842329 128640807596792448228631747)
        ·
          refine ⟨192961211395188672342947621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128640807596792448228631747 192961211395188672342947621)
          ·
            refine ⟨36180227136597876064302679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192961211395188672342947621 36180227136597876064302679)
            ·
              refine ⟨54270340704896814096454019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36180227136597876064302679 54270340704896814096454019)
              ·
                refine ⟨81405511057345221144681029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54270340704896814096454019 81405511057345221144681029)
                ·
                  refine ⟨15263533323252228964627693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81405511057345221144681029 15263533323252228964627693)
                  ·
                    refine ⟨5723824996219585861735385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15263533323252228964627693 5723824996219585861735385)
                    ·
                      refine ⟨4292868747164689396301539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5723824996219585861735385 4292868747164689396301539)
                      ·
                        rfl

theorem cell23_8360332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_8360332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360332 prefixEnd_8360332 := by exact prefixLift 8360332
  have htrace : WordTrace (prefixWord ++ tailWord_8360332) baseStart_8360332 baseEnd_8360332 := by
    simpa [prefixWord, tailWord_8360332, baseEnd_8360332] using wordTrace_append hprefix tailTrace_8360332
  have hstable : (prefixWord ++ tailWord_8360332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360332).length < 2 ^ (prefixWord ++ tailWord_8360332).sum := by decide
  have hdescent : baseEnd_8360332 < baseStart_8360332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360345 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_8360345 : Nat := 118140960795 + 8360345 * 2 ^ 59
def prefixEnd_8360345 : Nat := 4983230072969 + 3 ^ 40 * 8360345 * 2
def baseEnd_8360345 : Nat := 4292875422413197845438979

theorem tailTrace_8360345 : CollatzResearch.WordTrace tailWord_8360345 prefixEnd_8360345 4292875422413197845438979 := by
  unfold tailWord_8360345
  simp only [CollatzResearch.WordTrace]
  refine ⟨304926832896905373095498489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203284555264603582063665659 304926832896905373095498489)
  ·
    refine ⟨228695124672679029821623867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304926832896905373095498489 228695124672679029821623867)
    ·
      refine ⟨343042687009018544732435801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228695124672679029821623867 343042687009018544732435801)
      ·
        refine ⟨257282015256763908549326851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343042687009018544732435801 257282015256763908549326851)
        ·
          refine ⟨385923022885145862823990277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257282015256763908549326851 385923022885145862823990277)
          ·
            refine ⟨72360566790964849279498177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385923022885145862823990277 72360566790964849279498177)
            ·
              refine ⟨54270425093223636959623633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72360566790964849279498177 54270425093223636959623633)
              ·
                refine ⟨40702818819917727719717725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54270425093223636959623633 40702818819917727719717725)
                ·
                  refine ⟨15263557057469147894894147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40702818819917727719717725 15263557057469147894894147)
                  ·
                    refine ⟨22895335586203721842341221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15263557057469147894894147 22895335586203721842341221)
                    ·
                      refine ⟨4292875422413197845438979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22895335586203721842341221 4292875422413197845438979)
                      ·
                        rfl

theorem cell23_8360345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_8360345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360345 prefixEnd_8360345 := by exact prefixLift 8360345
  have htrace : WordTrace (prefixWord ++ tailWord_8360345) baseStart_8360345 baseEnd_8360345 := by
    simpa [prefixWord, tailWord_8360345, baseEnd_8360345] using wordTrace_append hprefix tailTrace_8360345
  have hstable : (prefixWord ++ tailWord_8360345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360345).length < 2 ^ (prefixWord ++ tailWord_8360345).sum := by decide
  have hdescent : baseEnd_8360345 < baseStart_8360345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360359 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 1, 5]
def baseStart_8360359 : Nat := 118140960795 + 8360359 * 2 ^ 59
def prefixEnd_8360359 : Nat := 4983230072969 + 3 ^ 40 * 8360359 * 2
def baseEnd_8360359 : Nat := 1430960870380786930221305

theorem tailTrace_8360359 : CollatzResearch.WordTrace tailWord_8360359 prefixEnd_8360359 1430960870380786930221305 := by
  unfold tailWord_8360359
  simp only [CollatzResearch.WordTrace]
  refine ⟨304927343518854653486508131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203284895679236435657672087 304927343518854653486508131)
  ·
    refine ⟨457391015278281980229762197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304927343518854653486508131 457391015278281980229762197)
    ·
      refine ⟨21440203841169467823270103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 457391015278281980229762197 21440203841169467823270103)
      ·
        refine ⟨32160305761754201734905155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21440203841169467823270103 32160305761754201734905155)
        ·
          refine ⟨48240458642631302602357733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32160305761754201734905155 48240458642631302602357733)
          ·
            refine ⟨9045085995493369237942075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48240458642631302602357733 9045085995493369237942075)
            ·
              refine ⟨13567628993240053856913113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9045085995493369237942075 13567628993240053856913113)
              ·
                refine ⟨10175721744930040392684835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13567628993240053856913113 10175721744930040392684835)
                ·
                  refine ⟨15263582617395060589027253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10175721744930040392684835 15263582617395060589027253)
                  ·
                    refine ⟨1430960870380786930221305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15263582617395060589027253 1430960870380786930221305)
                    ·
                      rfl

theorem cell23_8360359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_8360359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360359 prefixEnd_8360359 := by exact prefixLift 8360359
  have htrace : WordTrace (prefixWord ++ tailWord_8360359) baseStart_8360359 baseEnd_8360359 := by
    simpa [prefixWord, tailWord_8360359, baseEnd_8360359] using wordTrace_append hprefix tailTrace_8360359
  have hstable : (prefixWord ++ tailWord_8360359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360359).length < 2 ^ (prefixWord ++ tailWord_8360359).sum := by decide
  have hdescent : baseEnd_8360359 < baseStart_8360359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360375 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_8360375 : Nat := 118140960795 + 8360375 * 2 ^ 59
def prefixEnd_8360375 : Nat := 4983230072969 + 3 ^ 40 * 8360375 * 2
def baseEnd_8360375 : Nat := 4292890826832832728063841

theorem tailTrace_8360375 : CollatzResearch.WordTrace tailWord_8360375 prefixEnd_8360375 4292890826832832728063841 := by
  unfold tailWord_8360375
  simp only [CollatzResearch.WordTrace]
  refine ⟨304927927086796688219090579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203285284724531125479393719 304927927086796688219090579)
  ·
    refine ⟨457391890630195032328635869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304927927086796688219090579 457391890630195032328635869)
    ·
      refine ⟨171521958986323137123238451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457391890630195032328635869 171521958986323137123238451)
      ·
        refine ⟨257282938479484705684857677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171521958986323137123238451 257282938479484705684857677)
        ·
          refine ⟨96481101929806764631821629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257282938479484705684857677 96481101929806764631821629)
          ·
            refine ⟨36180413223677536736933111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96481101929806764631821629 36180413223677536736933111)
            ·
              refine ⟨54270619835516305105399667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36180413223677536736933111 54270619835516305105399667)
              ·
                refine ⟨81405929753274457658099501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54270619835516305105399667 81405929753274457658099501)
                ·
                  refine ⟨30527223657477921621787313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81405929753274457658099501 30527223657477921621787313)
                  ·
                    refine ⟨22895417743108441216340485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30527223657477921621787313 22895417743108441216340485)
                    ·
                      refine ⟨4292890826832832728063841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22895417743108441216340485 4292890826832832728063841)
                      ·
                        rfl

theorem cell23_8360375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_8360375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360375 prefixEnd_8360375 := by exact prefixLift 8360375
  have htrace : WordTrace (prefixWord ++ tailWord_8360375) baseStart_8360375 baseEnd_8360375 := by
    simpa [prefixWord, tailWord_8360375, baseEnd_8360375] using wordTrace_append hprefix tailTrace_8360375
  have hstable : (prefixWord ++ tailWord_8360375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360375).length < 2 ^ (prefixWord ++ tailWord_8360375).sum := by decide
  have hdescent : baseEnd_8360375 < baseStart_8360375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360382 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_8360382 : Nat := 118140960795 + 8360382 * 2 ^ 59
def prefixEnd_8360382 : Nat := 4983230072969 + 3 ^ 40 * 8360382 * 2
def baseEnd_8360382 : Nat := 4292894421197414200676309

theorem tailTrace_8360382 : CollatzResearch.WordTrace tailWord_8360382 prefixEnd_8360382 4292894421197414200676309 := by
  unfold tailWord_8360382
  simp only [CollatzResearch.WordTrace]
  refine ⟨38116022799721416051824425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203285454931847552276396933 38116022799721416051824425)
  ·
    refine ⟨28587017099791062038868319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38116022799721416051824425 28587017099791062038868319)
    ·
      refine ⟨42880525649686593058302479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28587017099791062038868319 42880525649686593058302479)
      ·
        refine ⟨64320788474529889587453719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42880525649686593058302479 64320788474529889587453719)
        ·
          refine ⟨96481182711794834381180579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64320788474529889587453719 96481182711794834381180579)
          ·
            refine ⟨144721774067692251571770869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96481182711794834381180579 144721774067692251571770869)
            ·
              refine ⟨13567666318846148584853519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144721774067692251571770869 13567666318846148584853519)
              ·
                refine ⟨20351499478269222877280279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13567666318846148584853519 20351499478269222877280279)
                ·
                  refine ⟨30527249217403834315920419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20351499478269222877280279 30527249217403834315920419)
                  ·
                    refine ⟨45790873826105751473880629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30527249217403834315920419 45790873826105751473880629)
                    ·
                      refine ⟨4292894421197414200676309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45790873826105751473880629 4292894421197414200676309)
                      ·
                        rfl

theorem cell23_8360382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_8360382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360382 prefixEnd_8360382 := by exact prefixLift 8360382
  have htrace : WordTrace (prefixWord ++ tailWord_8360382) baseStart_8360382 baseEnd_8360382 := by
    simpa [prefixWord, tailWord_8360382, baseEnd_8360382] using wordTrace_append hprefix tailTrace_8360382
  have hstable : (prefixWord ++ tailWord_8360382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360382).length < 2 ^ (prefixWord ++ tailWord_8360382).sum := by decide
  have hdescent : baseEnd_8360382 < baseStart_8360382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360395 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 3]
def baseStart_8360395 : Nat := 118140960795 + 8360395 * 2 ^ 59
def prefixEnd_8360395 : Nat := 4983230072969 + 3 ^ 40 * 8360395 * 2
def baseEnd_8360395 : Nat := 4292901096445922649813749

theorem tailTrace_8360395 : CollatzResearch.WordTrace tailWord_8360395 prefixEnd_8360395 4292901096445922649813749 := by
  unfold tailWord_8360395
  simp only [CollatzResearch.WordTrace]
  refine ⟨304928656546724231634818639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203285771031149487756545759 304928656546724231634818639)
  ·
    refine ⟨457392984820086347452227959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304928656546724231634818639 457392984820086347452227959)
    ·
      refine ⟨686089477230129521178341939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457392984820086347452227959 686089477230129521178341939)
      ·
        refine ⟨1029134215845194281767512909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686089477230129521178341939 1029134215845194281767512909)
        ·
          refine ⟨385925330941947855662817341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1029134215845194281767512909 385925330941947855662817341)
          ·
            refine ⟨144721999103230445873556503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385925330941947855662817341 144721999103230445873556503)
            ·
              refine ⟨217082998654845668810334755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144721999103230445873556503 217082998654845668810334755)
              ·
                refine ⟨325624497982268503215502133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217082998654845668810334755 325624497982268503215502133)
                ·
                  refine ⟨30527296685837672176453325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325624497982268503215502133 30527296685837672176453325)
                  ·
                    refine ⟨11447736257189127066169997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30527296685837672176453325 11447736257189127066169997)
                    ·
                      refine ⟨4292901096445922649813749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11447736257189127066169997 4292901096445922649813749)
                      ·
                        rfl

theorem cell23_8360395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 3].length) (baseStart_8360395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360395 prefixEnd_8360395 := by exact prefixLift 8360395
  have htrace : WordTrace (prefixWord ++ tailWord_8360395) baseStart_8360395 baseEnd_8360395 := by
    simpa [prefixWord, tailWord_8360395, baseEnd_8360395] using wordTrace_append hprefix tailTrace_8360395
  have hstable : (prefixWord ++ tailWord_8360395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360395).length < 2 ^ (prefixWord ++ tailWord_8360395).sum := by decide
  have hdescent : baseEnd_8360395 < baseStart_8360395 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360429 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_8360429 : Nat := 118140960795 + 8360429 * 2 ^ 59
def prefixEnd_8360429 : Nat := 4983230072969 + 3 ^ 40 * 8360429 * 2
def baseEnd_8360429 : Nat := 4292918554788175516788593

theorem tailTrace_8360429 : CollatzResearch.WordTrace tailWord_8360429 prefixEnd_8360429 4292918554788175516788593 := by
  unfold tailWord_8360429
  simp only [CollatzResearch.WordTrace]
  refine ⟨304929896628601055441556341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203286597752400703627704227 304929896628601055441556341)
  ·
    refine ⟨28587177808931348947645907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304929896628601055441556341 28587177808931348947645907)
    ·
      refine ⟨42880766713397023421468861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28587177808931348947645907 42880766713397023421468861)
      ·
        refine ⟨16080287517523883783050823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42880766713397023421468861 16080287517523883783050823)
        ·
          refine ⟨24120431276285825674576235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16080287517523883783050823 24120431276285825674576235)
          ·
            refine ⟨36180646914428738511864353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24120431276285825674576235 36180646914428738511864353)
            ·
              refine ⟨27135485185821553883898265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36180646914428738511864353 27135485185821553883898265)
              ·
                refine ⟨20351613889366165412923699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27135485185821553883898265 20351613889366165412923699)
                ·
                  refine ⟨30527420834049248119385549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20351613889366165412923699 30527420834049248119385549)
                  ·
                    refine ⟨11447782812768468044769581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30527420834049248119385549 11447782812768468044769581)
                    ·
                      refine ⟨4292918554788175516788593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11447782812768468044769581 4292918554788175516788593)
                      ·
                        rfl

theorem cell23_8360429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_8360429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360429 prefixEnd_8360429 := by exact prefixLift 8360429
  have htrace : WordTrace (prefixWord ++ tailWord_8360429) baseStart_8360429 baseEnd_8360429 := by
    simpa [prefixWord, tailWord_8360429, baseEnd_8360429] using wordTrace_append hprefix tailTrace_8360429
  have hstable : (prefixWord ++ tailWord_8360429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360429).length < 2 ^ (prefixWord ++ tailWord_8360429).sum := by decide
  have hdescent : baseEnd_8360429 < baseStart_8360429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360445 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_8360445 : Nat := 118140960795 + 8360445 * 2 ^ 59
def prefixEnd_8360445 : Nat := 4983230072969 + 3 ^ 40 * 8360445 * 2
def baseEnd_8360445 : Nat := 1430975590159549151396173

theorem tailTrace_8360445 : CollatzResearch.WordTrace tailWord_8360445 prefixEnd_8360445 1430975590159549151396173 := by
  unfold tailWord_8360445
  simp only [CollatzResearch.WordTrace]
  refine ⟨304930480196543090174138789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203286986797695393449425859 304930480196543090174138789)
  ·
    refine ⟨57174465036851829407651023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304930480196543090174138789 57174465036851829407651023)
    ·
      refine ⟨85761697555277744111476535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57174465036851829407651023 85761697555277744111476535)
      ·
        refine ⟨128642546332916616167214803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85761697555277744111476535 128642546332916616167214803)
        ·
          refine ⟨192963819499374924250822205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128642546332916616167214803 192963819499374924250822205)
          ·
            refine ⟨72361432312265596594058327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192963819499374924250822205 72361432312265596594058327)
            ·
              refine ⟨108542148468398394891087491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72361432312265596594058327 108542148468398394891087491)
              ·
                refine ⟨162813222702597592336631237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108542148468398394891087491 162813222702597592336631237)
                ·
                  refine ⟨30527479256737048563118357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162813222702597592336631237 30527479256737048563118357)
                  ·
                    refine ⟨1430975590159549151396173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30527479256737048563118357 1430975590159549151396173)
                    ·
                      rfl

theorem cell23_8360445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_8360445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360445 prefixEnd_8360445 := by exact prefixLift 8360445
  have htrace : WordTrace (prefixWord ++ tailWord_8360445) baseStart_8360445 baseEnd_8360445 := by
    simpa [prefixWord, tailWord_8360445, baseEnd_8360445] using wordTrace_append hprefix tailTrace_8360445
  have hstable : (prefixWord ++ tailWord_8360445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360445).length < 2 ^ (prefixWord ++ tailWord_8360445).sum := by decide
  have hdescent : baseEnd_8360445 < baseStart_8360445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360462 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_8360462 : Nat := 118140960795 + 8360462 * 2 ^ 59
def prefixEnd_8360462 : Nat := 4983230072969 + 3 ^ 40 * 8360462 * 2
def baseEnd_8360462 : Nat := 1430978499883257962558647

theorem tailTrace_8360462 : CollatzResearch.WordTrace tailWord_8360462 prefixEnd_8360462 1430978499883257962558647 := by
  unfold tailWord_8360462
  simp only [CollatzResearch.WordTrace]
  refine ⟨38116387529685187759688455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203287400158321001385005093 38116387529685187759688455)
  ·
    refine ⟨57174581294527781639532683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38116387529685187759688455 57174581294527781639532683)
    ·
      refine ⟨85761871941791672459299025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57174581294527781639532683 85761871941791672459299025)
      ·
        refine ⟨64321403956343754344474269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85761871941791672459299025 64321403956343754344474269)
        ·
          refine ⟨24120526483628907879177851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64321403956343754344474269 24120526483628907879177851)
          ·
            refine ⟨36180789725443361818766777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24120526483628907879177851 36180789725443361818766777)
            ·
              refine ⟨27135592294082521364075083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36180789725443361818766777 27135592294082521364075083)
              ·
                refine ⟨40703388441123782046112625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27135592294082521364075083 40703388441123782046112625)
                ·
                  refine ⟨30527541330842836534584469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40703388441123782046112625 30527541330842836534584469)
                  ·
                    refine ⟨1430978499883257962558647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30527541330842836534584469 1430978499883257962558647)
                    ·
                      rfl

theorem cell23_8360462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_8360462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360462 prefixEnd_8360462 := by exact prefixLift 8360462
  have htrace : WordTrace (prefixWord ++ tailWord_8360462) baseStart_8360462 baseEnd_8360462 := by
    simpa [prefixWord, tailWord_8360462, baseEnd_8360462] using wordTrace_append hprefix tailTrace_8360462
  have hstable : (prefixWord ++ tailWord_8360462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360462).length < 2 ^ (prefixWord ++ tailWord_8360462).sum := by decide
  have hdescent : baseEnd_8360462 < baseStart_8360462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360465 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_8360465 : Nat := 118140960795 + 8360465 * 2 ^ 59
def prefixEnd_8360465 : Nat := 4983230072969 + 3 ^ 40 * 8360465 * 2
def baseEnd_8360465 : Nat := 4292937040091737375938427

theorem tailTrace_8360465 : CollatzResearch.WordTrace tailWord_8360465 prefixEnd_8360465 4292937040091737375938427 := by
  unfold tailWord_8360465
  simp only [CollatzResearch.WordTrace]
  refine ⟨304931209656470633589866849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203287473104313755726577899 304931209656470633589866849)
  ·
    refine ⟨228698407242352975192400137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304931209656470633589866849 228698407242352975192400137)
    ·
      refine ⟨171523805431764731394300103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228698407242352975192400137 171523805431764731394300103)
      ·
        refine ⟨257285708147647097091450155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171523805431764731394300103 257285708147647097091450155)
        ·
          refine ⟨385928562221470645637175233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257285708147647097091450155 385928562221470645637175233)
          ·
            refine ⟨289446421666102984227881425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385928562221470645637175233 289446421666102984227881425)
            ·
              refine ⟨217084816249577238170911069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289446421666102984227881425 217084816249577238170911069)
              ·
                refine ⟨81406806093591464314091651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217084816249577238170911069 81406806093591464314091651)
                ·
                  refine ⟨122110209140387196471137477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81406806093591464314091651 122110209140387196471137477)
                  ·
                    refine ⟨22895664213822599338338277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122110209140387196471137477 22895664213822599338338277)
                    ·
                      refine ⟨4292937040091737375938427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22895664213822599338338277 4292937040091737375938427)
                      ·
                        rfl

theorem cell23_8360465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_8360465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360465 prefixEnd_8360465 := by exact prefixLift 8360465
  have htrace : WordTrace (prefixWord ++ tailWord_8360465) baseStart_8360465 baseEnd_8360465 := by
    simpa [prefixWord, tailWord_8360465, baseEnd_8360465] using wordTrace_append hprefix tailTrace_8360465
  have hstable : (prefixWord ++ tailWord_8360465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360465).length < 2 ^ (prefixWord ++ tailWord_8360465).sum := by decide
  have hdescent : baseEnd_8360465 < baseStart_8360465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360509 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 7]
def baseStart_8360509 : Nat := 118140960795 + 8360509 * 2 ^ 59
def prefixEnd_8360509 : Nat := 4983230072969 + 3 ^ 40 * 8360509 * 2
def baseEnd_8360509 : Nat := 476995514804503911532025

theorem tailTrace_8360509 : CollatzResearch.WordTrace tailWord_8360509 prefixEnd_8360509 476995514804503911532025 := by
  unfold tailWord_8360509
  simp only [CollatzResearch.WordTrace]
  refine ⟨304932814468311229104468581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203288542978874152736312387 304932814468311229104468581)
  ·
    refine ⟨57174902712808355457087859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304932814468311229104468581 57174902712808355457087859)
    ·
      refine ⟨85762354069212533185631789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57174902712808355457087859 85762354069212533185631789)
      ·
        refine ⟨32160882775954699944611921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85762354069212533185631789 32160882775954699944611921)
        ·
          refine ⟨24120662081966024958458941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32160882775954699944611921 24120662081966024958458941)
          ·
            refine ⟨9045248280737259359422103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24120662081966024958458941 9045248280737259359422103)
            ·
              refine ⟨13567872421105889039133155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9045248280737259359422103 13567872421105889039133155)
              ·
                refine ⟨20351808631658833558699733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13567872421105889039133155 20351808631658833558699733)
                ·
                  refine ⟨476995514804503911532025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20351808631658833558699733 476995514804503911532025)
                  ·
                    rfl

theorem cell23_8360509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_8360509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360509 prefixEnd_8360509 := by exact prefixLift 8360509
  have htrace : WordTrace (prefixWord ++ tailWord_8360509) baseStart_8360509 baseEnd_8360509 := by
    simpa [prefixWord, tailWord_8360509, baseEnd_8360509] using wordTrace_append hprefix tailTrace_8360509
  have hstable : (prefixWord ++ tailWord_8360509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360509).length < 2 ^ (prefixWord ++ tailWord_8360509).sum := by decide
  have hdescent : baseEnd_8360509 < baseStart_8360509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360586 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_8360586 : Nat := 118140960795 + 8360586 * 2 ^ 59
def prefixEnd_8360586 : Nat := 4983230072969 + 3 ^ 40 * 8360586 * 2
def baseEnd_8360586 : Nat := 1430999723750310467508457

theorem tailTrace_8360586 : CollatzResearch.WordTrace tailWord_8360586 prefixEnd_8360586 1430999723750310467508457 := by
  unfold tailWord_8360586
  simp only [CollatzResearch.WordTrace]
  refine ⟨76233905722258067813755403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203290415259354847503347741 76233905722258067813755403)
  ·
    refine ⟨114350858583387101720633105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76233905722258067813755403 114350858583387101720633105)
    ·
      refine ⟨85763143937540326290474829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114350858583387101720633105 85763143937540326290474829)
      ·
        refine ⟨32161178976577622358928061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85763143937540326290474829 32161178976577622358928061)
        ·
          refine ⟨12060442116216608384598023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32161178976577622358928061 12060442116216608384598023)
          ·
            refine ⟨18090663174324912576897035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12060442116216608384598023 18090663174324912576897035)
            ·
              refine ⟨27135994761487368865345553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18090663174324912576897035 27135994761487368865345553)
              ·
                refine ⟨20351996071115526649009165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27135994761487368865345553 20351996071115526649009165)
                ·
                  refine ⟨7631998526668322493378437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20351996071115526649009165 7631998526668322493378437)
                  ·
                    refine ⟨1430999723750310467508457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7631998526668322493378437 1430999723750310467508457)
                    ·
                      rfl

theorem cell23_8360586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_8360586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360586 prefixEnd_8360586 := by exact prefixLift 8360586
  have htrace : WordTrace (prefixWord ++ tailWord_8360586) baseStart_8360586 baseEnd_8360586 := by
    simpa [prefixWord, tailWord_8360586, baseEnd_8360586] using wordTrace_append hprefix tailTrace_8360586
  have hstable : (prefixWord ++ tailWord_8360586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360586).length < 2 ^ (prefixWord ++ tailWord_8360586).sum := by decide
  have hdescent : baseEnd_8360586 < baseStart_8360586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360596 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_8360596 : Nat := 118140960795 + 8360596 * 2 ^ 59
def prefixEnd_8360596 : Nat := 4983230072969 + 3 ^ 40 * 8360596 * 2
def baseEnd_8360596 : Nat := 4293004306057476363400325

theorem tailTrace_8360596 : CollatzResearch.WordTrace tailWord_8360596 prefixEnd_8360596 4293004306057476363400325 := by
  unfold tailWord_8360596
  simp only [CollatzResearch.WordTrace]
  refine ⟨152467993809498021481442821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203290658412664028641923761 152467993809498021481442821)
  ·
    refine ⟨28587748839280879027770529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152467993809498021481442821 28587748839280879027770529)
    ·
      refine ⟨21440811629460659270827897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28587748839280879027770529 21440811629460659270827897)
      ·
        refine ⟨16080608722095494453120923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21440811629460659270827897 16080608722095494453120923)
        ·
          refine ⟨24120913083143241679681385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16080608722095494453120923 24120913083143241679681385)
          ·
            refine ⟨18090684812357431259761039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24120913083143241679681385 18090684812357431259761039)
            ·
              refine ⟨27136027218536146889641559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18090684812357431259761039 27136027218536146889641559)
              ·
                refine ⟨40704040827804220334462339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27136027218536146889641559 40704040827804220334462339)
                ·
                  refine ⟨61056061241706330501693509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40704040827804220334462339 61056061241706330501693509)
                  ·
                    refine ⟨11448011482819936969067533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61056061241706330501693509 11448011482819936969067533)
                    ·
                      refine ⟨4293004306057476363400325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11448011482819936969067533 4293004306057476363400325)
                      ·
                        rfl

theorem cell23_8360596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_8360596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360596 prefixEnd_8360596 := by exact prefixLift 8360596
  have htrace : WordTrace (prefixWord ++ tailWord_8360596) baseStart_8360596 baseEnd_8360596 := by
    simpa [prefixWord, tailWord_8360596, baseEnd_8360596] using wordTrace_append hprefix tailTrace_8360596
  have hstable : (prefixWord ++ tailWord_8360596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360596).length < 2 ^ (prefixWord ++ tailWord_8360596).sum := by decide
  have hdescent : baseEnd_8360596 < baseStart_8360596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360750 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_8360750 : Nat := 118140960795 + 8360750 * 2 ^ 59
def prefixEnd_8360750 : Nat := 4983230072969 + 3 ^ 40 * 8360750 * 2
def baseEnd_8360750 : Nat := 4293083382078268760874617

theorem tailTrace_8360750 : CollatzResearch.WordTrace tailWord_8360750 prefixEnd_8360750 4293083382078268760874617 := by
  unfold tailWord_8360750
  simp only [CollatzResearch.WordTrace]
  refine ⟨38117700557554765907998963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203294402973625418175994469 38117700557554765907998963)
  ·
    refine ⟨57176550836332148861998445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38117700557554765907998963 57176550836332148861998445)
    ·
      refine ⟨21441206563624555823249417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57176550836332148861998445 21441206563624555823249417)
      ·
        refine ⟨16080904922718416867437063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21441206563624555823249417 16080904922718416867437063)
        ·
          refine ⟨24121357384077625301155595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16080904922718416867437063 24121357384077625301155595)
          ·
            refine ⟨36182036076116437951733393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24121357384077625301155595 36182036076116437951733393)
            ·
              refine ⟨27136527057087328463800045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36182036076116437951733393 27136527057087328463800045)
              ·
                refine ⟨10176197646407748173925017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27136527057087328463800045 10176197646407748173925017)
                ·
                  refine ⟨7632148234805811130443763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10176197646407748173925017 7632148234805811130443763)
                  ·
                    refine ⟨11448222352208716695665645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7632148234805811130443763 11448222352208716695665645)
                    ·
                      refine ⟨4293083382078268760874617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11448222352208716695665645 4293083382078268760874617)
                      ·
                        rfl

theorem cell23_8360750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_8360750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360750 prefixEnd_8360750 := by exact prefixLift 8360750
  have htrace : WordTrace (prefixWord ++ tailWord_8360750) baseStart_8360750 baseEnd_8360750 := by
    simpa [prefixWord, tailWord_8360750, baseEnd_8360750] using wordTrace_append hprefix tailTrace_8360750
  have hstable : (prefixWord ++ tailWord_8360750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360750).length < 2 ^ (prefixWord ++ tailWord_8360750).sum := by decide
  have hdescent : baseEnd_8360750 < baseStart_8360750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360759 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_8360759 : Nat := 118140960795 + 8360759 * 2 ^ 59
def prefixEnd_8360759 : Nat := 4983230072969 + 3 ^ 40 * 8360759 * 2
def baseEnd_8360759 : Nat := 4293088003404159225662075

theorem tailTrace_8360759 : CollatzResearch.WordTrace tailWord_8360759 prefixEnd_8360759 4293088003404159225662075 := by
  unfold tailWord_8360759
  simp only [CollatzResearch.WordTrace]
  refine ⟨304941932717405521801069331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203294621811603681200712887 304941932717405521801069331)
  ·
    refine ⟨457412899076108282701603997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304941932717405521801069331 457412899076108282701603997)
    ·
      refine ⟨171529837153540606013101499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457412899076108282701603997 171529837153540606013101499)
      ·
        refine ⟨257294755730310909019652249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171529837153540606013101499 257294755730310909019652249)
        ·
          refine ⟨192971066797733181764739187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257294755730310909019652249 192971066797733181764739187)
          ·
            refine ⟨289456600196599772647108781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192971066797733181764739187 289456600196599772647108781)
            ·
              refine ⟨108546225073724914742665793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289456600196599772647108781 108546225073724914742665793)
              ·
                refine ⟨81409668805293686056999345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108546225073724914742665793 81409668805293686056999345)
                ·
                  refine ⟨61057251603970264542749509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81409668805293686056999345 61057251603970264542749509)
                  ·
                    refine ⟨11448234675744424601765533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61057251603970264542749509 11448234675744424601765533)
                    ·
                      refine ⟨4293088003404159225662075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11448234675744424601765533 4293088003404159225662075)
                      ·
                        rfl

theorem cell23_8360759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_8360759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360759 prefixEnd_8360759 := by exact prefixLift 8360759
  have htrace : WordTrace (prefixWord ++ tailWord_8360759) baseStart_8360759 baseEnd_8360759 := by
    simpa [prefixWord, tailWord_8360759, baseEnd_8360759] using wordTrace_append hprefix tailTrace_8360759
  have hstable : (prefixWord ++ tailWord_8360759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360759).length < 2 ^ (prefixWord ++ tailWord_8360759).sum := by decide
  have hdescent : baseEnd_8360759 < baseStart_8360759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360796 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 7]
def baseStart_8360796 : Nat := 118140960795 + 8360796 * 2 ^ 59
def prefixEnd_8360796 : Nat := 4983230072969 + 3 ^ 40 * 8360796 * 2
def baseEnd_8360796 : Nat := 477011889132041731211045

theorem tailTrace_8360796 : CollatzResearch.WordTrace tailWord_8360796 prefixEnd_8360796 477011889132041731211045 := by
  unfold tailWord_8360796
  simp only [CollatzResearch.WordTrace]
  refine ⟨152471641109135738560083121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203295521478847651413444161 152471641109135738560083121)
  ·
    refine ⟨114353730831851803920062341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152471641109135738560083121 114353730831851803920062341)
    ·
      refine ⟨21441324530972213235011689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114353730831851803920062341 21441324530972213235011689)
      ·
        refine ⟨16080993398229159926258767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21441324530972213235011689 16080993398229159926258767)
        ·
          refine ⟨24121490097343739889388151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16080993398229159926258767 24121490097343739889388151)
          ·
            refine ⟨36182235146015609834082227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24121490097343739889388151 36182235146015609834082227)
            ·
              refine ⟨54273352719023414751123341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36182235146015609834082227 54273352719023414751123341)
              ·
                refine ⟨20352507269633780531671253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54273352719023414751123341 20352507269633780531671253)
                ·
                  refine ⟨477011889132041731211045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20352507269633780531671253 477011889132041731211045)
                  ·
                    rfl

theorem cell23_8360796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_8360796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360796 prefixEnd_8360796 := by exact prefixLift 8360796
  have htrace : WordTrace (prefixWord ++ tailWord_8360796) baseStart_8360796 baseEnd_8360796 := by
    simpa [prefixWord, tailWord_8360796, baseEnd_8360796] using wordTrace_append hprefix tailTrace_8360796
  have hstable : (prefixWord ++ tailWord_8360796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360796).length < 2 ^ (prefixWord ++ tailWord_8360796).sum := by decide
  have hdescent : baseEnd_8360796 < baseStart_8360796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360807 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_8360807 : Nat := 118140960795 + 8360807 * 2 ^ 59
def prefixEnd_8360807 : Nat := 4983230072969 + 3 ^ 40 * 8360807 * 2
def baseEnd_8360807 : Nat := 4293112650475575037861855

theorem tailTrace_8360807 : CollatzResearch.WordTrace tailWord_8360807 prefixEnd_8360807 4293112650475575037861855 := by
  unfold tailWord_8360807
  simp only [CollatzResearch.WordTrace]
  refine ⟨304943683421231625998816675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203295788947487750665877783 304943683421231625998816675)
  ·
    refine ⟨457415525131847438998225013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304943683421231625998816675 457415525131847438998225013)
    ·
      refine ⟨42882705481110697406083595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 457415525131847438998225013 42882705481110697406083595)
      ·
        refine ⟨64324058221666046109125393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42882705481110697406083595 64324058221666046109125393)
        ·
          refine ⟨48243043666249534581844045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64324058221666046109125393 48243043666249534581844045)
          ·
            refine ⟨18091141374843575468191517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48243043666249534581844045 18091141374843575468191517)
            ·
              refine ⟨6784178015566340800571819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18091141374843575468191517 6784178015566340800571819)
              ·
                refine ⟨10176267023349511200857729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784178015566340800571819 10176267023349511200857729)
                ·
                  refine ⟨7632200267512133400643297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10176267023349511200857729 7632200267512133400643297)
                  ·
                    refine ⟨5724150200634100050482473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7632200267512133400643297 5724150200634100050482473)
                    ·
                      refine ⟨4293112650475575037861855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724150200634100050482473 4293112650475575037861855)
                      ·
                        rfl

theorem cell23_8360807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_8360807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360807 prefixEnd_8360807 := by exact prefixLift 8360807
  have htrace : WordTrace (prefixWord ++ tailWord_8360807) baseStart_8360807 baseEnd_8360807 := by
    simpa [prefixWord, tailWord_8360807, baseEnd_8360807] using wordTrace_append hprefix tailTrace_8360807
  have hstable : (prefixWord ++ tailWord_8360807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360807).length < 2 ^ (prefixWord ++ tailWord_8360807).sum := by decide
  have hdescent : baseEnd_8360807 < baseStart_8360807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360816 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 2, 5, 2]
def baseStart_8360816 : Nat := 118140960795 + 8360816 * 2 ^ 59
def prefixEnd_8360816 : Nat := 4983230072969 + 3 ^ 40 * 8360816 * 2
def baseEnd_8360816 : Nat := 4293117271801465502649313

theorem tailTrace_8360816 : CollatzResearch.WordTrace tailWord_8360816 prefixEnd_8360816 4293117271801465502649313 := by
  unfold tailWord_8360816
  simp only [CollatzResearch.WordTrace]
  refine ⟨152472005839099510267947151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203296007785466013690596201 152472005839099510267947151)
  ·
    refine ⟨228708008758649265401920727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152472005839099510267947151 228708008758649265401920727)
    ·
      refine ⟨343062013137973898102881091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228708008758649265401920727 343062013137973898102881091)
      ·
        refine ⟨514593019706960847154321637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343062013137973898102881091 514593019706960847154321637)
        ·
          refine ⟨96486191195055158841435307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514593019706960847154321637 96486191195055158841435307)
          ·
            refine ⟨144729286792582738262152961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96486191195055158841435307 144729286792582738262152961)
            ·
              refine ⟨108546965094437053696614721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144729286792582738262152961 108546965094437053696614721)
              ·
                refine ⟨81410223820827790272461041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108546965094437053696614721 81410223820827790272461041)
                ·
                  refine ⟨61057667865620842704345781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81410223820827790272461041 61057667865620842704345781)
                  ·
                    refine ⟨5724156362401954003532417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61057667865620842704345781 5724156362401954003532417)
                    ·
                      refine ⟨4293117271801465502649313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724156362401954003532417 4293117271801465502649313)
                      ·
                        rfl

theorem cell23_8360816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 5, 2].length) (baseStart_8360816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360816 prefixEnd_8360816 := by exact prefixLift 8360816
  have htrace : WordTrace (prefixWord ++ tailWord_8360816) baseStart_8360816 baseEnd_8360816 := by
    simpa [prefixWord, tailWord_8360816, baseEnd_8360816] using wordTrace_append hprefix tailTrace_8360816
  have hstable : (prefixWord ++ tailWord_8360816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360816).length < 2 ^ (prefixWord ++ tailWord_8360816).sum := by decide
  have hdescent : baseEnd_8360816 < baseStart_8360816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360907 : List Nat := [1, 1, 1, 1, 3, 7, 2, 2, 1, 4]
def baseStart_8360907 : Nat := 118140960795 + 8360907 * 2 ^ 59
def prefixEnd_8360907 : Nat := 4983230072969 + 3 ^ 40 * 8360907 * 2
def baseEnd_8360907 : Nat := 1431054666180341548870465

theorem tailTrace_8360907 : CollatzResearch.WordTrace tailWord_8360907 prefixEnd_8360907 1431054666180341548870465 := by
  unfold tailWord_8360907
  simp only [CollatzResearch.WordTrace]
  refine ⟨304947330720869343077456975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203298220480579562051637983 304947330720869343077456975)
  ·
    refine ⟨457420996081304014616185463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304947330720869343077456975 457420996081304014616185463)
    ·
      refine ⟨686131494121956021924278195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457420996081304014616185463 686131494121956021924278195)
      ·
        refine ⟨1029197241182934032886417293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686131494121956021924278195 1029197241182934032886417293)
        ·
          refine ⟨385948965443600262332406485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1029197241182934032886417293 385948965443600262332406485)
          ·
            refine ⟨9045678877584381148415777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 385948965443600262332406485 9045678877584381148415777)
            ·
              refine ⟨6784259158188285861311833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9045678877584381148415777 6784259158188285861311833)
              ·
                refine ⟨5088194368641214395983875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6784259158188285861311833 5088194368641214395983875)
                ·
                  refine ⟨7632291552961821593975813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5088194368641214395983875 7632291552961821593975813)
                  ·
                    refine ⟨1431054666180341548870465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7632291552961821593975813 1431054666180341548870465)
                    ·
                      rfl

theorem cell23_8360907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 4].length) (baseStart_8360907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360907 prefixEnd_8360907 := by exact prefixLift 8360907
  have htrace : WordTrace (prefixWord ++ tailWord_8360907) baseStart_8360907 baseEnd_8360907 := by
    simpa [prefixWord, tailWord_8360907, baseEnd_8360907] using wordTrace_append hprefix tailTrace_8360907
  have hstable : (prefixWord ++ tailWord_8360907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360907).length < 2 ^ (prefixWord ++ tailWord_8360907).sum := by decide
  have hdescent : baseEnd_8360907 < baseStart_8360907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360913 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_8360913 : Nat := 118140960795 + 8360913 * 2 ^ 59
def prefixEnd_8360913 : Nat := 4983230072969 + 3 ^ 40 * 8360913 * 2
def baseEnd_8360913 : Nat := 4293167079424951623136367

theorem tailTrace_8360913 : CollatzResearch.WordTrace tailWord_8360913 prefixEnd_8360913 4293167079424951623136367 := by
  unfold tailWord_8360913
  simp only [CollatzResearch.WordTrace]
  refine ⟨304947549558847606102175393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203298366372565070734783595 304947549558847606102175393)
  ·
    refine ⟨228710662169135704576631545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304947549558847606102175393 228710662169135704576631545)
    ·
      refine ⟨171532996626851778432473659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228710662169135704576631545 171532996626851778432473659)
      ·
        refine ⟨257299494940277667648710489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171532996626851778432473659 257299494940277667648710489)
        ·
          refine ⟨192974621205208250736532867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257299494940277667648710489 192974621205208250736532867)
          ·
            refine ⟨289461931807812376104799301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192974621205208250736532867 289461931807812376104799301)
            ·
              refine ⟨54274112213964820519649869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289461931807812376104799301 54274112213964820519649869)
              ·
                refine ⟨20352792080236807694868701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54274112213964820519649869 20352792080236807694868701)
                ·
                  refine ⟨7632297030088802885575763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20352792080236807694868701 7632297030088802885575763)
                  ·
                    refine ⟨11448445545133204328363645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7632297030088802885575763 11448445545133204328363645)
                    ·
                      refine ⟨4293167079424951623136367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11448445545133204328363645 4293167079424951623136367)
                      ·
                        rfl

theorem cell23_8360913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_8360913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360913 prefixEnd_8360913 := by exact prefixLift 8360913
  have htrace : WordTrace (prefixWord ++ tailWord_8360913) baseStart_8360913 baseEnd_8360913 := by
    simpa [prefixWord, tailWord_8360913, baseEnd_8360913] using wordTrace_append hprefix tailTrace_8360913
  have hstable : (prefixWord ++ tailWord_8360913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360913).length < 2 ^ (prefixWord ++ tailWord_8360913).sum := by decide
  have hdescent : baseEnd_8360913 < baseStart_8360913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360950 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_8360950 : Nat := 118140960795 + 8360950 * 2 ^ 59
def prefixEnd_8360950 : Nat := 4983230072969 + 3 ^ 40 * 8360950 * 2
def baseEnd_8360950 : Nat := 1431062026069722659457899

theorem tailTrace_8360950 : CollatzResearch.WordTrace tailWord_8360950 prefixEnd_8360950 1431062026069722659457899 := by
  unfold tailWord_8360950
  simp only [CollatzResearch.WordTrace]
  refine ⟨19059306191232097588829519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203299266039809040947514869 19059306191232097588829519)
  ·
    refine ⟨28588959286848146383244279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19059306191232097588829519 28588959286848146383244279)
    ·
      refine ⟨42883438930272219574866419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28588959286848146383244279 42883438930272219574866419)
      ·
        refine ⟨64325158395408329362299629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42883438930272219574866419 64325158395408329362299629)
        ·
          refine ⟨24121934398278123510862361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64325158395408329362299629 24121934398278123510862361)
          ·
            refine ⟨18091450798708592633146771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24121934398278123510862361 18091450798708592633146771)
            ·
              refine ⟨27137176198062888949720157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18091450798708592633146771 27137176198062888949720157)
              ·
                refine ⟨10176441074273583356145059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27137176198062888949720157 10176441074273583356145059)
                ·
                  refine ⟨15264661611410375034217589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10176441074273583356145059 15264661611410375034217589)
                  ·
                    refine ⟨1431062026069722659457899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15264661611410375034217589 1431062026069722659457899)
                    ·
                      rfl

theorem cell23_8360950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_8360950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360950 prefixEnd_8360950 := by exact prefixLift 8360950
  have htrace : WordTrace (prefixWord ++ tailWord_8360950) baseStart_8360950 baseEnd_8360950 := by
    simpa [prefixWord, tailWord_8360950, baseEnd_8360950] using wordTrace_append hprefix tailTrace_8360950
  have hstable : (prefixWord ++ tailWord_8360950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360950).length < 2 ^ (prefixWord ++ tailWord_8360950).sum := by decide
  have hdescent : baseEnd_8360950 < baseStart_8360950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360953 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 4]
def baseStart_8360953 : Nat := 118140960795 + 8360953 * 2 ^ 59
def prefixEnd_8360953 : Nat := 4983230072969 + 3 ^ 40 * 8360953 * 2
def baseEnd_8360953 : Nat := 4293187618651131466636183

theorem tailTrace_8360953 : CollatzResearch.WordTrace tailWord_8360953 prefixEnd_8360953 4293187618651131466636183 := by
  unfold tailWord_8360953
  simp only [CollatzResearch.WordTrace]
  refine ⟨304949008478702692933631513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203299338985801795289087675 304949008478702692933631513)
  ·
    refine ⟨228711756359027019700223635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304949008478702692933631513 228711756359027019700223635)
    ·
      refine ⟨343067634538540529550335453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228711756359027019700223635 343067634538540529550335453)
      ·
        refine ⟨128650362951952698581375795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343067634538540529550335453 128650362951952698581375795)
        ·
          refine ⟨192975544427929047872063693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128650362951952698581375795 192975544427929047872063693)
          ·
            refine ⟨72365829160473392952023885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192975544427929047872063693 72365829160473392952023885)
            ·
              refine ⟨27137185935177522357008957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72365829160473392952023885 27137185935177522357008957)
              ·
                refine ⟨10176444725691570883878359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27137185935177522357008957 10176444725691570883878359)
                ·
                  refine ⟨15264667088537356325817539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10176444725691570883878359 15264667088537356325817539)
                  ·
                    refine ⟨22897000632806034488726309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15264667088537356325817539 22897000632806034488726309)
                    ·
                      refine ⟨4293187618651131466636183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22897000632806034488726309 4293187618651131466636183)
                      ·
                        rfl

theorem cell23_8360953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_8360953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360953 prefixEnd_8360953 := by exact prefixLift 8360953
  have htrace : WordTrace (prefixWord ++ tailWord_8360953) baseStart_8360953 baseEnd_8360953 := by
    simpa [prefixWord, tailWord_8360953, baseEnd_8360953] using wordTrace_append hprefix tailTrace_8360953
  have hstable : (prefixWord ++ tailWord_8360953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360953).length < 2 ^ (prefixWord ++ tailWord_8360953).sum := by decide
  have hdescent : baseEnd_8360953 < baseStart_8360953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360983 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_8360983 : Nat := 118140960795 + 8360983 * 2 ^ 59
def prefixEnd_8360983 : Nat := 4983230072969 + 3 ^ 40 * 8360983 * 2
def baseEnd_8360983 : Nat := 4293203023070766349261045

theorem tailTrace_8360983 : CollatzResearch.WordTrace tailWord_8360983 prefixEnd_8360983 4293203023070766349261045 := by
  unfold tailWord_8360983
  simp only [CollatzResearch.WordTrace]
  refine ⟨304950102668594008057223603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203300068445729338704815735 304950102668594008057223603)
  ·
    refine ⟨457425154002891012085835405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304950102668594008057223603 457425154002891012085835405)
    ·
      refine ⟨171534432751084129532188277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457425154002891012085835405 171534432751084129532188277)
      ·
        refine ⟨16081353070414137143642651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171534432751084129532188277 16081353070414137143642651)
        ·
          refine ⟨24122029605621205715463977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16081353070414137143642651 24122029605621205715463977)
          ·
            refine ⟨18091522204215904286597983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24122029605621205715463977 18091522204215904286597983)
            ·
              refine ⟨27137283306323856429896975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18091522204215904286597983 27137283306323856429896975)
              ·
                refine ⟨40705924959485784644845463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27137283306323856429896975 40705924959485784644845463)
                ·
                  refine ⟨61058887439228676967268195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40705924959485784644845463 61058887439228676967268195)
                  ·
                    refine ⟨91588331158843015450902293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61058887439228676967268195 91588331158843015450902293)
                    ·
                      refine ⟨4293203023070766349261045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91588331158843015450902293 4293203023070766349261045)
                      ·
                        rfl

theorem cell23_8360983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_8360983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360983 prefixEnd_8360983 := by exact prefixLift 8360983
  have htrace : WordTrace (prefixWord ++ tailWord_8360983) baseStart_8360983 baseEnd_8360983 := by
    simpa [prefixWord, tailWord_8360983, baseEnd_8360983] using wordTrace_append hprefix tailTrace_8360983
  have hstable : (prefixWord ++ tailWord_8360983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360983).length < 2 ^ (prefixWord ++ tailWord_8360983).sum := by decide
  have hdescent : baseEnd_8360983 < baseStart_8360983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8360993 : List Nat := [1, 2, 3, 2, 3, 1, 4, 7]
def baseStart_8360993 : Nat := 118140960795 + 8360993 * 2 ^ 59
def prefixEnd_8360993 : Nat := 4983230072969 + 3 ^ 40 * 8360993 * 2
def baseEnd_8360993 : Nat := 159007709551011530005037

theorem tailTrace_8360993 : CollatzResearch.WordTrace tailWord_8360993 prefixEnd_8360993 159007709551011530005037 := by
  unfold tailWord_8360993
  simp only [CollatzResearch.WordTrace]
  refine ⟨304950467398557779765087633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203300311599038519843391755 304950467398557779765087633)
  ·
    refine ⟨228712850548918334823815725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304950467398557779765087633 228712850548918334823815725)
    ·
      refine ⟨85767318955844375558930897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228712850548918334823815725 85767318955844375558930897)
      ·
        refine ⟨64325489216883281669198173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85767318955844375558930897 64325489216883281669198173)
        ·
          refine ⟨24122058456331230625949315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64325489216883281669198173 24122058456331230625949315)
          ·
            refine ⟨36183087684496845938923973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24122058456331230625949315 36183087684496845938923973)
            ·
              refine ⟨6784328940843158613548245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36183087684496845938923973 6784328940843158613548245)
              ·
                refine ⟨159007709551011530005037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6784328940843158613548245 159007709551011530005037)
                ·
                  rfl

theorem cell23_8360993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 7].length) (baseStart_8360993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8360993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8360993 prefixEnd_8360993 := by exact prefixLift 8360993
  have htrace : WordTrace (prefixWord ++ tailWord_8360993) baseStart_8360993 baseEnd_8360993 := by
    simpa [prefixWord, tailWord_8360993, baseEnd_8360993] using wordTrace_append hprefix tailTrace_8360993
  have hstable : (prefixWord ++ tailWord_8360993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8360993).length < 2 ^ (prefixWord ++ tailWord_8360993).sum := by decide
  have hdescent : baseEnd_8360993 < baseStart_8360993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8360993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361003 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 3]
def baseStart_8361003 : Nat := 118140960795 + 8361003 * 2 ^ 59
def prefixEnd_8361003 : Nat := 4983230072969 + 3 ^ 40 * 8361003 * 2
def baseEnd_8361003 : Nat := 4293213292683856271010953

theorem tailTrace_8361003 : CollatzResearch.WordTrace tailWord_8361003 prefixEnd_8361003 4293213292683856271010953 := by
  unfold tailWord_8361003
  simp only [CollatzResearch.WordTrace]
  refine ⟨304950832128521551472951663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203300554752347700981967775 304950832128521551472951663)
  ·
    refine ⟨457426248192782327209427495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304950832128521551472951663 457426248192782327209427495)
    ·
      refine ⟨686139372289173490814141243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457426248192782327209427495 686139372289173490814141243)
      ·
        refine ⟨1029209058433760236221211865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686139372289173490814141243 1029209058433760236221211865)
        ·
          refine ⟨771906793825320177165908899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1029209058433760236221211865 771906793825320177165908899)
          ·
            refine ⟨1157860190737980265748863349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771906793825320177165908899 1157860190737980265748863349)
            ·
              refine ⟨108549392881685649913955939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1157860190737980265748863349 108549392881685649913955939)
              ·
                refine ⟨162824089322528474870933909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108549392881685649913955939 162824089322528474870933909)
                ·
                  refine ⟨7632379186993522259575027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162824089322528474870933909 7632379186993522259575027)
                  ·
                    refine ⟨11448568780490283389362541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7632379186993522259575027 11448568780490283389362541)
                    ·
                      refine ⟨4293213292683856271010953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11448568780490283389362541 4293213292683856271010953)
                      ·
                        rfl

theorem cell23_8361003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 3].length) (baseStart_8361003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361003 prefixEnd_8361003 := by exact prefixLift 8361003
  have htrace : WordTrace (prefixWord ++ tailWord_8361003) baseStart_8361003 baseEnd_8361003 := by
    simpa [prefixWord, tailWord_8361003, baseEnd_8361003] using wordTrace_append hprefix tailTrace_8361003
  have hstable : (prefixWord ++ tailWord_8361003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361003).length < 2 ^ (prefixWord ++ tailWord_8361003).sum := by decide
  have hdescent : baseEnd_8361003 < baseStart_8361003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361020 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_8361020 : Nat := 118140960795 + 8361020 * 2 ^ 59
def prefixEnd_8361020 : Nat := 4983230072969 + 3 ^ 40 * 8361020 * 2
def baseEnd_8361020 : Nat := 4293222021854982704498375

theorem tailTrace_8361020 : CollatzResearch.WordTrace tailWord_8361020 prefixEnd_8361020 4293222021854982704498375 := by
  unfold tailWord_8361020
  simp only [CollatzResearch.WordTrace]
  refine ⟨152475726084729981688160257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203300968112973308917547009 152475726084729981688160257)
  ·
    refine ⟨114356794563547486266120193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152475726084729981688160257 114356794563547486266120193)
    ·
      refine ⟨85767595922660614699590145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114356794563547486266120193 85767595922660614699590145)
      ·
        refine ⟨64325696941995461024692609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85767595922660614699590145 64325696941995461024692609)
        ·
          refine ⟨48244272706496595768519457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64325696941995461024692609 48244272706496595768519457)
          ·
            refine ⟨36183204529872446826389593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48244272706496595768519457 36183204529872446826389593)
            ·
              refine ⟨27137403397404335119792195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36183204529872446826389593 27137403397404335119792195)
              ·
                refine ⟨40706105096106502679688293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27137403397404335119792195 40706105096106502679688293)
                ·
                  refine ⟨7632394705519969252441555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40706105096106502679688293 7632394705519969252441555)
                  ·
                    refine ⟨11448592058279953878662333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7632394705519969252441555 11448592058279953878662333)
                    ·
                      refine ⟨4293222021854982704498375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11448592058279953878662333 4293222021854982704498375)
                      ·
                        rfl

theorem cell23_8361020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_8361020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361020 prefixEnd_8361020 := by exact prefixLift 8361020
  have htrace : WordTrace (prefixWord ++ tailWord_8361020) baseStart_8361020 baseEnd_8361020 := by
    simpa [prefixWord, tailWord_8361020, baseEnd_8361020] using wordTrace_append hprefix tailTrace_8361020
  have hstable : (prefixWord ++ tailWord_8361020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361020).length < 2 ^ (prefixWord ++ tailWord_8361020).sum := by decide
  have hdescent : baseEnd_8361020 < baseStart_8361020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361021 : List Nat := [1, 4, 1, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_8361021 : Nat := 118140960795 + 8361021 * 2 ^ 59
def prefixEnd_8361021 : Nat := 4983230072969 + 3 ^ 40 * 8361021 * 2
def baseEnd_8361021 : Nat := 4293222535335637200585871

theorem tailTrace_8361021 : CollatzResearch.WordTrace tailWord_8361021 prefixEnd_8361021 4293222535335637200585871 := by
  unfold tailWord_8361021
  simp only [CollatzResearch.WordTrace]
  refine ⟨304951488642456340547106917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203300992428304227031404611 304951488642456340547106917)
  ·
    refine ⟨57178404120460563852582547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304951488642456340547106917 57178404120460563852582547)
    ·
      refine ⟨85767606180690845778873821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57178404120460563852582547 85767606180690845778873821)
      ·
        refine ⟨32162852317759067167077683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85767606180690845778873821 32162852317759067167077683)
        ·
          refine ⟨48244278476638600750616525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32162852317759067167077683 48244278476638600750616525)
          ·
            refine ⟨18091604428739475281481197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48244278476638600750616525 18091604428739475281481197)
            ·
              refine ⟨6784351660777303230555449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18091604428739475281481197 6784351660777303230555449)
              ·
                refine ⟨5088263745582977422916587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6784351660777303230555449 5088263745582977422916587)
                ·
                  refine ⟨7632395618374466134374881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5088263745582977422916587 7632395618374466134374881)
                  ·
                    refine ⟨5724296713780849600781161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7632395618374466134374881 5724296713780849600781161)
                    ·
                      refine ⟨4293222535335637200585871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724296713780849600781161 4293222535335637200585871)
                      ·
                        rfl

theorem cell23_8361021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_8361021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361021 prefixEnd_8361021 := by exact prefixLift 8361021
  have htrace : WordTrace (prefixWord ++ tailWord_8361021) baseStart_8361021 baseEnd_8361021 := by
    simpa [prefixWord, tailWord_8361021, baseEnd_8361021] using wordTrace_append hprefix tailTrace_8361021
  have hstable : (prefixWord ++ tailWord_8361021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361021).length < 2 ^ (prefixWord ++ tailWord_8361021).sum := by decide
  have hdescent : baseEnd_8361021 < baseStart_8361021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361036 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_8361036 : Nat := 118140960795 + 8361036 * 2 ^ 59
def prefixEnd_8361036 : Nat := 4983230072969 + 3 ^ 40 * 8361036 * 2
def baseEnd_8361036 : Nat := 1431076745848484880632767

theorem tailTrace_8361036 : CollatzResearch.WordTrace tailWord_8361036 prefixEnd_8361036 1431076745848484880632767 := by
  unfold tailWord_8361036
  simp only [CollatzResearch.WordTrace]
  refine ⟨152476017868700999054451481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203301357158267998739268641 152476017868700999054451481)
  ·
    refine ⟨114357013401525749290838611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152476017868700999054451481 114357013401525749290838611)
    ·
      refine ⟨171535520102288623936257917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114357013401525749290838611 171535520102288623936257917)
      ·
        refine ⟨64325820038358233976096719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171535520102288623936257917 64325820038358233976096719)
        ·
          refine ⟨96488730057537350964145079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64325820038358233976096719 96488730057537350964145079)
          ·
            refine ⟨144733095086306026446217619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96488730057537350964145079 144733095086306026446217619)
            ·
              refine ⟨217099642629459039669326429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144733095086306026446217619 217099642629459039669326429)
              ·
                refine ⟨81412365986047139875997411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217099642629459039669326429 81412365986047139875997411)
                ·
                  refine ⟨122118548979070709813996117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81412365986047139875997411 122118548979070709813996117)
                  ·
                    refine ⟨1431076745848484880632767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122118548979070709813996117 1431076745848484880632767)
                    ·
                      rfl

theorem cell23_8361036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_8361036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361036 prefixEnd_8361036 := by exact prefixLift 8361036
  have htrace : WordTrace (prefixWord ++ tailWord_8361036) baseStart_8361036 baseEnd_8361036 := by
    simpa [prefixWord, tailWord_8361036, baseEnd_8361036] using wordTrace_append hprefix tailTrace_8361036
  have hstable : (prefixWord ++ tailWord_8361036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361036).length < 2 ^ (prefixWord ++ tailWord_8361036).sum := by decide
  have hdescent : baseEnd_8361036 < baseStart_8361036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361054 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_8361054 : Nat := 118140960795 + 8361054 * 2 ^ 59
def prefixEnd_8361054 : Nat := 4983230072969 + 3 ^ 40 * 8361054 * 2
def baseEnd_8361054 : Nat := 4293239480197235571473219

theorem tailTrace_8361054 : CollatzResearch.WordTrace tailWord_8361054 prefixEnd_8361054 4293239480197235571473219 := by
  unfold tailWord_8361054
  simp only [CollatzResearch.WordTrace]
  refine ⟨38119086531417098397882277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203301794834224524788705477 38119086531417098397882277)
  ·
    refine ⟨7147328724640705949602927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38119086531417098397882277 7147328724640705949602927)
    ·
      refine ⟨10720993086961058924404391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7147328724640705949602927 10720993086961058924404391)
      ·
        refine ⟨16081489630441588386606587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720993086961058924404391 16081489630441588386606587)
        ·
          refine ⟨24122234445662382579909881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16081489630441588386606587 24122234445662382579909881)
          ·
            refine ⟨18091675834246786934932411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24122234445662382579909881 18091675834246786934932411)
            ·
              refine ⟨27137513751370180402398617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18091675834246786934932411 27137513751370180402398617)
              ·
                refine ⟨20353135313527635301798963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27137513751370180402398617 20353135313527635301798963)
                ·
                  refine ⟨30529702970291452952698445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20353135313527635301798963 30529702970291452952698445)
                  ·
                    refine ⟨11448638613859294857261917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30529702970291452952698445 11448638613859294857261917)
                    ·
                      refine ⟨4293239480197235571473219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11448638613859294857261917 4293239480197235571473219)
                      ·
                        rfl

theorem cell23_8361054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_8361054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361054 prefixEnd_8361054 := by exact prefixLift 8361054
  have htrace : WordTrace (prefixWord ++ tailWord_8361054) baseStart_8361054 baseEnd_8361054 := by
    simpa [prefixWord, tailWord_8361054, baseEnd_8361054] using wordTrace_append hprefix tailTrace_8361054
  have hstable : (prefixWord ++ tailWord_8361054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361054).length < 2 ^ (prefixWord ++ tailWord_8361054).sum := by decide
  have hdescent : baseEnd_8361054 < baseStart_8361054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361063 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_8361063 : Nat := 118140960795 + 8361063 * 2 ^ 59
def prefixEnd_8361063 : Nat := 4983230072969 + 3 ^ 40 * 8361063 * 2
def baseEnd_8361063 : Nat := 4293244101523126036260677

theorem tailTrace_8361063 : CollatzResearch.WordTrace tailWord_8361063 prefixEnd_8361063 4293244101523126036260677 := by
  unfold tailWord_8361063
  simp only [CollatzResearch.WordTrace]
  refine ⟨304953020508304181720135843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203302013672202787813423895 304953020508304181720135843)
  ·
    refine ⟨457429530762456272580203765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304953020508304181720135843 457429530762456272580203765)
    ·
      refine ⟨42884018508980275554394103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 457429530762456272580203765 42884018508980275554394103)
      ·
        refine ⟨64326027763470413331591155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42884018508980275554394103 64326027763470413331591155)
        ·
          refine ⟨96489041645205619997386733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64326027763470413331591155 96489041645205619997386733)
          ·
            refine ⟨36183390616952107499020025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96489041645205619997386733 36183390616952107499020025)
            ·
              refine ⟨27137542962714080624265019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36183390616952107499020025 27137542962714080624265019)
              ·
                refine ⟨40706314444071120936397529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27137542962714080624265019 40706314444071120936397529)
                ·
                  refine ⟨30529735833053340702298147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40706314444071120936397529 30529735833053340702298147)
                  ·
                    refine ⟨45794603749580011053447221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30529735833053340702298147 45794603749580011053447221)
                    ·
                      refine ⟨4293244101523126036260677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45794603749580011053447221 4293244101523126036260677)
                      ·
                        rfl

theorem cell23_8361063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_8361063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361063 prefixEnd_8361063 := by exact prefixLift 8361063
  have htrace : WordTrace (prefixWord ++ tailWord_8361063) baseStart_8361063 baseEnd_8361063 := by
    simpa [prefixWord, tailWord_8361063, baseEnd_8361063] using wordTrace_append hprefix tailTrace_8361063
  have hstable : (prefixWord ++ tailWord_8361063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361063).length < 2 ^ (prefixWord ++ tailWord_8361063).sum := by decide
  have hdescent : baseEnd_8361063 < baseStart_8361063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361150 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_8361150 : Nat := 118140960795 + 8361150 * 2 ^ 59
def prefixEnd_8361150 : Nat := 4983230072969 + 3 ^ 40 * 8361150 * 2
def baseEnd_8361150 : Nat := 4293288774340067195872777

theorem tailTrace_8361150 : CollatzResearch.WordTrace tailWord_8361150 prefixEnd_8361150 4293288774340067195872777 := by
  unfold tailWord_8361150
  simp only [CollatzResearch.WordTrace]
  refine ⟨38119524207373624447319113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203304129105992663719035269 38119524207373624447319113)
  ·
    refine ⟨28589643155530218335489335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38119524207373624447319113 28589643155530218335489335)
    ·
      refine ⟨42884464733295327503234003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28589643155530218335489335 42884464733295327503234003)
      ·
        refine ⟨64326697099942991254851005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42884464733295327503234003 64326697099942991254851005)
        ·
          refine ⟨24122511412478621720569127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64326697099942991254851005 24122511412478621720569127)
          ·
            refine ⟨36183767118717932580853691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24122511412478621720569127 36183767118717932580853691)
            ·
              refine ⟨54275650678076898871280537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36183767118717932580853691 54275650678076898871280537)
              ·
                refine ⟨40706738008557674153460403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54275650678076898871280537 40706738008557674153460403)
                ·
                  refine ⟨61060107012836511230190605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40706738008557674153460403 61060107012836511230190605)
                  ·
                    refine ⟨22897540129813691711321477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61060107012836511230190605 22897540129813691711321477)
                    ·
                      refine ⟨4293288774340067195872777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22897540129813691711321477 4293288774340067195872777)
                      ·
                        rfl

theorem cell23_8361150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_8361150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361150 prefixEnd_8361150 := by exact prefixLift 8361150
  have htrace : WordTrace (prefixWord ++ tailWord_8361150) baseStart_8361150 baseEnd_8361150 := by
    simpa [prefixWord, tailWord_8361150, baseEnd_8361150] using wordTrace_append hprefix tailTrace_8361150
  have hstable : (prefixWord ++ tailWord_8361150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361150).length < 2 ^ (prefixWord ++ tailWord_8361150).sum := by decide
  have hdescent : baseEnd_8361150 < baseStart_8361150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361160 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 3, 4]
def baseStart_8361160 : Nat := 118140960795 + 8361160 * 2 ^ 59
def prefixEnd_8361160 : Nat := 4983230072969 + 3 ^ 40 * 8361160 * 2
def baseEnd_8361160 : Nat := 1431097969715537385582577

theorem tailTrace_8361160 : CollatzResearch.WordTrace tailWord_8361160 prefixEnd_8361160 1431097969715537385582577 := by
  unfold tailWord_8361160
  simp only [CollatzResearch.WordTrace]
  refine ⟨152478279194476383643208467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203304372259301844857611289 152478279194476383643208467)
  ·
    refine ⟨228717418791714575464812701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152478279194476383643208467 228717418791714575464812701)
    ·
      refine ⟨85769032046892965799304763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228717418791714575464812701 85769032046892965799304763)
      ·
        refine ⟨128653548070339448698957145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85769032046892965799304763 128653548070339448698957145)
        ·
          refine ⟨96490161052754586524217859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128653548070339448698957145 96490161052754586524217859)
          ·
            refine ⟨144735241579131879786326789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96490161052754586524217859 144735241579131879786326789)
            ·
              refine ⟨27137857796087227459936273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144735241579131879786326789 27137857796087227459936273)
              ·
                refine ⟨20353393347065420594952205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27137857796087227459936273 20353393347065420594952205)
                ·
                  refine ⟨7632522505149532723107077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20353393347065420594952205 7632522505149532723107077)
                  ·
                    refine ⟨1431097969715537385582577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7632522505149532723107077 1431097969715537385582577)
                    ·
                      rfl

theorem cell23_8361160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_8361160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361160 prefixEnd_8361160 := by exact prefixLift 8361160
  have htrace : WordTrace (prefixWord ++ tailWord_8361160) baseStart_8361160 baseEnd_8361160 := by
    simpa [prefixWord, tailWord_8361160, baseEnd_8361160] using wordTrace_append hprefix tailTrace_8361160
  have hstable : (prefixWord ++ tailWord_8361160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361160).length < 2 ^ (prefixWord ++ tailWord_8361160).sum := by decide
  have hdescent : baseEnd_8361160 < baseStart_8361160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361170 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_8361170 : Nat := 118140960795 + 8361170 * 2 ^ 59
def prefixEnd_8361170 : Nat := 4983230072969 + 3 ^ 40 * 8361170 * 2
def baseEnd_8361170 : Nat := 4293299043953157117622685

theorem tailTrace_8361170 : CollatzResearch.WordTrace tailWord_8361170 prefixEnd_8361170 4293299043953157117622685 := by
  unfold tailWord_8361170
  simp only [CollatzResearch.WordTrace]
  refine ⟨76239230779729134748570241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203304615412611025996187309 76239230779729134748570241)
  ·
    refine ⟨57179423084796851061427681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76239230779729134748570241 57179423084796851061427681)
    ·
      refine ⟨42884567313597638296070761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57179423084796851061427681 42884567313597638296070761)
      ·
        refine ⟨32163425485198228722053071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42884567313597638296070761 32163425485198228722053071)
        ·
          refine ⟨48245138227797343083079607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32163425485198228722053071 48245138227797343083079607)
          ·
            refine ⟨72367707341696014624619411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48245138227797343083079607 72367707341696014624619411)
            ·
              refine ⟨108551561012544021936929117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72367707341696014624619411 108551561012544021936929117)
              ·
                refine ⟨40706835379704008226348419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108551561012544021936929117 40706835379704008226348419)
                ·
                  refine ⟨61060253069556012339522629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40706835379704008226348419 61060253069556012339522629)
                  ·
                    refine ⟨11448797450541752313660493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61060253069556012339522629 11448797450541752313660493)
                    ·
                      refine ⟨4293299043953157117622685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11448797450541752313660493 4293299043953157117622685)
                      ·
                        rfl

theorem cell23_8361170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_8361170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361170 prefixEnd_8361170 := by exact prefixLift 8361170
  have htrace : WordTrace (prefixWord ++ tailWord_8361170) baseStart_8361170 baseEnd_8361170 := by
    simpa [prefixWord, tailWord_8361170, baseEnd_8361170] using wordTrace_append hprefix tailTrace_8361170
  have hstable : (prefixWord ++ tailWord_8361170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361170).length < 2 ^ (prefixWord ++ tailWord_8361170).sum := by decide
  have hdescent : baseEnd_8361170 < baseStart_8361170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361227 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 2, 3, 2]
def baseStart_8361227 : Nat := 118140960795 + 8361227 * 2 ^ 59
def prefixEnd_8361227 : Nat := 4983230072969 + 3 ^ 40 * 8361227 * 2
def baseEnd_8361227 : Nat := 4293328312350463394609923

theorem tailTrace_8361227 : CollatzResearch.WordTrace tailWord_8361227 prefixEnd_8361227 4293328312350463394609923 := by
  unfold tailWord_8361227
  simp only [CollatzResearch.WordTrace]
  refine ⟨304959002079710037729105935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203306001386473358486070623 304959002079710037729105935)
  ·
    refine ⟨457438503119565056593658903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304959002079710037729105935 457438503119565056593658903)
    ·
      refine ⟨686157754679347584890488355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457438503119565056593658903 686157754679347584890488355)
      ·
        refine ⟨1029236632019021377335732533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686157754679347584890488355 1029236632019021377335732533)
        ·
          refine ⟨96490934251783254125224925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1029236632019021377335732533 96490934251783254125224925)
          ·
            refine ⟨36184100344418720296959347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96490934251783254125224925 36184100344418720296959347)
            ·
              refine ⟨54276150516628080445439021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36184100344418720296959347 54276150516628080445439021)
              ·
                refine ⟨20353556443735530167039633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54276150516628080445439021 20353556443735530167039633)
                ·
                  refine ⟨15265167332801647625279725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20353556443735530167039633 15265167332801647625279725)
                  ·
                    refine ⟨5724437749800617859479897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15265167332801647625279725 5724437749800617859479897)
                    ·
                      refine ⟨4293328312350463394609923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724437749800617859479897 4293328312350463394609923)
                      ·
                        rfl

theorem cell23_8361227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 3, 2].length) (baseStart_8361227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361227 prefixEnd_8361227 := by exact prefixLift 8361227
  have htrace : WordTrace (prefixWord ++ tailWord_8361227) baseStart_8361227 baseEnd_8361227 := by
    simpa [prefixWord, tailWord_8361227, baseEnd_8361227] using wordTrace_append hprefix tailTrace_8361227
  have hstable : (prefixWord ++ tailWord_8361227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361227).length < 2 ^ (prefixWord ++ tailWord_8361227).sum := by decide
  have hdescent : baseEnd_8361227 < baseStart_8361227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361251 : List Nat := [1, 1, 1, 4, 2, 3, 4, 2, 1, 1, 3]
def baseStart_8361251 : Nat := 118140960795 + 8361251 * 2 ^ 59
def prefixEnd_8361251 : Nat := 4983230072969 + 3 ^ 40 * 8361251 * 2
def baseEnd_8361251 : Nat := 4293340635886171300709813

theorem tailTrace_8361251 : CollatzResearch.WordTrace tailWord_8361251 prefixEnd_8361251 4293340635886171300709813 := by
  unfold tailWord_8361251
  simp only [CollatzResearch.WordTrace]
  refine ⟨304959877431623089827979607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203306584954415393218653071 304959877431623089827979607)
  ·
    refine ⟨457439816147434634741969411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304959877431623089827979607 457439816147434634741969411)
    ·
      refine ⟨686159724221151952112954117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457439816147434634741969411 686159724221151952112954117)
      ·
        refine ⟨128654948291465991021178897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 686159724221151952112954117 128654948291465991021178897)
        ·
          refine ⟨96491211218599493265884173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128654948291465991021178897 96491211218599493265884173)
          ·
            refine ⟨36184204206974809974706565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96491211218599493265884173 36184204206974809974706565)
            ·
              refine ⟨6784538288807776870257481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36184204206974809974706565 6784538288807776870257481)
              ·
                refine ⟨5088403716605832652693111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6784538288807776870257481 5088403716605832652693111)
                ·
                  refine ⟨7632605574908748979039667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5088403716605832652693111 7632605574908748979039667)
                  ·
                    refine ⟨11448908362363123468559501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7632605574908748979039667 11448908362363123468559501)
                    ·
                      refine ⟨4293340635886171300709813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11448908362363123468559501 4293340635886171300709813)
                      ·
                        rfl

theorem cell23_8361251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_8361251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361251 prefixEnd_8361251 := by exact prefixLift 8361251
  have htrace : WordTrace (prefixWord ++ tailWord_8361251) baseStart_8361251 baseEnd_8361251 := by
    simpa [prefixWord, tailWord_8361251, baseEnd_8361251] using wordTrace_append hprefix tailTrace_8361251
  have hstable : (prefixWord ++ tailWord_8361251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361251).length < 2 ^ (prefixWord ++ tailWord_8361251).sum := by decide
  have hdescent : baseEnd_8361251 < baseStart_8361251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361267 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 2, 4]
def baseStart_8361267 : Nat := 118140960795 + 8361267 * 2 ^ 59
def prefixEnd_8361267 : Nat := 4983230072969 + 3 ^ 40 * 8361267 * 2
def baseEnd_8361267 : Nat := 1431116283858881079369913

theorem tailTrace_8361267 : CollatzResearch.WordTrace tailWord_8361267 prefixEnd_8361267 1431116283858881079369913 := by
  unfold tailWord_8361267
  simp only [CollatzResearch.WordTrace]
  refine ⟨304960460999565124560562055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203306973999710083040374703 304960460999565124560562055)
  ·
    refine ⟨457440691499347686840843083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304960460999565124560562055 457440691499347686840843083)
    ·
      refine ⟨686161037249021530261264625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457440691499347686840843083 686161037249021530261264625)
      ·
        refine ⟨514620777936766147695948469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686161037249021530261264625 514620777936766147695948469)
        ·
          refine ⟨48245697931571826346495169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 514620777936766147695948469 48245697931571826346495169)
          ·
            refine ⟨36184273448678869759871377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48245697931571826346495169 36184273448678869759871377)
            ·
              refine ⟨27138205086509152319903533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36184273448678869759871377 27138205086509152319903533)
              ·
                refine ⟨10176826907440932119963825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27138205086509152319903533 10176826907440932119963825)
                ·
                  refine ⟨7632620180580699089972869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10176826907440932119963825 7632620180580699089972869)
                  ·
                    refine ⟨1431116283858881079369913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7632620180580699089972869 1431116283858881079369913)
                    ·
                      rfl

theorem cell23_8361267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 4].length) (baseStart_8361267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361267 prefixEnd_8361267 := by exact prefixLift 8361267
  have htrace : WordTrace (prefixWord ++ tailWord_8361267) baseStart_8361267 baseEnd_8361267 := by
    simpa [prefixWord, tailWord_8361267, baseEnd_8361267] using wordTrace_append hprefix tailTrace_8361267
  have hstable : (prefixWord ++ tailWord_8361267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361267).length < 2 ^ (prefixWord ++ tailWord_8361267).sum := by decide
  have hdescent : baseEnd_8361267 < baseStart_8361267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361274 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2]
def baseStart_8361274 : Nat := 118140960795 + 8361274 * 2 ^ 59
def prefixEnd_8361274 : Nat := 4983230072969 + 3 ^ 40 * 8361274 * 2
def baseEnd_8361274 : Nat := 4293352445941224710722207

theorem tailTrace_8361274 : CollatzResearch.WordTrace tailWord_8361274 prefixEnd_8361274 4293352445941224710722207 := by
  unfold tailWord_8361274
  simp only [CollatzResearch.WordTrace]
  refine ⟨76240179077634941189016719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203307144207026509837377917 76240179077634941189016719)
  ·
    refine ⟨114360268616452411783525079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76240179077634941189016719 114360268616452411783525079)
    ·
      refine ⟨171540402924678617675287619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114360268616452411783525079 171540402924678617675287619)
      ·
        refine ⟨257310604387017926512931429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171540402924678617675287619 257310604387017926512931429)
        ·
          refine ⟨48245738322565861221174643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257310604387017926512931429 48245738322565861221174643)
          ·
            refine ⟨72368607483848791831761965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48245738322565861221174643 72368607483848791831761965)
            ·
              refine ⟨27138227806443296936910737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72368607483848791831761965 27138227806443296936910737)
              ·
                refine ⟨20353670854832472702683053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27138227806443296936910737 20353670854832472702683053)
                ·
                  refine ⟨7632626570562177263506145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20353670854832472702683053 7632626570562177263506145)
                  ·
                    refine ⟨5724469927921632947629609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7632626570562177263506145 5724469927921632947629609)
                    ·
                      refine ⟨4293352445941224710722207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724469927921632947629609 4293352445941224710722207)
                      ·
                        rfl

theorem cell23_8361274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_8361274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361274 prefixEnd_8361274 := by exact prefixLift 8361274
  have htrace : WordTrace (prefixWord ++ tailWord_8361274) baseStart_8361274 baseEnd_8361274 := by
    simpa [prefixWord, tailWord_8361274, baseEnd_8361274] using wordTrace_append hprefix tailTrace_8361274
  have hstable : (prefixWord ++ tailWord_8361274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361274).length < 2 ^ (prefixWord ++ tailWord_8361274).sum := by decide
  have hdescent : baseEnd_8361274 < baseStart_8361274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361280 : List Nat := [2, 1, 1, 2, 2, 1, 7, 7]
def baseStart_8361280 : Nat := 118140960795 + 8361280 * 2 ^ 59
def prefixEnd_8361280 : Nat := 4983230072969 + 3 ^ 40 * 8361280 * 2
def baseEnd_8361280 : Nat := 159013167660190803231377

theorem tailTrace_8361280 : CollatzResearch.WordTrace tailWord_8361280 prefixEnd_8361280 159013167660190803231377 := by
  unfold tailWord_8361280
  simp only [CollatzResearch.WordTrace]
  refine ⟨152480467574259013890392647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203307290099012018520523529 152480467574259013890392647)
  ·
    refine ⟨228720701361388520835588971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152480467574259013890392647 228720701361388520835588971)
    ·
      refine ⟨343081052042082781253383457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228720701361388520835588971 343081052042082781253383457)
      ·
        refine ⟨257310789031562085940037593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343081052042082781253383457 257310789031562085940037593)
        ·
          refine ⟨192983091773671564455028195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257310789031562085940037593 192983091773671564455028195)
          ·
            refine ⟨289474637660507346682542293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192983091773671564455028195 289474637660507346682542293)
            ·
              refine ⟨6784561820168140937872085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 289474637660507346682542293 6784561820168140937872085)
              ·
                refine ⟨159013167660190803231377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6784561820168140937872085 159013167660190803231377)
                ·
                  rfl

theorem cell23_8361280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 7].length) (baseStart_8361280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361280 prefixEnd_8361280 := by exact prefixLift 8361280
  have htrace : WordTrace (prefixWord ++ tailWord_8361280) baseStart_8361280 baseEnd_8361280 := by
    simpa [prefixWord, tailWord_8361280, baseEnd_8361280] using wordTrace_append hprefix tailTrace_8361280
  have hstable : (prefixWord ++ tailWord_8361280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361280).length < 2 ^ (prefixWord ++ tailWord_8361280).sum := by decide
  have hdescent : baseEnd_8361280 < baseStart_8361280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361324 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_8361324 : Nat := 118140960795 + 8361324 * 2 ^ 59
def prefixEnd_8361324 : Nat := 4983230072969 + 3 ^ 40 * 8361324 * 2
def baseEnd_8361324 : Nat := 4293378119973949515096977

theorem tailTrace_8361324 : CollatzResearch.WordTrace tailWord_8361324 prefixEnd_8361324 4293378119973949515096977 := by
  unfold tailWord_8361324
  simp only [CollatzResearch.WordTrace]
  refine ⟨152481269980179311647693513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203308359973572415530258017 152481269980179311647693513)
  ·
    refine ⟨114360952485134483735770135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152481269980179311647693513 114360952485134483735770135)
    ·
      refine ⟨171541428727701725603655203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114360952485134483735770135 171541428727701725603655203)
      ·
        refine ⟨257312143091552588405482805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171541428727701725603655203 257312143091552588405482805)
        ·
          refine ⟨24123013414833055163014013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257312143091552588405482805 24123013414833055163014013)
          ·
            refine ⟨9046130030562395686130255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24123013414833055163014013 9046130030562395686130255)
            ·
              refine ⟨13569195045843593529195383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046130030562395686130255 13569195045843593529195383)
              ·
                refine ⟨20353792568765390293793075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13569195045843593529195383 20353792568765390293793075)
                ·
                  refine ⟨30530688853148085440689613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20353792568765390293793075 30530688853148085440689613)
                  ·
                    refine ⟨11449008319930532040258605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30530688853148085440689613 11449008319930532040258605)
                    ·
                      refine ⟨4293378119973949515096977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11449008319930532040258605 4293378119973949515096977)
                      ·
                        rfl

theorem cell23_8361324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_8361324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361324 prefixEnd_8361324 := by exact prefixLift 8361324
  have htrace : WordTrace (prefixWord ++ tailWord_8361324) baseStart_8361324 baseEnd_8361324 := by
    simpa [prefixWord, tailWord_8361324, baseEnd_8361324] using wordTrace_append hprefix tailTrace_8361324
  have hstable : (prefixWord ++ tailWord_8361324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361324).length < 2 ^ (prefixWord ++ tailWord_8361324).sum := by decide
  have hdescent : baseEnd_8361324 < baseStart_8361324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361400 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 1, 7]
def baseStart_8361400 : Nat := 118140960795 + 8361400 * 2 ^ 59
def prefixEnd_8361400 : Nat := 4983230072969 + 3 ^ 40 * 8361400 * 2
def baseEnd_8361400 : Nat := 1431139048167897072582209

theorem tailTrace_8361400 : CollatzResearch.WordTrace tailWord_8361400 prefixEnd_8361400 1431139048167897072582209 := by
  unfold tailWord_8361400
  simp only [CollatzResearch.WordTrace]
  refine ⟨152482655954041644137576827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203310207938722192183435769 152482655954041644137576827)
  ·
    refine ⟨228723983931062466206365241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152482655954041644137576827 228723983931062466206365241)
    ·
      refine ⟨171542987948296849654773931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228723983931062466206365241 171542987948296849654773931)
      ·
        refine ⟨257314481922445274482160897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171542987948296849654773931 257314481922445274482160897)
        ·
          refine ⟨192985861441833955861620673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257314481922445274482160897 192985861441833955861620673)
          ·
            refine ⟨144739396081375466896215505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192985861441833955861620673 144739396081375466896215505)
            ·
              refine ⟨108554547061031600172161629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144739396081375466896215505 108554547061031600172161629)
              ·
                refine ⟨40707955147886850064560611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108554547061031600172161629 40707955147886850064560611)
                ·
                  refine ⟨61061932721830275096840917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40707955147886850064560611 61061932721830275096840917)
                  ·
                    refine ⟨1431139048167897072582209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61061932721830275096840917 1431139048167897072582209)
                    ·
                      rfl

theorem cell23_8361400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_8361400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361400 prefixEnd_8361400 := by exact prefixLift 8361400
  have htrace : WordTrace (prefixWord ++ tailWord_8361400) baseStart_8361400 baseEnd_8361400 := by
    simpa [prefixWord, tailWord_8361400, baseEnd_8361400] using wordTrace_append hprefix tailTrace_8361400
  have hstable : (prefixWord ++ tailWord_8361400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361400).length < 2 ^ (prefixWord ++ tailWord_8361400).sum := by decide
  have hdescent : baseEnd_8361400 < baseStart_8361400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361407 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 4, 5, 2]
def baseStart_8361407 : Nat := 118140960795 + 8361407 * 2 ^ 59
def prefixEnd_8361407 : Nat := 4983230072969 + 3 ^ 40 * 8361407 * 2
def baseEnd_8361407 : Nat := 4293420738868272690359095

theorem tailTrace_8361407 : CollatzResearch.WordTrace tailWord_8361407 prefixEnd_8361407 4293420738868272690359095 := by
  unfold tailWord_8361407
  simp only [CollatzResearch.WordTrace]
  refine ⟨304965567219057928470658475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203310378146038618980438983 304965567219057928470658475)
  ·
    refine ⟨457448350828586892705987713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304965567219057928470658475 457448350828586892705987713)
    ·
      refine ⟨343086263121440169529490785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457448350828586892705987713 343086263121440169529490785)
      ·
        refine ⟨257314697341080127147118089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343086263121440169529490785 257314697341080127147118089)
        ·
          refine ⟨192986023005810095360338567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257314697341080127147118089 192986023005810095360338567)
          ·
            refine ⟨289479034508715143040507851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192986023005810095360338567 289479034508715143040507851)
            ·
              refine ⟨434218551763072714560761777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289479034508715143040507851 434218551763072714560761777)
              ·
                refine ⟨325663913822304535920571333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434218551763072714560761777 325663913822304535920571333)
                ·
                  refine ⟨61061983841682100485107125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325663913822304535920571333 61061983841682100485107125)
                  ·
                    refine ⟨5724560985157696920478793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61061983841682100485107125 5724560985157696920478793)
                    ·
                      refine ⟨4293420738868272690359095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724560985157696920478793 4293420738868272690359095)
                      ·
                        rfl

theorem cell23_8361407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_8361407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361407 prefixEnd_8361407 := by exact prefixLift 8361407
  have htrace : WordTrace (prefixWord ++ tailWord_8361407) baseStart_8361407 baseEnd_8361407 := by
    simpa [prefixWord, tailWord_8361407, baseEnd_8361407] using wordTrace_append hprefix tailTrace_8361407
  have hstable : (prefixWord ++ tailWord_8361407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361407).length < 2 ^ (prefixWord ++ tailWord_8361407).sum := by decide
  have hdescent : baseEnd_8361407 < baseStart_8361407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361454 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_8361454 : Nat := 118140960795 + 8361454 * 2 ^ 59
def prefixEnd_8361454 : Nat := 4983230072969 + 3 ^ 40 * 8361454 * 2
def baseEnd_8361454 : Nat := 4293444872459034006471379

theorem tailTrace_8361454 : CollatzResearch.WordTrace tailWord_8361454 prefixEnd_8361454 4293444872459034006471379 := by
  unfold tailWord_8361454
  simp only [CollatzResearch.WordTrace]
  refine ⟨38120910181235956937202427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203311520966591770331746277 38120910181235956937202427)
  ·
    refine ⟨57181365271853935405803641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38120910181235956937202427 57181365271853935405803641)
    ·
      refine ⟨42886023953890451554352731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57181365271853935405803641 42886023953890451554352731)
      ·
        refine ⟨64329035930835677331529097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42886023953890451554352731 64329035930835677331529097)
        ·
          refine ⟨48246776948126757998646823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64329035930835677331529097 48246776948126757998646823)
          ·
            refine ⟨72370165422190136997970235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48246776948126757998646823 72370165422190136997970235)
            ·
              refine ⟨108555248133285205496955353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72370165422190136997970235 108555248133285205496955353)
              ·
                refine ⟨81416436099963904122716515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108555248133285205496955353 81416436099963904122716515)
                ·
                  refine ⟨122124654149945856184074773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81416436099963904122716515 122124654149945856184074773)
                  ·
                    refine ⟨5724593163278712008628505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122124654149945856184074773 5724593163278712008628505)
                    ·
                      refine ⟨4293444872459034006471379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724593163278712008628505 4293444872459034006471379)
                      ·
                        rfl

theorem cell23_8361454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_8361454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361454 prefixEnd_8361454 := by exact prefixLift 8361454
  have htrace : WordTrace (prefixWord ++ tailWord_8361454) baseStart_8361454 baseEnd_8361454 := by
    simpa [prefixWord, tailWord_8361454, baseEnd_8361454] using wordTrace_append hprefix tailTrace_8361454
  have hstable : (prefixWord ++ tailWord_8361454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361454).length < 2 ^ (prefixWord ++ tailWord_8361454).sum := by decide
  have hdescent : baseEnd_8361454 < baseStart_8361454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361547 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 3]
def baseStart_8361547 : Nat := 118140960795 + 8361547 * 2 ^ 59
def prefixEnd_8361547 : Nat := 4983230072969 + 3 ^ 40 * 8361547 * 2
def baseEnd_8361547 : Nat := 4293492626159902142608451

theorem tailTrace_8361547 : CollatzResearch.WordTrace tailWord_8361547 prefixEnd_8361547 4293492626159902142608451 := by
  unfold tailWord_8361547
  simp only [CollatzResearch.WordTrace]
  refine ⟨304970673438550732380754895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203313782292367154920503263 304970673438550732380754895)
  ·
    refine ⟨457456010157826098571132343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304970673438550732380754895 457456010157826098571132343)
    ·
      refine ⟨686184015236739147856698515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457456010157826098571132343 686184015236739147856698515)
      ·
        refine ⟨1029276022855108721785047773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686184015236739147856698515 1029276022855108721785047773)
        ·
          refine ⟨385978508570665770669392915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1029276022855108721785047773 385978508570665770669392915)
          ·
            refine ⟨578967762855998656004089373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385978508570665770669392915 578967762855998656004089373)
            ·
              refine ⟨217112911070999496001533515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 578967762855998656004089373 217112911070999496001533515)
              ·
                refine ⟨325669366606499244002300273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217112911070999496001533515 325669366606499244002300273)
                ·
                  refine ⟨244252024954874433001725205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325669366606499244002300273 244252024954874433001725205)
                  ·
                    refine ⟨11449313669759739046955869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 244252024954874433001725205 11449313669759739046955869)
                    ·
                      refine ⟨4293492626159902142608451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11449313669759739046955869 4293492626159902142608451)
                      ·
                        rfl

theorem cell23_8361547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 3].length) (baseStart_8361547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361547 prefixEnd_8361547 := by exact prefixLift 8361547
  have htrace : WordTrace (prefixWord ++ tailWord_8361547) baseStart_8361547 baseEnd_8361547 := by
    simpa [prefixWord, tailWord_8361547, baseEnd_8361547] using wordTrace_append hprefix tailTrace_8361547
  have hstable : (prefixWord ++ tailWord_8361547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361547).length < 2 ^ (prefixWord ++ tailWord_8361547).sum := by decide
  have hdescent : baseEnd_8361547 < baseStart_8361547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361561 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 3, 2, 2]
def baseStart_8361561 : Nat := 118140960795 + 8361561 * 2 ^ 59
def prefixEnd_8361561 : Nat := 4983230072969 + 3 ^ 40 * 8361561 * 2
def baseEnd_8361561 : Nat := 4293499814889065087833387

theorem tailTrace_8361561 : CollatzResearch.WordTrace tailWord_8361561 prefixEnd_8361561 4293499814889065087833387 := by
  unfold tailWord_8361561
  simp only [CollatzResearch.WordTrace]
  refine ⟨304971184060500012771764537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203314122707000008514509691 304971184060500012771764537)
  ·
    refine ⟨228728388045375009578823403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304971184060500012771764537 228728388045375009578823403)
    ·
      refine ⟨343092582068062514368235105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228728388045375009578823403 343092582068062514368235105)
      ·
        refine ⟨257319436551046885776176329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343092582068062514368235105 257319436551046885776176329)
        ·
          refine ⟨192989577413285164332132247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257319436551046885776176329 192989577413285164332132247)
          ·
            refine ⟨289484366119927746498198371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192989577413285164332132247 289484366119927746498198371)
            ·
              refine ⟨434226549179891619747297557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289484366119927746498198371 434226549179891619747297557)
              ·
                refine ⟨20354369492807419675654573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 434226549179891619747297557 20354369492807419675654573)
                ·
                  refine ⟨7632888559802782378370465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20354369492807419675654573 7632888559802782378370465)
                  ·
                    refine ⟨5724666419852086783777849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7632888559802782378370465 5724666419852086783777849)
                    ·
                      refine ⟨4293499814889065087833387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724666419852086783777849 4293499814889065087833387)
                      ·
                        rfl

theorem cell23_8361561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_8361561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361561 prefixEnd_8361561 := by exact prefixLift 8361561
  have htrace : WordTrace (prefixWord ++ tailWord_8361561) baseStart_8361561 baseEnd_8361561 := by
    simpa [prefixWord, tailWord_8361561, baseEnd_8361561] using wordTrace_append hprefix tailTrace_8361561
  have hstable : (prefixWord ++ tailWord_8361561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361561).length < 2 ^ (prefixWord ++ tailWord_8361561).sum := by decide
  have hdescent : baseEnd_8361561 < baseStart_8361561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361578 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_8361578 : Nat := 118140960795 + 8361578 * 2 ^ 59
def prefixEnd_8361578 : Nat := 4983230072969 + 3 ^ 40 * 8361578 * 2
def baseEnd_8361578 : Nat := 4293508544060191521320809

theorem tailTrace_8361578 : CollatzResearch.WordTrace tailWord_8361578 prefixEnd_8361578 4293508544060191521320809 := by
  unfold tailWord_8361578
  simp only [CollatzResearch.WordTrace]
  refine ⟨76242951025359606168783347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203314536067625616450088925 76242951025359606168783347)
  ·
    refine ⟨114364426538039409253175021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76242951025359606168783347 114364426538039409253175021)
    ·
      refine ⟨42886659951764778469940633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114364426538039409253175021 42886659951764778469940633)
      ·
        refine ⟨32164994963823583852455475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42886659951764778469940633 32164994963823583852455475)
        ·
          refine ⟨48247492445735375778683213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32164994963823583852455475 48247492445735375778683213)
          ·
            refine ⟨18092809667150765917006205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48247492445735375778683213 18092809667150765917006205)
            ·
              refine ⟨6784803625181537218877327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18092809667150765917006205 6784803625181537218877327)
              ·
                refine ⟨10177205437772305828315991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784803625181537218877327 10177205437772305828315991)
                ·
                  refine ⟨15265808156658458742473987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10177205437772305828315991 15265808156658458742473987)
                  ·
                    refine ⟨22898712234987688113710981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15265808156658458742473987 22898712234987688113710981)
                    ·
                      refine ⟨4293508544060191521320809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22898712234987688113710981 4293508544060191521320809)
                      ·
                        rfl

theorem cell23_8361578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_8361578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361578 prefixEnd_8361578 := by exact prefixLift 8361578
  have htrace : WordTrace (prefixWord ++ tailWord_8361578) baseStart_8361578 baseEnd_8361578 := by
    simpa [prefixWord, tailWord_8361578, baseEnd_8361578] using wordTrace_append hprefix tailTrace_8361578
  have hstable : (prefixWord ++ tailWord_8361578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361578).length < 2 ^ (prefixWord ++ tailWord_8361578).sum := by decide
  have hdescent : baseEnd_8361578 < baseStart_8361578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361608 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_8361608 : Nat := 118140960795 + 8361608 * 2 ^ 59
def prefixEnd_8361608 : Nat := 4983230072969 + 3 ^ 40 * 8361608 * 2
def baseEnd_8361608 : Nat := 4293523948479826403945671

theorem tailTrace_8361608 : CollatzResearch.WordTrace tailWord_8361608 prefixEnd_8361608 4293523948479826403945671 := by
  unfold tailWord_8361608
  simp only [CollatzResearch.WordTrace]
  refine ⟨152486449145664869899362739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203315265527553159865816985 152486449145664869899362739)
  ·
    refine ⟨228729673718497304849044109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152486449145664869899362739 228729673718497304849044109)
    ·
      refine ⟨85773627644436489318391541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228729673718497304849044109 85773627644436489318391541)
      ·
        refine ⟨8041277591665920873599207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85773627644436489318391541 8041277591665920873599207)
        ·
          refine ⟨12061916387498881310398811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041277591665920873599207 12061916387498881310398811)
          ·
            refine ⟨18092874581248321965598217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12061916387498881310398811 18092874581248321965598217)
            ·
              refine ⟨13569655935936241474198663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18092874581248321965598217 13569655935936241474198663)
              ·
                refine ⟨20354483903904362211297995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13569655935936241474198663 20354483903904362211297995)
                ·
                  refine ⟨30531725855856543316946993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20354483903904362211297995 30531725855856543316946993)
                  ·
                    refine ⟨22898794391892407487710245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30531725855856543316946993 22898794391892407487710245)
                    ·
                      refine ⟨4293523948479826403945671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22898794391892407487710245 4293523948479826403945671)
                      ·
                        rfl

theorem cell23_8361608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_8361608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361608 prefixEnd_8361608 := by exact prefixLift 8361608
  have htrace : WordTrace (prefixWord ++ tailWord_8361608) baseStart_8361608 baseEnd_8361608 := by
    simpa [prefixWord, tailWord_8361608, baseEnd_8361608] using wordTrace_append hprefix tailTrace_8361608
  have hstable : (prefixWord ++ tailWord_8361608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361608).length < 2 ^ (prefixWord ++ tailWord_8361608).sum := by decide
  have hdescent : baseEnd_8361608 < baseStart_8361608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361611 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 3]
def baseStart_8361611 : Nat := 118140960795 + 8361611 * 2 ^ 59
def prefixEnd_8361611 : Nat := 4983230072969 + 3 ^ 40 * 8361611 * 2
def baseEnd_8361611 : Nat := 4293525488921789892208157

theorem tailTrace_8361611 : CollatzResearch.WordTrace tailWord_8361611 prefixEnd_8361611 4293525488921789892208157 := by
  unfold tailWord_8361611
  simp only [CollatzResearch.WordTrace]
  refine ⟨304973007710318871311084687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203315338473545914207389791 304973007710318871311084687)
  ·
    refine ⟨457459511565478306966627031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304973007710318871311084687 457459511565478306966627031)
    ·
      refine ⟨686189267348217460449940547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457459511565478306966627031 686189267348217460449940547)
      ·
        refine ⟨1029283901022326190674910821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686189267348217460449940547 1029283901022326190674910821)
        ·
          refine ⟨192990731441686160751545779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1029283901022326190674910821 192990731441686160751545779)
          ·
            refine ⟨289486097162529241127318669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192990731441686160751545779 289486097162529241127318669)
            ·
              refine ⟨108557286435948465422744501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289486097162529241127318669 108557286435948465422744501)
              ·
                refine ⟨10177245603370168633382297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108557286435948465422744501 10177245603370168633382297)
                ·
                  refine ⟨7632934202527626475036723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10177245603370168633382297 7632934202527626475036723)
                  ·
                    refine ⟨11449401303791439712555085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7632934202527626475036723 11449401303791439712555085)
                    ·
                      refine ⟨4293525488921789892208157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11449401303791439712555085 4293525488921789892208157)
                      ·
                        rfl

theorem cell23_8361611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 3].length) (baseStart_8361611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361611 prefixEnd_8361611 := by exact prefixLift 8361611
  have htrace : WordTrace (prefixWord ++ tailWord_8361611) baseStart_8361611 baseEnd_8361611 := by
    simpa [prefixWord, tailWord_8361611, baseEnd_8361611] using wordTrace_append hprefix tailTrace_8361611
  have hstable : (prefixWord ++ tailWord_8361611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361611).length < 2 ^ (prefixWord ++ tailWord_8361611).sum := by decide
  have hdescent : baseEnd_8361611 < baseStart_8361611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361664 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_8361664 : Nat := 118140960795 + 8361664 * 2 ^ 59
def prefixEnd_8361664 : Nat := 4983230072969 + 3 ^ 40 * 8361664 * 2
def baseEnd_8361664 : Nat := 4293552703396478184845413

theorem tailTrace_8361664 : CollatzResearch.WordTrace tailWord_8361664 prefixEnd_8361664 4293552703396478184845413 := by
  unfold tailWord_8361664
  simp only [CollatzResearch.WordTrace]
  refine ⟨152487470389563430681382023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203316627186084574241842697 152487470389563430681382023)
  ·
    refine ⟨228731205584345146022073035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152487470389563430681382023 228731205584345146022073035)
    ·
      refine ⟨343096808376517719033109553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228731205584345146022073035 343096808376517719033109553)
      ·
        refine ⟨257322606282388289274832165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343096808376517719033109553 257322606282388289274832165)
        ·
          refine ⟨48247988677947804239031031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257322606282388289274832165 48247988677947804239031031)
          ·
            refine ⟨72371983016921706358546547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48247988677947804239031031 72371983016921706358546547)
            ·
              refine ⟨108557974525382559537819821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72371983016921706358546547 108557974525382559537819821)
              ·
                refine ⟨40709240447018459826682433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108557974525382559537819821 40709240447018459826682433)
                ·
                  refine ⟨30531930335263844870011825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40709240447018459826682433 30531930335263844870011825)
                  ·
                    refine ⟨22898947751447883652508869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30531930335263844870011825 22898947751447883652508869)
                    ·
                      refine ⟨4293552703396478184845413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22898947751447883652508869 4293552703396478184845413)
                      ·
                        rfl

theorem cell23_8361664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_8361664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361664 prefixEnd_8361664 := by exact prefixLift 8361664
  have htrace : WordTrace (prefixWord ++ tailWord_8361664) baseStart_8361664 baseEnd_8361664 := by
    simpa [prefixWord, tailWord_8361664, baseEnd_8361664] using wordTrace_append hprefix tailTrace_8361664
  have hstable : (prefixWord ++ tailWord_8361664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361664).length < 2 ^ (prefixWord ++ tailWord_8361664).sum := by decide
  have hdescent : baseEnd_8361664 < baseStart_8361664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361667 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 9]
def baseStart_8361667 : Nat := 118140960795 + 8361667 * 2 ^ 59
def prefixEnd_8361667 : Nat := 4983230072969 + 3 ^ 40 * 8361667 * 2
def baseEnd_8361667 : Nat := 4293554243838441673107899

theorem tailTrace_8361667 : CollatzResearch.WordTrace tailWord_8361667 prefixEnd_8361667 4293554243838441673107899 := by
  unfold tailWord_8361667
  simp only [CollatzResearch.WordTrace]
  refine ⟨304975050198115992875123255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203316700132077328583415503 304975050198115992875123255)
  ·
    refine ⟨457462575297173989312684883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304975050198115992875123255 457462575297173989312684883)
    ·
      refine ⟨686193862945760983969027325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457462575297173989312684883 686193862945760983969027325)
      ·
        refine ⟨257322698604660368988385247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686193862945760983969027325 257322698604660368988385247)
        ·
          refine ⟨385984047906990553482577871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257322698604660368988385247 385984047906990553482577871)
          ·
            refine ⟨578976071860485830223866807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385984047906990553482577871 578976071860485830223866807)
            ·
              refine ⟨868464107790728745335800211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578976071860485830223866807 868464107790728745335800211)
              ·
                refine ⟨1302696161686093118003700317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868464107790728745335800211 1302696161686093118003700317)
                ·
                  refine ⟨488511060632284919251387619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1302696161686093118003700317 488511060632284919251387619)
                  ·
                    refine ⟨732766590948427378877081429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 488511060632284919251387619 732766590948427378877081429)
                    ·
                      refine ⟨4293554243838441673107899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 732766590948427378877081429 4293554243838441673107899)
                      ·
                        rfl

theorem cell23_8361667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_8361667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361667 prefixEnd_8361667 := by exact prefixLift 8361667
  have htrace : WordTrace (prefixWord ++ tailWord_8361667) baseStart_8361667 baseEnd_8361667 := by
    simpa [prefixWord, tailWord_8361667, baseEnd_8361667] using wordTrace_append hprefix tailTrace_8361667
  have hstable : (prefixWord ++ tailWord_8361667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361667).length < 2 ^ (prefixWord ++ tailWord_8361667).sum := by decide
  have hdescent : baseEnd_8361667 < baseStart_8361667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361711 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 2, 5, 2]
def baseStart_8361711 : Nat := 118140960795 + 8361711 * 2 ^ 59
def prefixEnd_8361711 : Nat := 4983230072969 + 3 ^ 40 * 8361711 * 2
def baseEnd_8361711 : Nat := 4293576836987239500957697

theorem tailTrace_8361711 : CollatzResearch.WordTrace tailWord_8361711 prefixEnd_8361711 4293576836987239500957697 := by
  unfold tailWord_8361711
  simp only [CollatzResearch.WordTrace]
  refine ⟨304976655009956588389724987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203317770006637725593149991 304976655009956588389724987)
  ·
    refine ⟨457464982514934882584587481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304976655009956588389724987 457464982514934882584587481)
    ·
      refine ⟨343098736886201161938440611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457464982514934882584587481 343098736886201161938440611)
      ·
        refine ⟨514648105329301742907660917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343098736886201161938440611 514648105329301742907660917)
        ·
          refine ⟨48248259874622038397593211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 514648105329301742907660917 48248259874622038397593211)
          ·
            refine ⟨72372389811933057596389817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48248259874622038397593211 72372389811933057596389817)
            ·
              refine ⟨54279292358949793197292363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72372389811933057596389817 54279292358949793197292363)
              ·
                refine ⟨81418938538424689795938545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54279292358949793197292363 81418938538424689795938545)
                ·
                  refine ⟨61064203903818517346953909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81418938538424689795938545 61064203903818517346953909)
                  ·
                    refine ⟨5724769115982986001276929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61064203903818517346953909 5724769115982986001276929)
                    ·
                      refine ⟨4293576836987239500957697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724769115982986001276929 4293576836987239500957697)
                      ·
                        rfl

theorem cell23_8361711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 5, 2].length) (baseStart_8361711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361711 prefixEnd_8361711 := by exact prefixLift 8361711
  have htrace : WordTrace (prefixWord ++ tailWord_8361711) baseStart_8361711 baseEnd_8361711 := by
    simpa [prefixWord, tailWord_8361711, baseEnd_8361711] using wordTrace_append hprefix tailTrace_8361711
  have hstable : (prefixWord ++ tailWord_8361711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361711).length < 2 ^ (prefixWord ++ tailWord_8361711).sum := by decide
  have hdescent : baseEnd_8361711 < baseStart_8361711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361785 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 3, 4]
def baseStart_8361785 : Nat := 118140960795 + 8361785 * 2 ^ 59
def prefixEnd_8361785 : Nat := 4983230072969 + 3 ^ 40 * 8361785 * 2
def baseEnd_8361785 : Nat := 1431204944851890737144119

theorem tailTrace_8361785 : CollatzResearch.WordTrace tailWord_8361785 prefixEnd_8361785 1431204944851890737144119 := by
  unfold tailWord_8361785
  simp only [CollatzResearch.WordTrace]
  refine ⟨304979354011688499027918809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203319569341125666018612539 304979354011688499027918809)
  ·
    refine ⟨228734515508766374270939107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304979354011688499027918809 228734515508766374270939107)
    ·
      refine ⟨343101773263149561406408661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228734515508766374270939107 343101773263149561406408661)
      ·
        refine ⟨8041447810855067845462703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 343101773263149561406408661 8041447810855067845462703)
        ·
          refine ⟨12062171716282601768194055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041447810855067845462703 12062171716282601768194055)
          ·
            refine ⟨18093257574423902652291083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12062171716282601768194055 18093257574423902652291083)
            ·
              refine ⟨27139886361635853978436625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18093257574423902652291083 27139886361635853978436625)
              ·
                refine ⟨20354914771226890483827469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27139886361635853978436625 20354914771226890483827469)
                ·
                  refine ⟨7633093039210083931435301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20354914771226890483827469 7633093039210083931435301)
                  ·
                    refine ⟨1431204944851890737144119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7633093039210083931435301 1431204944851890737144119)
                    ·
                      rfl

theorem cell23_8361785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 4].length) (baseStart_8361785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361785 prefixEnd_8361785 := by exact prefixLift 8361785
  have htrace : WordTrace (prefixWord ++ tailWord_8361785) baseStart_8361785 baseEnd_8361785 := by
    simpa [prefixWord, tailWord_8361785, baseEnd_8361785] using wordTrace_append hprefix tailTrace_8361785
  have hstable : (prefixWord ++ tailWord_8361785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361785).length < 2 ^ (prefixWord ++ tailWord_8361785).sum := by decide
  have hdescent : baseEnd_8361785 < baseStart_8361785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361815 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 6]
def baseStart_8361815 : Nat := 118140960795 + 8361815 * 2 ^ 59
def prefixEnd_8361815 : Nat := 4983230072969 + 3 ^ 40 * 8361815 * 2
def baseEnd_8361815 : Nat := 477070026552811899339691

theorem tailTrace_8361815 : CollatzResearch.WordTrace tailWord_8361815 prefixEnd_8361815 477070026552811899339691 := by
  unfold tailWord_8361815
  simp only [CollatzResearch.WordTrace]
  refine ⟨304980448201579814151510899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203320298801053209434340599 304980448201579814151510899)
  ·
    refine ⟨457470672302369721227266349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304980448201579814151510899 457470672302369721227266349)
    ·
      refine ⟨171551502113388645460224881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457470672302369721227266349 171551502113388645460224881)
      ·
        refine ⟨128663626585041484095168661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171551502113388645460224881 128663626585041484095168661)
        ·
          refine ⟨6031107496173819566961031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128663626585041484095168661 6031107496173819566961031)
          ·
            refine ⟨9046661244260729350441547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031107496173819566961031 9046661244260729350441547)
            ·
              refine ⟨13569991866391094025662321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046661244260729350441547 13569991866391094025662321)
              ·
                refine ⟨10177493899793320519246741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13569991866391094025662321 10177493899793320519246741)
                ·
                  refine ⟨477070026552811899339691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10177493899793320519246741 477070026552811899339691)
                  ·
                    rfl

theorem cell23_8361815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 6].length) (baseStart_8361815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361815 prefixEnd_8361815 := by exact prefixLift 8361815
  have htrace : WordTrace (prefixWord ++ tailWord_8361815) baseStart_8361815 baseEnd_8361815 := by
    simpa [prefixWord, tailWord_8361815, baseEnd_8361815] using wordTrace_append hprefix tailTrace_8361815
  have hstable : (prefixWord ++ tailWord_8361815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361815).length < 2 ^ (prefixWord ++ tailWord_8361815).sum := by decide
  have hdescent : baseEnd_8361815 < baseStart_8361815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361818 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2]
def baseStart_8361818 : Nat := 118140960795 + 8361818 * 2 ^ 59
def prefixEnd_8361818 : Nat := 4983230072969 + 3 ^ 40 * 8361818 * 2
def baseEnd_8361818 : Nat := 4293631779417270582319705

theorem tailTrace_8361818 : CollatzResearch.WordTrace tailWord_8361818 prefixEnd_8361818 4293631779417270582319705 := by
  unfold tailWord_8361818
  simp only [CollatzResearch.WordTrace]
  refine ⟨76245139405142236415967527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203320371747045963775913405 76245139405142236415967527)
  ·
    refine ⟨114367709107713354623951291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76245139405142236415967527 114367709107713354623951291)
    ·
      refine ⟨171551563661570031935926937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114367709107713354623951291 171551563661570031935926937)
      ·
        refine ⟨128663672746177523951945203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171551563661570031935926937 128663672746177523951945203)
        ·
          refine ⟨192995509119266285927917805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128663672746177523951945203 192995509119266285927917805)
          ·
            refine ⟨72373315919724857222969177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192995509119266285927917805 72373315919724857222969177)
            ·
              refine ⟨54279986939793642917226883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72373315919724857222969177 54279986939793642917226883)
              ·
                refine ⟨81419980409690464375840325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54279986939793642917226883 81419980409690464375840325)
                ·
                  refine ⟨15266246326816962070470061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81419980409690464375840325 15266246326816962070470061)
                  ·
                    refine ⟨5724842372556360776426273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15266246326816962070470061 5724842372556360776426273)
                    ·
                      refine ⟨4293631779417270582319705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724842372556360776426273 4293631779417270582319705)
                      ·
                        rfl

theorem cell23_8361818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_8361818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361818 prefixEnd_8361818 := by exact prefixLift 8361818
  have htrace : WordTrace (prefixWord ++ tailWord_8361818) baseStart_8361818 baseEnd_8361818 := by
    simpa [prefixWord, tailWord_8361818, baseEnd_8361818] using wordTrace_append hprefix tailTrace_8361818
  have hstable : (prefixWord ++ tailWord_8361818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361818).length < 2 ^ (prefixWord ++ tailWord_8361818).sum := by decide
  have hdescent : baseEnd_8361818 < baseStart_8361818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361825 : List Nat := [1, 2, 3, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_8361825 : Nat := 118140960795 + 8361825 * 2 ^ 59
def prefixEnd_8361825 : Nat := 4983230072969 + 3 ^ 40 * 8361825 * 2
def baseEnd_8361825 : Nat := 4293635373781852054932173

theorem tailTrace_8361825 : CollatzResearch.WordTrace tailWord_8361825 prefixEnd_8361825 4293635373781852054932173 := by
  unfold tailWord_8361825
  simp only [CollatzResearch.WordTrace]
  refine ⟨304980812931543585859374929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203320541954362390572916619 304980812931543585859374929)
  ·
    refine ⟨228735609698657689394531197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304980812931543585859374929 228735609698657689394531197)
    ·
      refine ⟨85775853636996633522949199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228735609698657689394531197 85775853636996633522949199)
      ·
        refine ⟨128663780455494950284423799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85775853636996633522949199 128663780455494950284423799)
        ·
          refine ⟨192995670683242425426635699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128663780455494950284423799 192995670683242425426635699)
          ·
            refine ⟨289493506024863638139953549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192995670683242425426635699 289493506024863638139953549)
            ·
              refine ⟨108560064759323864302482581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289493506024863638139953549 108560064759323864302482581)
              ·
                refine ⟨5088753035593306139178871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108560064759323864302482581 5088753035593306139178871)
                ·
                  refine ⟨7633129553389959208768307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5088753035593306139178871 7633129553389959208768307)
                  ·
                    refine ⟨11449694330084938813152461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7633129553389959208768307 11449694330084938813152461)
                    ·
                      refine ⟨4293635373781852054932173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11449694330084938813152461 4293635373781852054932173)
                      ·
                        rfl

theorem cell23_8361825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_8361825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361825 prefixEnd_8361825 := by exact prefixLift 8361825
  have htrace : WordTrace (prefixWord ++ tailWord_8361825) baseStart_8361825 baseEnd_8361825 := by
    simpa [prefixWord, tailWord_8361825, baseEnd_8361825] using wordTrace_append hprefix tailTrace_8361825
  have hstable : (prefixWord ++ tailWord_8361825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361825).length < 2 ^ (prefixWord ++ tailWord_8361825).sum := by decide
  have hdescent : baseEnd_8361825 < baseStart_8361825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361861 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_8361861 : Nat := 118140960795 + 8361861 * 2 ^ 59
def prefixEnd_8361861 : Nat := 4983230072969 + 3 ^ 40 * 8361861 * 2
def baseEnd_8361861 : Nat := 4293653859085413914082007

theorem tailTrace_8361861 : CollatzResearch.WordTrace tailWord_8361861 prefixEnd_8361861 4293653859085413914082007 := by
  unfold tailWord_8361861
  simp only [CollatzResearch.WordTrace]
  refine ⟨304982125959413164007685437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203321417306275442671790291 304982125959413164007685437)
  ·
    refine ⟨114368297234779936502882039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304982125959413164007685437 114368297234779936502882039)
    ·
      refine ⟨171552445852169904754323059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114368297234779936502882039 171552445852169904754323059)
      ·
        refine ⟨257328668778254857131484589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171552445852169904754323059 257328668778254857131484589)
        ·
          refine ⟨96498250791845571424306721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257328668778254857131484589 96498250791845571424306721)
          ·
            refine ⟨72373688093884178568230041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96498250791845571424306721 72373688093884178568230041)
            ·
              refine ⟨54280266070413133926172531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72373688093884178568230041 54280266070413133926172531)
              ·
                refine ⟨81420399105619700889258797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54280266070413133926172531 81420399105619700889258797)
                ·
                  refine ⟨30532649664607387833472049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81420399105619700889258797 30532649664607387833472049)
                  ·
                    refine ⟨22899487248455540875104037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30532649664607387833472049 22899487248455540875104037)
                    ·
                      refine ⟨4293653859085413914082007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22899487248455540875104037 4293653859085413914082007)
                      ·
                        rfl

theorem cell23_8361861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_8361861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361861 prefixEnd_8361861 := by exact prefixLift 8361861
  have htrace : WordTrace (prefixWord ++ tailWord_8361861) baseStart_8361861 baseEnd_8361861 := by
    simpa [prefixWord, tailWord_8361861, baseEnd_8361861] using wordTrace_append hprefix tailTrace_8361861
  have hstable : (prefixWord ++ tailWord_8361861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361861).length < 2 ^ (prefixWord ++ tailWord_8361861).sum := by decide
  have hdescent : baseEnd_8361861 < baseStart_8361861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361882 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2]
def baseStart_8361882 : Nat := 118140960795 + 8361882 * 2 ^ 59
def prefixEnd_8361882 : Nat := 4983230072969 + 3 ^ 40 * 8361882 * 2
def baseEnd_8361882 : Nat := 4293664642179158331919411

theorem tailTrace_8361882 : CollatzResearch.WordTrace tailWord_8361882 prefixEnd_8361882 4293664642179158331919411 := by
  unfold tailWord_8361882
  simp only [CollatzResearch.WordTrace]
  refine ⟨76245722973084271148549975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203321927928224723062799933 76245722973084271148549975)
  ·
    refine ⟨114368584459626406722824963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76245722973084271148549975 114368584459626406722824963)
    ·
      refine ⟨171552876689439610084237445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114368584459626406722824963 171552876689439610084237445)
      ·
        refine ⟨32166164379269926890794521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171552876689439610084237445 32166164379269926890794521)
        ·
          refine ⟨24124623284452445168095891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32166164379269926890794521 24124623284452445168095891)
          ·
            refine ⟨36186934926678667752143837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24124623284452445168095891 36186934926678667752143837)
            ·
              refine ⟨13570100597504500407053939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36186934926678667752143837 13570100597504500407053939)
              ·
                refine ⟨20355150896256750610580909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13570100597504500407053939 20355150896256750610580909)
                ·
                  refine ⟨7633181586096281478967841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20355150896256750610580909 7633181586096281478967841)
                  ·
                    refine ⟨5724886189572211109225881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7633181586096281478967841 5724886189572211109225881)
                    ·
                      refine ⟨4293664642179158331919411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724886189572211109225881 4293664642179158331919411)
                      ·
                        rfl

theorem cell23_8361882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_8361882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361882 prefixEnd_8361882 := by exact prefixLift 8361882
  have htrace : WordTrace (prefixWord ++ tailWord_8361882) baseStart_8361882 baseEnd_8361882 := by
    simpa [prefixWord, tailWord_8361882, baseEnd_8361882] using wordTrace_append hprefix tailTrace_8361882
  have hstable : (prefixWord ++ tailWord_8361882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361882).length < 2 ^ (prefixWord ++ tailWord_8361882).sum := by decide
  have hdescent : baseEnd_8361882 < baseStart_8361882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361892 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_8361892 : Nat := 118140960795 + 8361892 * 2 ^ 59
def prefixEnd_8361892 : Nat := 4983230072969 + 3 ^ 40 * 8361892 * 2
def baseEnd_8361892 : Nat := 1431223258995234430931455

theorem tailTrace_8361892 : CollatzResearch.WordTrace tailWord_8361892 prefixEnd_8361892 1431223258995234430931455 := by
  unfold tailWord_8361892
  simp only [CollatzResearch.WordTrace]
  refine ⟨152491628311150428151031965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203322171081533904201375953 152491628311150428151031965)
  ·
    refine ⟨57184360616681410556636987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152491628311150428151031965 57184360616681410556636987)
    ·
      refine ⟨85776540925022115834955481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57184360616681410556636987 85776540925022115834955481)
      ·
        refine ⟨64332405693766586876216611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85776540925022115834955481 64332405693766586876216611)
        ·
          refine ⟨96498608540649880314324917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64332405693766586876216611 96498608540649880314324917)
          ·
            refine ⟨9046744550685926279467961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96498608540649880314324917 9046744550685926279467961)
            ·
              refine ⟨6785058413014444709600971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9046744550685926279467961 6785058413014444709600971)
              ·
                refine ⟨10177587619521667064401457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785058413014444709600971 10177587619521667064401457)
                ·
                  refine ⟨7633190714641250298301093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10177587619521667064401457 7633190714641250298301093)
                  ·
                    refine ⟨1431223258995234430931455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7633190714641250298301093 1431223258995234430931455)
                    ·
                      rfl

theorem cell23_8361892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_8361892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361892 prefixEnd_8361892 := by exact prefixLift 8361892
  have htrace : WordTrace (prefixWord ++ tailWord_8361892) baseStart_8361892 baseEnd_8361892 := by
    simpa [prefixWord, tailWord_8361892, baseEnd_8361892] using wordTrace_append hprefix tailTrace_8361892
  have hstable : (prefixWord ++ tailWord_8361892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361892).length < 2 ^ (prefixWord ++ tailWord_8361892).sum := by decide
  have hdescent : baseEnd_8361892 < baseStart_8361892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361931 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 2, 6]
def baseStart_8361931 : Nat := 118140960795 + 8361931 * 2 ^ 59
def prefixEnd_8361931 : Nat := 4983230072969 + 3 ^ 40 * 8361931 * 2
def baseEnd_8361931 : Nat := 1431229934243742880068895

theorem tailTrace_8361931 : CollatzResearch.WordTrace tailWord_8361931 prefixEnd_8361931 1431229934243742880068895 := by
  unfold tailWord_8361931
  simp only [CollatzResearch.WordTrace]
  refine ⟨304984679069159565962733647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203323119379439710641822431 304984679069159565962733647)
  ·
    refine ⟨457477018603739348944100471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304984679069159565962733647 457477018603739348944100471)
    ·
      refine ⟨686215527905609023416150707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457477018603739348944100471 686215527905609023416150707)
      ·
        refine ⟨1029323291858413535124226061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686215527905609023416150707 1029323291858413535124226061)
        ·
          refine ⟨385996234446905075671584773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1029323291858413535124226061 385996234446905075671584773)
          ·
            refine ⟨72374293958794701688422145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385996234446905075671584773 72374293958794701688422145)
            ·
              refine ⟨54280720469096026266316609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72374293958794701688422145 54280720469096026266316609)
              ·
                refine ⟨40710540351822019699737457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54280720469096026266316609 40710540351822019699737457)
                ·
                  refine ⟨30532905263866514774803093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40710540351822019699737457 30532905263866514774803093)
                  ·
                    refine ⟨1431229934243742880068895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30532905263866514774803093 1431229934243742880068895)
                    ·
                      rfl

theorem cell23_8361931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 6].length) (baseStart_8361931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361931 prefixEnd_8361931 := by exact prefixLift 8361931
  have htrace : WordTrace (prefixWord ++ tailWord_8361931) baseStart_8361931 baseEnd_8361931 := by
    simpa [prefixWord, tailWord_8361931, baseEnd_8361931] using wordTrace_append hprefix tailTrace_8361931
  have hstable : (prefixWord ++ tailWord_8361931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361931).length < 2 ^ (prefixWord ++ tailWord_8361931).sum := by decide
  have hdescent : baseEnd_8361931 < baseStart_8361931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361932 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_8361932 : Nat := 118140960795 + 8361932 * 2 ^ 59
def prefixEnd_8361932 : Nat := 4983230072969 + 3 ^ 40 * 8361932 * 2
def baseEnd_8361932 : Nat := 4293690316211883136294181

theorem tailTrace_8361932 : CollatzResearch.WordTrace tailWord_8361932 prefixEnd_8361932 4293690316211883136294181 := by
  unfold tailWord_8361932
  simp only [CollatzResearch.WordTrace]
  refine ⟨152492357771077971566760025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203323143694770628755680033 152492357771077971566760025)
  ·
    refine ⟨114369268328308478675070019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152492357771077971566760025 114369268328308478675070019)
    ·
      refine ⟨171553902492462718012605029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114369268328308478675070019 171553902492462718012605029)
      ·
        refine ⟨32166356717336759627363443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171553902492462718012605029 32166356717336759627363443)
        ·
          refine ⟨48249535076005139441045165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32166356717336759627363443 48249535076005139441045165)
          ·
            refine ⟨18093575653501927290391937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48249535076005139441045165 18093575653501927290391937)
            ·
              refine ⟨13570181740126445467793953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18093575653501927290391937 13570181740126445467793953)
              ·
                refine ⟨10177636305094834100845465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13570181740126445467793953 10177636305094834100845465)
                ·
                  refine ⟨7633227228821125575634099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10177636305094834100845465 7633227228821125575634099)
                  ·
                    refine ⟨11449840843231688363451149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7633227228821125575634099 11449840843231688363451149)
                    ·
                      refine ⟨4293690316211883136294181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11449840843231688363451149 4293690316211883136294181)
                      ·
                        rfl

theorem cell23_8361932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_8361932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361932 prefixEnd_8361932 := by exact prefixLift 8361932
  have htrace : WordTrace (prefixWord ++ tailWord_8361932) baseStart_8361932 baseEnd_8361932 := by
    simpa [prefixWord, tailWord_8361932, baseEnd_8361932] using wordTrace_append hprefix tailTrace_8361932
  have hstable : (prefixWord ++ tailWord_8361932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361932).length < 2 ^ (prefixWord ++ tailWord_8361932).sum := by decide
  have hdescent : baseEnd_8361932 < baseStart_8361932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361955 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 1, 4, 2]
def baseStart_8361955 : Nat := 118140960795 + 8361955 * 2 ^ 59
def prefixEnd_8361955 : Nat := 4983230072969 + 3 ^ 40 * 8361955 * 2
def baseEnd_8361955 : Nat := 4293702126266936546306575

theorem tailTrace_8361955 : CollatzResearch.WordTrace tailWord_8361955 prefixEnd_8361955 4293702126266936546306575 := by
  unfold tailWord_8361955
  simp only [CollatzResearch.WordTrace]
  refine ⟨304985554421072618061607319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203323702947381745374404879 304985554421072618061607319)
  ·
    refine ⟨457478331631608927092410979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304985554421072618061607319 457478331631608927092410979)
    ·
      refine ⟨686217497447413390638616469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457478331631608927092410979 686217497447413390638616469)
      ·
        refine ⟨32166445192847502686185147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 686217497447413390638616469 32166445192847502686185147)
        ·
          refine ⟨48249667789271254029277721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32166445192847502686185147 48249667789271254029277721)
          ·
            refine ⟨36187250841953440521958291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48249667789271254029277721 36187250841953440521958291)
            ·
              refine ⟨54280876262930160782937437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36187250841953440521958291 54280876262930160782937437)
              ·
                refine ⟨20355328598598810293601539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54280876262930160782937437 20355328598598810293601539)
                ·
                  refine ⟨30532992897898215440402309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20355328598598810293601539 30532992897898215440402309)
                  ·
                    refine ⟨5724936168355915395075433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30532992897898215440402309 5724936168355915395075433)
                    ·
                      refine ⟨4293702126266936546306575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724936168355915395075433 4293702126266936546306575)
                      ·
                        rfl

theorem cell23_8361955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_8361955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361955 prefixEnd_8361955 := by exact prefixLift 8361955
  have htrace : WordTrace (prefixWord ++ tailWord_8361955) baseStart_8361955 baseEnd_8361955 := by
    simpa [prefixWord, tailWord_8361955, baseEnd_8361955] using wordTrace_append hprefix tailTrace_8361955
  have hstable : (prefixWord ++ tailWord_8361955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361955).length < 2 ^ (prefixWord ++ tailWord_8361955).sum := by decide
  have hdescent : baseEnd_8361955 < baseStart_8361955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8361989 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 2, 2, 2]
def baseStart_8361989 : Nat := 118140960795 + 8361989 * 2 ^ 59
def prefixEnd_8361989 : Nat := 4983230072969 + 3 ^ 40 * 8361989 * 2
def baseEnd_8361989 : Nat := 4293719584609189413281419

theorem tailTrace_8361989 : CollatzResearch.WordTrace tailWord_8361989 prefixEnd_8361989 4293719584609189413281419 := by
  unfold tailWord_8361989
  simp only [CollatzResearch.WordTrace]
  refine ⟨304986794502949441868345021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203324529668632961245563347 304986794502949441868345021)
  ·
    refine ⟨114370047938606040700629383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304986794502949441868345021 114370047938606040700629383)
    ·
      refine ⟨171555071907909061050944075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114370047938606040700629383 171555071907909061050944075)
      ·
        refine ⟨257332607861863591576416113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171555071907909061050944075 257332607861863591576416113)
        ·
          refine ⟨192999455896397693682312085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257332607861863591576416113 192999455896397693682312085)
          ·
            refine ⟨9046849495143641891358379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192999455896397693682312085 9046849495143641891358379)
            ·
              refine ⟨13570274242715462837037569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046849495143641891358379 13570274242715462837037569)
              ·
                refine ⟨10177705682036597127778177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13570274242715462837037569 10177705682036597127778177)
                ·
                  refine ⟨7633279261527447845833633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10177705682036597127778177 7633279261527447845833633)
                  ·
                    refine ⟨5724959446145585884375225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7633279261527447845833633 5724959446145585884375225)
                    ·
                      refine ⟨4293719584609189413281419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5724959446145585884375225 4293719584609189413281419)
                      ·
                        rfl

theorem cell23_8361989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_8361989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8361989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8361989 prefixEnd_8361989 := by exact prefixLift 8361989
  have htrace : WordTrace (prefixWord ++ tailWord_8361989) baseStart_8361989 baseEnd_8361989 := by
    simpa [prefixWord, tailWord_8361989, baseEnd_8361989] using wordTrace_append hprefix tailTrace_8361989
  have hstable : (prefixWord ++ tailWord_8361989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8361989).length < 2 ^ (prefixWord ++ tailWord_8361989).sum := by decide
  have hdescent : baseEnd_8361989 < baseStart_8361989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8361989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362045 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_8362045 : Nat := 118140960795 + 8362045 * 2 ^ 59
def prefixEnd_8362045 : Nat := 4983230072969 + 3 ^ 40 * 8362045 * 2
def baseEnd_8362045 : Nat := 4293748339525841194181161

theorem tailTrace_8362045 : CollatzResearch.WordTrace tailWord_8362045 prefixEnd_8362045 4293748339525841194181161 := by
  unfold tailWord_8362045
  simp only [CollatzResearch.WordTrace]
  refine ⟨304988836990746563432383589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203325891327164375621589059 304988836990746563432383589)
  ·
    refine ⟨57185406935764980643571923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304988836990746563432383589 57185406935764980643571923)
    ·
      refine ⟨85778110403647470965357885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57185406935764980643571923 85778110403647470965357885)
      ·
        refine ⟨32166791401367801612009207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85778110403647470965357885 32166791401367801612009207)
        ·
          refine ⟨48250187102051702418013811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32166791401367801612009207 48250187102051702418013811)
          ·
            refine ⟨72375280653077553627020717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48250187102051702418013811 72375280653077553627020717)
            ·
              refine ⟨27140730244904082610132769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72375280653077553627020717 27140730244904082610132769)
              ·
                refine ⟨20355547683678061957599577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27140730244904082610132769 20355547683678061957599577)
                ·
                  refine ⟨15266660762758546468199683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20355547683678061957599577 15266660762758546468199683)
                  ·
                    refine ⟨22899991144137819702299525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15266660762758546468199683 22899991144137819702299525)
                    ·
                      refine ⟨4293748339525841194181161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22899991144137819702299525 4293748339525841194181161)
                      ·
                        rfl

theorem cell23_8362045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_8362045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362045 prefixEnd_8362045 := by exact prefixLift 8362045
  have htrace : WordTrace (prefixWord ++ tailWord_8362045) baseStart_8362045 baseEnd_8362045 := by
    simpa [prefixWord, tailWord_8362045, baseEnd_8362045] using wordTrace_append hprefix tailTrace_8362045
  have hstable : (prefixWord ++ tailWord_8362045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362045).length < 2 ^ (prefixWord ++ tailWord_8362045).sum := by decide
  have hdescent : baseEnd_8362045 < baseStart_8362045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362102 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_8362102 : Nat := 118140960795 + 8362102 * 2 ^ 59
def prefixEnd_8362102 : Nat := 4983230072969 + 3 ^ 40 * 8362102 * 2
def baseEnd_8362102 : Nat := 477086400880349719018711

theorem tailTrace_8362102 : CollatzResearch.WordTrace tailWord_8362102 prefixEnd_8362102 477086400880349719018711 := by
  unfold tailWord_8362102
  simp only [CollatzResearch.WordTrace]
  refine ⟨19061932246971253885450535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203327277301026708111472373 19061932246971253885450535)
  ·
    refine ⟨28592898370456880828175803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19061932246971253885450535 28592898370456880828175803)
    ·
      refine ⟨42889347555685321242263705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28592898370456880828175803 42889347555685321242263705)
      ·
        refine ⟨32167010666763990931697779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42889347555685321242263705 32167010666763990931697779)
        ·
          refine ⟨48250516000145986397546669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32167010666763990931697779 48250516000145986397546669)
          ·
            refine ⟨18093943500054744899080001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48250516000145986397546669 18093943500054744899080001)
            ·
              refine ⟨13570457625041058674310001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18093943500054744899080001 13570457625041058674310001)
              ·
                refine ⟨10177843218780794005732501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13570457625041058674310001 10177843218780794005732501)
                ·
                  refine ⟨477086400880349719018711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10177843218780794005732501 477086400880349719018711)
                  ·
                    rfl

theorem cell23_8362102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_8362102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362102 prefixEnd_8362102 := by exact prefixLift 8362102
  have htrace : WordTrace (prefixWord ++ tailWord_8362102) baseStart_8362102 baseEnd_8362102 := by
    simpa [prefixWord, tailWord_8362102, baseEnd_8362102] using wordTrace_append hprefix tailTrace_8362102
  have hstable : (prefixWord ++ tailWord_8362102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362102).length < 2 ^ (prefixWord ++ tailWord_8362102).sum := by decide
  have hdescent : baseEnd_8362102 < baseStart_8362102 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362145 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 1, 6]
def baseStart_8362145 : Nat := 118140960795 + 8362145 * 2 ^ 59
def prefixEnd_8362145 : Nat := 4983230072969 + 3 ^ 40 * 8362145 * 2
def baseEnd_8362145 : Nat := 1431266562530430267643567

theorem tailTrace_8362145 : CollatzResearch.WordTrace tailWord_8362145 prefixEnd_8362145 1431266562530430267643567 := by
  unfold tailWord_8362145
  simp only [CollatzResearch.WordTrace]
  refine ⟨304992484290384280511023889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203328322860256187007349259 304992484290384280511023889)
  ·
    refine ⟨228744363217788210383267917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304992484290384280511023889 228744363217788210383267917)
    ·
      refine ⟨85779136206670578893725469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228744363217788210383267917 85779136206670578893725469)
      ·
        refine ⟨32167176077501467085147051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85779136206670578893725469 32167176077501467085147051)
        ·
          refine ⟨48250764116252200627720577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32167176077501467085147051 48250764116252200627720577)
          ·
            refine ⟨36188073087189150470790433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48250764116252200627720577 36188073087189150470790433)
            ·
              refine ⟨27141054815391862853092825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36188073087189150470790433 27141054815391862853092825)
              ·
                refine ⟨20355791111543897139819619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27141054815391862853092825 20355791111543897139819619)
                ·
                  refine ⟨30533686667315845709729429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20355791111543897139819619 30533686667315845709729429)
                  ·
                    refine ⟨1431266562530430267643567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30533686667315845709729429 1431266562530430267643567)
                    ·
                      rfl

theorem cell23_8362145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_8362145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362145 prefixEnd_8362145 := by exact prefixLift 8362145
  have htrace : WordTrace (prefixWord ++ tailWord_8362145) baseStart_8362145 baseEnd_8362145 := by
    simpa [prefixWord, tailWord_8362145, baseEnd_8362145] using wordTrace_append hprefix tailTrace_8362145
  have hstable : (prefixWord ++ tailWord_8362145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362145).length < 2 ^ (prefixWord ++ tailWord_8362145).sum := by decide
  have hdescent : baseEnd_8362145 < baseStart_8362145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362146 : List Nat := [3, 3, 1, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_8362146 : Nat := 118140960795 + 8362146 * 2 ^ 59
def prefixEnd_8362146 : Nat := 4983230072969 + 3 ^ 40 * 8362146 * 2
def baseEnd_8362146 : Nat := 4293800201071945299018197

theorem tailTrace_8362146 : CollatzResearch.WordTrace tailWord_8362146 prefixEnd_8362146 4293800201071945299018197 := by
  unfold tailWord_8362146
  simp only [CollatzResearch.WordTrace]
  refine ⟨76248130190845164420452573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203328347175587105121206861 76248130190845164420452573)
  ·
    refine ⟨28593048821566936657669715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76248130190845164420452573 28593048821566936657669715)
    ·
      refine ⟨42889573232350404986504573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28593048821566936657669715 42889573232350404986504573)
      ·
        refine ⟨16083589962131401869939215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42889573232350404986504573 16083589962131401869939215)
        ·
          refine ⟨24125384943197102804908823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16083589962131401869939215 24125384943197102804908823)
          ·
            refine ⟨36188077414795654207363235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24125384943197102804908823 36188077414795654207363235)
            ·
              refine ⟨54282116122193481311044853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36188077414795654207363235 54282116122193481311044853)
              ·
                refine ⟨5088948386455638872910455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54282116122193481311044853 5088948386455638872910455)
                ·
                  refine ⟨7633422579683458309365683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5088948386455638872910455 7633422579683458309365683)
                  ·
                    refine ⟨11450133869525187464048525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7633422579683458309365683 11450133869525187464048525)
                    ·
                      refine ⟨4293800201071945299018197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450133869525187464048525 4293800201071945299018197)
                      ·
                        rfl

theorem cell23_8362146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_8362146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362146 prefixEnd_8362146 := by exact prefixLift 8362146
  have htrace : WordTrace (prefixWord ++ tailWord_8362146) baseStart_8362146 baseEnd_8362146 := by
    simpa [prefixWord, tailWord_8362146, baseEnd_8362146] using wordTrace_append hprefix tailTrace_8362146
  have hstable : (prefixWord ++ tailWord_8362146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362146).length < 2 ^ (prefixWord ++ tailWord_8362146).sum := by decide
  have hdescent : baseEnd_8362146 < baseStart_8362146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362169 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 3, 2, 2]
def baseStart_8362169 : Nat := 118140960795 + 8362169 * 2 ^ 59
def prefixEnd_8362169 : Nat := 4983230072969 + 3 ^ 40 * 8362169 * 2
def baseEnd_8362169 : Nat := 4293812011126998709030591

theorem tailTrace_8362169 : CollatzResearch.WordTrace tailWord_8362169 prefixEnd_8362169 4293812011126998709030591 := by
  unfold tailWord_8362169
  simp only [CollatzResearch.WordTrace]
  refine ⟨304993359642297332609897561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203328906428198221739931707 304993359642297332609897561)
  ·
    refine ⟨228745019731722999457423171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304993359642297332609897561 228745019731722999457423171)
    ·
      refine ⟨343117529597584499186134757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228745019731722999457423171 343117529597584499186134757)
      ·
        refine ⟨64334536799547093597400267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343117529597584499186134757 64334536799547093597400267)
        ·
          refine ⟨96501805199320640396100401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64334536799547093597400267 96501805199320640396100401)
          ·
            refine ⟨72376353899490480297075301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96501805199320640396100401 72376353899490480297075301)
            ·
              refine ⟨13570566356154465055701619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72376353899490480297075301 13570566356154465055701619)
              ·
                refine ⟨20355849534231697583552429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13570566356154465055701619 20355849534231697583552429)
                ·
                  refine ⟨7633443575336886593832161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20355849534231697583552429 7633443575336886593832161)
                  ·
                    refine ⟨5725082681502664945374121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7633443575336886593832161 5725082681502664945374121)
                    ·
                      refine ⟨4293812011126998709030591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725082681502664945374121 4293812011126998709030591)
                      ·
                        rfl

theorem cell23_8362169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_8362169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362169 prefixEnd_8362169 := by exact prefixLift 8362169
  have htrace : WordTrace (prefixWord ++ tailWord_8362169) baseStart_8362169 baseEnd_8362169 := by
    simpa [prefixWord, tailWord_8362169, baseEnd_8362169] using wordTrace_append hprefix tailTrace_8362169
  have hstable : (prefixWord ++ tailWord_8362169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362169).length < 2 ^ (prefixWord ++ tailWord_8362169).sum := by decide
  have hdescent : baseEnd_8362169 < baseStart_8362169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362172 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_8362172 : Nat := 118140960795 + 8362172 * 2 ^ 59
def prefixEnd_8362172 : Nat := 4983230072969 + 3 ^ 40 * 8362172 * 2
def baseEnd_8362172 : Nat := 4293813551568962197293077

theorem tailTrace_8362172 : CollatzResearch.WordTrace tailWord_8362172 prefixEnd_8362172 4293813551568962197293077 := by
  unfold tailWord_8362172
  simp only [CollatzResearch.WordTrace]
  refine ⟨152496734530643232061128385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203328979374190976081504513 152496734530643232061128385)
  ·
    refine ⟨114372550897982424045846289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152496734530643232061128385 114372550897982424045846289)
    ·
      refine ⟨85779413173486818034384717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114372550897982424045846289 85779413173486818034384717)
      ·
        refine ⟨32167279940057556762894269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85779413173486818034384717 32167279940057556762894269)
        ·
          refine ⟨12062729977521583786085351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32167279940057556762894269 12062729977521583786085351)
          ·
            refine ⟨18094094966282375679128027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12062729977521583786085351 18094094966282375679128027)
            ·
              refine ⟨27141142449423563518692041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18094094966282375679128027 27141142449423563518692041)
              ·
                refine ⟨20355856837067672639019031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27141142449423563518692041 20355856837067672639019031)
                ·
                  refine ⟨30533785255601508958528547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20355856837067672639019031 30533785255601508958528547)
                  ·
                    refine ⟨45800677883402263437792821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30533785255601508958528547 45800677883402263437792821)
                    ·
                      refine ⟨4293813551568962197293077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45800677883402263437792821 4293813551568962197293077)
                      ·
                        rfl

theorem cell23_8362172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_8362172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362172 prefixEnd_8362172 := by exact prefixLift 8362172
  have htrace : WordTrace (prefixWord ++ tailWord_8362172) baseStart_8362172 baseEnd_8362172 := by
    simpa [prefixWord, tailWord_8362172, baseEnd_8362172] using wordTrace_append hprefix tailTrace_8362172
  have hstable : (prefixWord ++ tailWord_8362172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362172).length < 2 ^ (prefixWord ++ tailWord_8362172).sum := by decide
  have hdescent : baseEnd_8362172 < baseStart_8362172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362185 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 3]
def baseStart_8362185 : Nat := 118140960795 + 8362185 * 2 ^ 59
def prefixEnd_8362185 : Nat := 4983230072969 + 3 ^ 40 * 8362185 * 2
def baseEnd_8362185 : Nat := 4293820226817470646430517

theorem tailTrace_8362185 : CollatzResearch.WordTrace tailWord_8362185 prefixEnd_8362185 4293820226817470646430517 := by
  unfold tailWord_8362185
  simp only [CollatzResearch.WordTrace]
  refine ⟨304993943210239367342480009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203329295473492911561653339 304993943210239367342480009)
  ·
    refine ⟨228745457407679525506860007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304993943210239367342480009 228745457407679525506860007)
    ·
      refine ⟨343118186111519288260290011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228745457407679525506860007 343118186111519288260290011)
      ·
        refine ⟨514677279167278932390435017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343118186111519288260290011 514677279167278932390435017)
        ·
          refine ⟨386007959375459199292826263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514677279167278932390435017 386007959375459199292826263)
          ·
            refine ⟨579011939063188798939239395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386007959375459199292826263 579011939063188798939239395)
            ·
              refine ⟨868517908594783198408859093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579011939063188798939239395 868517908594783198408859093)
              ·
                refine ⟨20355888482690231212707635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 868517908594783198408859093 20355888482690231212707635)
                ·
                  refine ⟨30533832724035346819061453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20355888482690231212707635 30533832724035346819061453)
                  ·
                    refine ⟨11450187271513255057148045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30533832724035346819061453 11450187271513255057148045)
                    ·
                      refine ⟨4293820226817470646430517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450187271513255057148045 4293820226817470646430517)
                      ·
                        rfl

theorem cell23_8362185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_8362185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362185 prefixEnd_8362185 := by exact prefixLift 8362185
  have htrace : WordTrace (prefixWord ++ tailWord_8362185) baseStart_8362185 baseEnd_8362185 := by
    simpa [prefixWord, tailWord_8362185, baseEnd_8362185] using wordTrace_append hprefix tailTrace_8362185
  have hstable : (prefixWord ++ tailWord_8362185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362185).length < 2 ^ (prefixWord ++ tailWord_8362185).sum := by decide
  have hdescent : baseEnd_8362185 < baseStart_8362185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362202 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_8362202 : Nat := 118140960795 + 8362202 * 2 ^ 59
def prefixEnd_8362202 : Nat := 4983230072969 + 3 ^ 40 * 8362202 * 2
def baseEnd_8362202 : Nat := 4293828955988597079917939

theorem tailTrace_8362202 : CollatzResearch.WordTrace tailWord_8362202 prefixEnd_8362202 4293828955988597079917939 := by
  unfold tailWord_8362202
  simp only [CollatzResearch.WordTrace]
  refine ⟨76248640812794444811462215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203329708834118519497232573 76248640812794444811462215)
  ·
    refine ⟨114372961219191667217193323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76248640812794444811462215 114372961219191667217193323)
    ·
      refine ⟨171559441828787500825789985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114372961219191667217193323 171559441828787500825789985)
      ·
        refine ⟨128669581371590625619342489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171559441828787500825789985 128669581371590625619342489)
        ·
          refine ⟨96502186028692969214506867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128669581371590625619342489 96502186028692969214506867)
          ·
            refine ⟨144753279043039453821760301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96502186028692969214506867 144753279043039453821760301)
            ·
              refine ⟨54282479641139795183160113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144753279043039453821760301 54282479641139795183160113)
              ·
                refine ⟨40711859730854846387370085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54282479641139795183160113 40711859730854846387370085)
                ·
                  refine ⟨7633473699535283697631891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40711859730854846387370085 7633473699535283697631891)
                  ·
                    refine ⟨11450210549302925546447837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7633473699535283697631891 11450210549302925546447837)
                    ·
                      refine ⟨4293828955988597079917939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450210549302925546447837 4293828955988597079917939)
                      ·
                        rfl

theorem cell23_8362202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_8362202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362202 prefixEnd_8362202 := by exact prefixLift 8362202
  have htrace : WordTrace (prefixWord ++ tailWord_8362202) baseStart_8362202 baseEnd_8362202 := by
    simpa [prefixWord, tailWord_8362202, baseEnd_8362202] using wordTrace_append hprefix tailTrace_8362202
  have hstable : (prefixWord ++ tailWord_8362202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362202).length < 2 ^ (prefixWord ++ tailWord_8362202).sum := by decide
  have hdescent : baseEnd_8362202 < baseStart_8362202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362212 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_8362212 : Nat := 118140960795 + 8362212 * 2 ^ 59
def prefixEnd_8362212 : Nat := 4983230072969 + 3 ^ 40 * 8362212 * 2
def baseEnd_8362212 : Nat := 4293834090795142040792893

theorem tailTrace_8362212 : CollatzResearch.WordTrace tailWord_8362212 prefixEnd_8362212 4293834090795142040792893 := by
  unfold tailWord_8362212
  simp only [CollatzResearch.WordTrace]
  refine ⟨152497463990570775476856445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203329951987427700635808593 152497463990570775476856445)
  ·
    refine ⟨57186548996464040803821167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152497463990570775476856445 57186548996464040803821167)
    ·
      refine ⟨85779823494696061205731751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57186548996464040803821167 85779823494696061205731751)
      ·
        refine ⟨128669735242044091808597627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85779823494696061205731751 128669735242044091808597627)
        ·
          refine ⟨193004602863066137712896441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128669735242044091808597627 193004602863066137712896441)
          ·
            refine ⟨144753452147299603284672331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193004602863066137712896441 144753452147299603284672331)
            ·
              refine ⟨217130178220949404927008497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144753452147299603284672331 217130178220949404927008497)
              ·
                refine ⟨162847633665712053695256373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217130178220949404927008497 162847633665712053695256373)
                ·
                  refine ⟨15266965656160505033930285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162847633665712053695256373 15266965656160505033930285)
                  ·
                    refine ⟨5725112121060189387723857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15266965656160505033930285 5725112121060189387723857)
                    ·
                      refine ⟨4293834090795142040792893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725112121060189387723857 4293834090795142040792893)
                      ·
                        rfl

theorem cell23_8362212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_8362212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362212 prefixEnd_8362212 := by exact prefixLift 8362212
  have htrace : WordTrace (prefixWord ++ tailWord_8362212) baseStart_8362212 baseEnd_8362212 := by
    simpa [prefixWord, tailWord_8362212, baseEnd_8362212] using wordTrace_append hprefix tailTrace_8362212
  have hstable : (prefixWord ++ tailWord_8362212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362212).length < 2 ^ (prefixWord ++ tailWord_8362212).sum := by decide
  have hdescent : baseEnd_8362212 < baseStart_8362212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362236 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_8362236 : Nat := 118140960795 + 8362236 * 2 ^ 59
def prefixEnd_8362236 : Nat := 4983230072969 + 3 ^ 40 * 8362236 * 2
def baseEnd_8362236 : Nat := 4293846414330849946892783

theorem tailTrace_8362236 : CollatzResearch.WordTrace tailWord_8362236 prefixEnd_8362236 4293846414330849946892783 := by
  unfold tailWord_8362236
  simp only [CollatzResearch.WordTrace]
  refine ⟨152497901666527301526293281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203330535555369735368391041 152497901666527301526293281)
  ·
    refine ⟨114373426249895476144719961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152497901666527301526293281 114373426249895476144719961)
    ·
      refine ⟨85780069687421607108539971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114373426249895476144719961 85780069687421607108539971)
      ·
        refine ⟨128670104531132410662809957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85780069687421607108539971 128670104531132410662809957)
        ·
          refine ⟨24125644599587326999276867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128670104531132410662809957 24125644599587326999276867)
          ·
            refine ⟨36188466899380990498915301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24125644599587326999276867 36188466899380990498915301)
            ·
              refine ⟨6785337543633935718546619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36188466899380990498915301 6785337543633935718546619)
              ·
                refine ⟨10178006315450903577819929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785337543633935718546619 10178006315450903577819929)
                ·
                  refine ⟨7633504736588177683364947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10178006315450903577819929 7633504736588177683364947)
                  ·
                    refine ⟨11450257104882266525047421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7633504736588177683364947 11450257104882266525047421)
                    ·
                      refine ⟨4293846414330849946892783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450257104882266525047421 4293846414330849946892783)
                      ·
                        rfl

theorem cell23_8362236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_8362236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362236 prefixEnd_8362236 := by exact prefixLift 8362236
  have htrace : WordTrace (prefixWord ++ tailWord_8362236) baseStart_8362236 baseEnd_8362236 := by
    simpa [prefixWord, tailWord_8362236, baseEnd_8362236] using wordTrace_append hprefix tailTrace_8362236
  have hstable : (prefixWord ++ tailWord_8362236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362236).length < 2 ^ (prefixWord ++ tailWord_8362236).sum := by decide
  have hdescent : baseEnd_8362236 < baseStart_8362236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362245 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_8362245 : Nat := 118140960795 + 8362245 * 2 ^ 59
def prefixEnd_8362245 : Nat := 4983230072969 + 3 ^ 40 * 8362245 * 2
def baseEnd_8362245 : Nat := 4293851035656740411680241

theorem tailTrace_8362245 : CollatzResearch.WordTrace tailWord_8362245 prefixEnd_8362245 4293851035656740411680241 := by
  unfold tailWord_8362245
  simp only [CollatzResearch.WordTrace]
  refine ⟨304996131590021997589664189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203330754393347998393109459 304996131590021997589664189)
  ·
    refine ⟨114373549346258249096124071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304996131590021997589664189 114373549346258249096124071)
    ·
      refine ⟨171560324019387373644186107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114373549346258249096124071 171560324019387373644186107)
      ·
        refine ⟨257340486029081060466279161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171560324019387373644186107 257340486029081060466279161)
        ·
          refine ⟨193005364521810795349709371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257340486029081060466279161 193005364521810795349709371)
          ·
            refine ⟨289508046782716193024564057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193005364521810795349709371 289508046782716193024564057)
            ·
              refine ⟨217131035087037144768423043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289508046782716193024564057 217131035087037144768423043)
              ·
                refine ⟨325696552630555717152634565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217131035087037144768423043 325696552630555717152634565)
                ·
                  refine ⟨61068103618229196966118981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325696552630555717152634565 61068103618229196966118981)
                  ·
                    refine ⟨11450269428417974431147309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61068103618229196966118981 11450269428417974431147309)
                    ·
                      refine ⟨4293851035656740411680241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450269428417974431147309 4293851035656740411680241)
                      ·
                        rfl

theorem cell23_8362245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_8362245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362245 prefixEnd_8362245 := by exact prefixLift 8362245
  have htrace : WordTrace (prefixWord ++ tailWord_8362245) baseStart_8362245 baseEnd_8362245 := by
    simpa [prefixWord, tailWord_8362245, baseEnd_8362245] using wordTrace_append hprefix tailTrace_8362245
  have hstable : (prefixWord ++ tailWord_8362245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362245).length < 2 ^ (prefixWord ++ tailWord_8362245).sum := by decide
  have hdescent : baseEnd_8362245 < baseStart_8362245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362276 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_8362276 : Nat := 118140960795 + 8362276 * 2 ^ 59
def prefixEnd_8362276 : Nat := 4983230072969 + 3 ^ 40 * 8362276 * 2
def baseEnd_8362276 : Nat := 4293866953557029790392599

theorem tailTrace_8362276 : CollatzResearch.WordTrace tailWord_8362276 prefixEnd_8362276 4293866953557029790392599 := by
  unfold tailWord_8362276
  simp only [CollatzResearch.WordTrace]
  refine ⟨152498631126454844942021341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203331508168606459922695121 152498631126454844942021341)
  ·
    refine ⟨57186986672420566853258003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152498631126454844942021341 57186986672420566853258003)
    ·
      refine ⟨85780480008630850279887005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57186986672420566853258003 85780480008630850279887005)
      ·
        refine ⟨32167680003236568854957627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85780480008630850279887005 32167680003236568854957627)
        ·
          refine ⟨48251520004854853282436441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32167680003236568854957627 48251520004854853282436441)
          ·
            refine ⟨36188640003641139961827331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48251520004854853282436441 36188640003641139961827331)
            ·
              refine ⟨54282960005461709942740997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36188640003641139961827331 54282960005461709942740997)
              ·
                refine ⟨10178055001024070614263937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54282960005461709942740997 10178055001024070614263937)
                ·
                  refine ⟨7633541250768052960697953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10178055001024070614263937 7633541250768052960697953)
                  ·
                    refine ⟨5725155938076039720523465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7633541250768052960697953 5725155938076039720523465)
                    ·
                      refine ⟨4293866953557029790392599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725155938076039720523465 4293866953557029790392599)
                      ·
                        rfl

theorem cell23_8362276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_8362276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362276 prefixEnd_8362276 := by exact prefixLift 8362276
  have htrace : WordTrace (prefixWord ++ tailWord_8362276) baseStart_8362276 baseEnd_8362276 := by
    simpa [prefixWord, tailWord_8362276, baseEnd_8362276] using wordTrace_append hprefix tailTrace_8362276
  have hstable : (prefixWord ++ tailWord_8362276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362276).length < 2 ^ (prefixWord ++ tailWord_8362276).sum := by decide
  have hdescent : baseEnd_8362276 < baseStart_8362276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362295 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 4, 5]
def baseStart_8362295 : Nat := 118140960795 + 8362295 * 2 ^ 59
def prefixEnd_8362295 : Nat := 4983230072969 + 3 ^ 40 * 8362295 * 2
def baseEnd_8362295 : Nat := 1431292236563155072018337

theorem tailTrace_8362295 : CollatzResearch.WordTrace tailWord_8362295 prefixEnd_8362295 1431292236563155072018337 := by
  unfold tailWord_8362295
  simp only [CollatzResearch.WordTrace]
  refine ⟨304997955239840856128984339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203331970159893904085989559 304997955239840856128984339)
  ·
    refine ⟨457496932859761284193476509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304997955239840856128984339 457496932859761284193476509)
    ·
      refine ⟨171561349822410481572553691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457496932859761284193476509 171561349822410481572553691)
      ·
        refine ⟨257342024733615722358830537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171561349822410481572553691 257342024733615722358830537)
        ·
          refine ⟨193006518550211791769122903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257342024733615722358830537 193006518550211791769122903)
          ·
            refine ⟨289509777825317687653684355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193006518550211791769122903 289509777825317687653684355)
            ·
              refine ⟨434264666737976531480526533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289509777825317687653684355 434264666737976531480526533)
              ·
                refine ⟨81424625013370599652598725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434264666737976531480526533 81424625013370599652598725)
                ·
                  refine ⟨15267117190006987434862261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81424625013370599652598725 15267117190006987434862261)
                  ·
                    refine ⟨1431292236563155072018337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15267117190006987434862261 1431292236563155072018337)
                    ·
                      rfl

theorem cell23_8362295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_8362295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362295 prefixEnd_8362295 := by exact prefixLift 8362295
  have htrace : WordTrace (prefixWord ++ tailWord_8362295) baseStart_8362295 baseEnd_8362295 := by
    simpa [prefixWord, tailWord_8362295, baseEnd_8362295] using wordTrace_append hprefix tailTrace_8362295
  have hstable : (prefixWord ++ tailWord_8362295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362295).length < 2 ^ (prefixWord ++ tailWord_8362295).sum := by decide
  have hdescent : baseEnd_8362295 < baseStart_8362295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362312 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 2, 5]
def baseStart_8362312 : Nat := 118140960795 + 8362312 * 2 ^ 59
def prefixEnd_8362312 : Nat := 4983230072969 + 3 ^ 40 * 8362312 * 2
def baseEnd_8362312 : Nat := 1431295146286863883180811

theorem tailTrace_8362312 : CollatzResearch.WordTrace tailWord_8362312 prefixEnd_8362312 1431295146286863883180811 := by
  unfold tailWord_8362312
  simp only [CollatzResearch.WordTrace]
  refine ⟨152499287640389634016176595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203332383520519512021568793 152499287640389634016176595)
  ·
    refine ⟨228748931460584451024264893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152499287640389634016176595 228748931460584451024264893)
    ·
      refine ⟨85780849297719169134099335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228748931460584451024264893 85780849297719169134099335)
      ·
        refine ⟨128671273946578753701149003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85780849297719169134099335 128671273946578753701149003)
        ·
          refine ⟨193006910919868130551723505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128671273946578753701149003 193006910919868130551723505)
          ·
            refine ⟨144755183189901097913792629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193006910919868130551723505 144755183189901097913792629)
            ·
              refine ⟨13570798424053227929418059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144755183189901097913792629 13570798424053227929418059)
              ·
                refine ⟨20356197636079841894127089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13570798424053227929418059 20356197636079841894127089)
                ·
                  refine ⟨15267148227059881420595317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20356197636079841894127089 15267148227059881420595317)
                  ·
                    refine ⟨1431295146286863883180811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15267148227059881420595317 1431295146286863883180811)
                    ·
                      rfl

theorem cell23_8362312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_8362312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362312 prefixEnd_8362312 := by exact prefixLift 8362312
  have htrace : WordTrace (prefixWord ++ tailWord_8362312) baseStart_8362312 baseEnd_8362312 := by
    simpa [prefixWord, tailWord_8362312, baseEnd_8362312] using wordTrace_append hprefix tailTrace_8362312
  have hstable : (prefixWord ++ tailWord_8362312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362312).length < 2 ^ (prefixWord ++ tailWord_8362312).sum := by decide
  have hdescent : baseEnd_8362312 < baseStart_8362312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362335 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_8362335 : Nat := 118140960795 + 8362335 * 2 ^ 59
def prefixEnd_8362335 : Nat := 4983230072969 + 3 ^ 40 * 8362335 * 2
def baseEnd_8362335 : Nat := 4293897248915645059554827

theorem tailTrace_8362335 : CollatzResearch.WordTrace tailWord_8362335 prefixEnd_8362335 4293897248915645059554827 := by
  unfold tailWord_8362335
  simp only [CollatzResearch.WordTrace]
  refine ⟨304999414159695942960440459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203332942773130628640293639 304999414159695942960440459)
  ·
    refine ⟨457499121239543914440660689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304999414159695942960440459 457499121239543914440660689)
    ·
      refine ⟨343124340929657935830495517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457499121239543914440660689 343124340929657935830495517)
      ·
        refine ⟨128671627848621725936435819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343124340929657935830495517 128671627848621725936435819)
        ·
          refine ⟨193007441772932588904653729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128671627848621725936435819 193007441772932588904653729)
          ·
            refine ⟨144755581329699441678490297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193007441772932588904653729 144755581329699441678490297)
            ·
              refine ⟨108566685997274581258867723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144755581329699441678490297 108566685997274581258867723)
              ·
                refine ⟨162850028995911871888301585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108566685997274581258867723 162850028995911871888301585)
                ·
                  refine ⟨122137521746933903916226189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162850028995911871888301585 122137521746933903916226189)
                  ·
                    refine ⟨45801570655100213968584821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122137521746933903916226189 45801570655100213968584821)
                    ·
                      refine ⟨4293897248915645059554827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45801570655100213968584821 4293897248915645059554827)
                      ·
                        rfl

theorem cell23_8362335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_8362335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362335 prefixEnd_8362335 := by exact prefixLift 8362335
  have htrace : WordTrace (prefixWord ++ tailWord_8362335) baseStart_8362335 baseEnd_8362335 := by
    simpa [prefixWord, tailWord_8362335, baseEnd_8362335] using wordTrace_append hprefix tailTrace_8362335
  have hstable : (prefixWord ++ tailWord_8362335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362335).length < 2 ^ (prefixWord ++ tailWord_8362335).sum := by decide
  have hdescent : baseEnd_8362335 < baseStart_8362335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362345 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_8362345 : Nat := 118140960795 + 8362345 * 2 ^ 59
def prefixEnd_8362345 : Nat := 4983230072969 + 3 ^ 40 * 8362345 * 2
def baseEnd_8362345 : Nat := 4293902383722190020429781

theorem tailTrace_8362345 : CollatzResearch.WordTrace tailWord_8362345 prefixEnd_8362345 4293902383722190020429781 := by
  unfold tailWord_8362345
  simp only [CollatzResearch.WordTrace]
  refine ⟨304999778889659714668304489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203333185926439809778869659 304999778889659714668304489)
  ·
    refine ⟨228749834167244786001228367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304999778889659714668304489 228749834167244786001228367)
    ·
      refine ⟨343124751250867179001842551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228749834167244786001228367 343124751250867179001842551)
      ·
        refine ⟨514687126876300768502763827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343124751250867179001842551 514687126876300768502763827)
        ·
          refine ⟨772030690314451152754145741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514687126876300768502763827 772030690314451152754145741)
          ·
            refine ⟨289511508867919182282804653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 772030690314451152754145741 289511508867919182282804653)
            ·
              refine ⟨108566815825469693356051745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289511508867919182282804653 108566815825469693356051745)
              ·
                refine ⟨81425111869102270017038809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108566815825469693356051745 81425111869102270017038809)
                ·
                  refine ⟨61068833901826702512779107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81425111869102270017038809 61068833901826702512779107)
                  ·
                    refine ⟨91603250852740053769168661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61068833901826702512779107 91603250852740053769168661)
                    ·
                      refine ⟨4293902383722190020429781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91603250852740053769168661 4293902383722190020429781)
                      ·
                        rfl

theorem cell23_8362345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_8362345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362345 prefixEnd_8362345 := by exact prefixLift 8362345
  have htrace : WordTrace (prefixWord ++ tailWord_8362345) baseStart_8362345 baseEnd_8362345 := by
    simpa [prefixWord, tailWord_8362345, baseEnd_8362345] using wordTrace_append hprefix tailTrace_8362345
  have hstable : (prefixWord ++ tailWord_8362345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362345).length < 2 ^ (prefixWord ++ tailWord_8362345).sum := by decide
  have hdescent : baseEnd_8362345 < baseStart_8362345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362349 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_8362349 : Nat := 118140960795 + 8362349 * 2 ^ 59
def prefixEnd_8362349 : Nat := 4983230072969 + 3 ^ 40 * 8362349 * 2
def baseEnd_8362349 : Nat := 4293904437644808004779763

theorem tailTrace_8362349 : CollatzResearch.WordTrace tailWord_8362349 prefixEnd_8362349 4293904437644808004779763 := by
  unfold tailWord_8362349
  simp only [CollatzResearch.WordTrace]
  refine ⟨304999924781645223351450101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203333283187763482234300067 304999924781645223351450101)
  ·
    refine ⟨28593742948279239689198447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304999924781645223351450101 28593742948279239689198447)
    ·
      refine ⟨42890614422418859533797671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28593742948279239689198447 42890614422418859533797671)
      ·
        refine ⟨64335921633628289300696507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42890614422418859533797671 64335921633628289300696507)
        ·
          refine ⟨96503882450442433951044761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64335921633628289300696507 96503882450442433951044761)
          ·
            refine ⟨72377911837831825463283571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96503882450442433951044761 72377911837831825463283571)
            ·
              refine ⟨108566867756747738194925357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72377911837831825463283571 108566867756747738194925357)
              ·
                refine ⟨40712575408780401823097009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108566867756747738194925357 40712575408780401823097009)
                ·
                  refine ⟨30534431556585301367322757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40712575408780401823097009 30534431556585301367322757)
                  ·
                    refine ⟨5725205916859744006373017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30534431556585301367322757 5725205916859744006373017)
                    ·
                      refine ⟨4293904437644808004779763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725205916859744006373017 4293904437644808004779763)
                      ·
                        rfl

theorem cell23_8362349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_8362349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362349 prefixEnd_8362349 := by exact prefixLift 8362349
  have htrace : WordTrace (prefixWord ++ tailWord_8362349) baseStart_8362349 baseEnd_8362349 := by
    simpa [prefixWord, tailWord_8362349, baseEnd_8362349] using wordTrace_append hprefix tailTrace_8362349
  have hstable : (prefixWord ++ tailWord_8362349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362349).length < 2 ^ (prefixWord ++ tailWord_8362349).sum := by decide
  have hdescent : baseEnd_8362349 < baseStart_8362349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362352 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 3]
def baseStart_8362352 : Nat := 118140960795 + 8362352 * 2 ^ 59
def prefixEnd_8362352 : Nat := 4983230072969 + 3 ^ 40 * 8362352 * 2
def baseEnd_8362352 : Nat := 4293905978086771493042249

theorem tailTrace_8362352 : CollatzResearch.WordTrace tailWord_8362352 prefixEnd_8362352 4293905978086771493042249 := by
  unfold tailWord_8362352
  simp only [CollatzResearch.WordTrace]
  refine ⟨152500017100317177431904655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203333356133756236575872873 152500017100317177431904655)
  ·
    refine ⟨228750025650475766147856983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152500017100317177431904655 228750025650475766147856983)
    ·
      refine ⟨343125038475713649221785475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228750025650475766147856983 343125038475713649221785475)
      ·
        refine ⟨514687557713570473832678213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343125038475713649221785475 514687557713570473832678213)
        ·
          refine ⟨96503917071294463843627165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514687557713570473832678213 96503917071294463843627165)
          ·
            refine ⟨36188968901735423941360187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96503917071294463843627165 36188968901735423941360187)
            ·
              refine ⟨54283453352603135912040281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36188968901735423941360187 54283453352603135912040281)
              ·
                refine ⟨40712590014452351934030211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54283453352603135912040281 40712590014452351934030211)
                ·
                  refine ⟨61068885021678527901045317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40712590014452351934030211 61068885021678527901045317)
                  ·
                    refine ⟨11450415941564723981445997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61068885021678527901045317 11450415941564723981445997)
                    ·
                      refine ⟨4293905978086771493042249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450415941564723981445997 4293905978086771493042249)
                      ·
                        rfl

theorem cell23_8362352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_8362352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362352 prefixEnd_8362352 := by exact prefixLift 8362352
  have htrace : WordTrace (prefixWord ++ tailWord_8362352) baseStart_8362352 baseEnd_8362352 := by
    simpa [prefixWord, tailWord_8362352, baseEnd_8362352] using wordTrace_append hprefix tailTrace_8362352
  have hstable : (prefixWord ++ tailWord_8362352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362352).length < 2 ^ (prefixWord ++ tailWord_8362352).sum := by decide
  have hdescent : baseEnd_8362352 < baseStart_8362352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362369 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_8362369 : Nat := 118140960795 + 8362369 * 2 ^ 59
def prefixEnd_8362369 : Nat := 4983230072969 + 3 ^ 40 * 8362369 * 2
def baseEnd_8362369 : Nat := 4293914707257897926529671

theorem tailTrace_8362369 : CollatzResearch.WordTrace tailWord_8362369 prefixEnd_8362369 4293914707257897926529671 := by
  unfold tailWord_8362369
  simp only [CollatzResearch.WordTrace]
  refine ⟨305000654241572766767178161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203333769494381844511452107 305000654241572766767178161)
  ·
    refine ⟨228750490681179575075383621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305000654241572766767178161 228750490681179575075383621)
    ·
      refine ⟨42890717002721170326634429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228750490681179575075383621 42890717002721170326634429)
      ·
        refine ⟨16084018876020438872487911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42890717002721170326634429 16084018876020438872487911)
        ·
          refine ⟨24126028314030658308731867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16084018876020438872487911 24126028314030658308731867)
          ·
            refine ⟨36189042471045987463097801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24126028314030658308731867 36189042471045987463097801)
            ·
              refine ⟨27141781853284490597323351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36189042471045987463097801 27141781853284490597323351)
              ·
                refine ⟨40712672779926735895985027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27141781853284490597323351 40712672779926735895985027)
                ·
                  refine ⟨61069009169890103843977541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40712672779926735895985027 61069009169890103843977541)
                  ·
                    refine ⟨11450439219354394470745789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61069009169890103843977541 11450439219354394470745789)
                    ·
                      refine ⟨4293914707257897926529671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450439219354394470745789 4293914707257897926529671)
                      ·
                        rfl

theorem cell23_8362369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_8362369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362369 prefixEnd_8362369 := by exact prefixLift 8362369
  have htrace : WordTrace (prefixWord ++ tailWord_8362369) baseStart_8362369 baseEnd_8362369 := by
    simpa [prefixWord, tailWord_8362369, baseEnd_8362369] using wordTrace_append hprefix tailTrace_8362369
  have hstable : (prefixWord ++ tailWord_8362369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362369).length < 2 ^ (prefixWord ++ tailWord_8362369).sum := by decide
  have hdescent : baseEnd_8362369 < baseStart_8362369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362420 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_8362420 : Nat := 118140960795 + 8362420 * 2 ^ 59
def prefixEnd_8362420 : Nat := 4983230072969 + 3 ^ 40 * 8362420 * 2
def baseEnd_8362420 : Nat := 4293940894771277226991937

theorem tailTrace_8362420 : CollatzResearch.WordTrace tailWord_8362420 prefixEnd_8362420 4293940894771277226991937 := by
  unfold tailWord_8362420
  simp only [CollatzResearch.WordTrace]
  refine ⟨152501257182194001238642357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203335009576258668318189809 152501257182194001238642357)
  ·
    refine ⟨14296992860830687616122721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152501257182194001238642357 14296992860830687616122721)
    ·
      refine ⟨10722744645623015712092041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14296992860830687616122721 10722744645623015712092041)
      ·
        refine ⟨8042058484217261784069031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10722744645623015712092041 8042058484217261784069031)
        ·
          refine ⟨12063087726325892676103547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042058484217261784069031 12063087726325892676103547)
          ·
            refine ⟨18094631589488839014155321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063087726325892676103547 18094631589488839014155321)
            ·
              refine ⟨13570973692116629260616491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18094631589488839014155321 13570973692116629260616491)
              ·
                refine ⟨20356460538174943890924737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13570973692116629260616491 20356460538174943890924737)
                ·
                  refine ⟨15267345403631207918193553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20356460538174943890924737 15267345403631207918193553)
                  ·
                    refine ⟨11450509052723405938645165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15267345403631207918193553 11450509052723405938645165)
                    ·
                      refine ⟨4293940894771277226991937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450509052723405938645165 4293940894771277226991937)
                      ·
                        rfl

theorem cell23_8362420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_8362420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362420 prefixEnd_8362420 := by exact prefixLift 8362420
  have htrace : WordTrace (prefixWord ++ tailWord_8362420) baseStart_8362420 baseEnd_8362420 := by
    simpa [prefixWord, tailWord_8362420, baseEnd_8362420] using wordTrace_append hprefix tailTrace_8362420
  have hstable : (prefixWord ++ tailWord_8362420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362420).length < 2 ^ (prefixWord ++ tailWord_8362420).sum := by decide
  have hdescent : baseEnd_8362420 < baseStart_8362420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362456 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 3, 2, 2]
def baseStart_8362456 : Nat := 118140960795 + 8362456 * 2 ^ 59
def prefixEnd_8362456 : Nat := 4983230072969 + 3 ^ 40 * 8362456 * 2
def baseEnd_8362456 : Nat := 4293959380074839086141771

theorem tailTrace_8362456 : CollatzResearch.WordTrace tailWord_8362456 prefixEnd_8362456 4293959380074839086141771 := by
  unfold tailWord_8362456
  simp only [CollatzResearch.WordTrace]
  refine ⟨152501913696128790312797611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203335884928171720417063481 152501913696128790312797611)
  ·
    refine ⟨228752870544193185469196417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152501913696128790312797611 228752870544193185469196417)
    ·
      refine ⟨171564652908144889101897313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228752870544193185469196417 171564652908144889101897313)
      ·
        refine ⟨128673489681108666826422985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171564652908144889101897313 128673489681108666826422985)
        ·
          refine ⟨96505117260831500119817239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128673489681108666826422985 96505117260831500119817239)
          ·
            refine ⟨144757675891247250179725859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96505117260831500119817239 144757675891247250179725859)
            ·
              refine ⟨217136513836870875269588789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144757675891247250179725859 217136513836870875269588789)
              ·
                refine ⟨20356548172206644556523949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217136513836870875269588789 20356548172206644556523949)
                ·
                  refine ⟨7633705564577491708696481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20356548172206644556523949 7633705564577491708696481)
                  ·
                    refine ⟨5725279173433118781522361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7633705564577491708696481 5725279173433118781522361)
                    ·
                      refine ⟨4293959380074839086141771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725279173433118781522361 4293959380074839086141771)
                      ·
                        rfl

theorem cell23_8362456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_8362456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362456 prefixEnd_8362456 := by exact prefixLift 8362456
  have htrace : WordTrace (prefixWord ++ tailWord_8362456) baseStart_8362456 baseEnd_8362456 := by
    simpa [prefixWord, tailWord_8362456, baseEnd_8362456] using wordTrace_append hprefix tailTrace_8362456
  have hstable : (prefixWord ++ tailWord_8362456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362456).length < 2 ^ (prefixWord ++ tailWord_8362456).sum := by decide
  have hdescent : baseEnd_8362456 < baseStart_8362456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362489 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 3]
def baseStart_8362489 : Nat := 118140960795 + 8362489 * 2 ^ 59
def prefixEnd_8362489 : Nat := 4983230072969 + 3 ^ 40 * 8362489 * 2
def baseEnd_8362489 : Nat := 4293976324936437457029119

theorem tailTrace_8362489 : CollatzResearch.WordTrace tailWord_8362489 prefixEnd_8362489 4293976324936437457029119 := by
  unfold tailWord_8362489
  simp only [CollatzResearch.WordTrace]
  refine ⟨305005031001138027261546521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203336687334092018174364347 305005031001138027261546521)
  ·
    refine ⟨228753773250853520446159891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305005031001138027261546521 228753773250853520446159891)
    ·
      refine ⟨343130659876280280669239837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228753773250853520446159891 343130659876280280669239837)
      ·
        refine ⟨128673997453605105250964939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343130659876280280669239837 128673997453605105250964939)
        ·
          refine ⟨193010996180407657876447409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128673997453605105250964939 193010996180407657876447409)
          ·
            refine ⟨144758247135305743407335557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193010996180407657876447409 144758247135305743407335557)
            ·
              refine ⟨27142171337869826888875417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144758247135305743407335557 27142171337869826888875417)
              ·
                refine ⟨20356628503402370166656563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27142171337869826888875417 20356628503402370166656563)
                ·
                  refine ⟨30534942755103555249984845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20356628503402370166656563 30534942755103555249984845)
                  ·
                    refine ⟨11450603533163833218744317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30534942755103555249984845 11450603533163833218744317)
                    ·
                      refine ⟨4293976324936437457029119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450603533163833218744317 4293976324936437457029119)
                      ·
                        rfl

theorem cell23_8362489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_8362489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362489 prefixEnd_8362489 := by exact prefixLift 8362489
  have htrace : WordTrace (prefixWord ++ tailWord_8362489) baseStart_8362489 baseEnd_8362489 := by
    simpa [prefixWord, tailWord_8362489, baseEnd_8362489] using wordTrace_append hprefix tailTrace_8362489
  have hstable : (prefixWord ++ tailWord_8362489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362489).length < 2 ^ (prefixWord ++ tailWord_8362489).sum := by decide
  have hdescent : baseEnd_8362489 < baseStart_8362489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362506 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_8362506 : Nat := 118140960795 + 8362506 * 2 ^ 59
def prefixEnd_8362506 : Nat := 4983230072969 + 3 ^ 40 * 8362506 * 2
def baseEnd_8362506 : Nat := 4293985054107563890516541

theorem tailTrace_8362506 : CollatzResearch.WordTrace tailWord_8362506 prefixEnd_8362506 4293985054107563890516541 := by
  unfold tailWord_8362506
  simp only [CollatzResearch.WordTrace]
  refine ⟨76251412760519109791228843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203337100694717626109943581 76251412760519109791228843)
  ·
    refine ⟨114377119140778664686843265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76251412760519109791228843 114377119140778664686843265)
    ·
      refine ⟨85782839355583998515132449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114377119140778664686843265 85782839355583998515132449)
      ·
        refine ⟨64337129516687998886349337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85782839355583998515132449 64337129516687998886349337)
        ·
          refine ⟨48252847137515999164762003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64337129516687998886349337 48252847137515999164762003)
          ·
            refine ⟨72379270706273998747143005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48252847137515999164762003 72379270706273998747143005)
            ·
              refine ⟨27142226514852749530178627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72379270706273998747143005 27142226514852749530178627)
              ·
                refine ⟨40713339772279124295267941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27142226514852749530178627 40713339772279124295267941)
                ·
                  refine ⟨7633751207302335805362739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40713339772279124295267941 7633751207302335805362739)
                  ·
                    refine ⟨11450626810953503708044109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7633751207302335805362739 11450626810953503708044109)
                    ·
                      refine ⟨4293985054107563890516541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450626810953503708044109 4293985054107563890516541)
                      ·
                        rfl

theorem cell23_8362506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_8362506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362506 prefixEnd_8362506 := by exact prefixLift 8362506
  have htrace : WordTrace (prefixWord ++ tailWord_8362506) baseStart_8362506 baseEnd_8362506 := by
    simpa [prefixWord, tailWord_8362506, baseEnd_8362506] using wordTrace_append hprefix tailTrace_8362506
  have hstable : (prefixWord ++ tailWord_8362506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362506).length < 2 ^ (prefixWord ++ tailWord_8362506).sum := by decide
  have hdescent : baseEnd_8362506 < baseStart_8362506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362512 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_8362512 : Nat := 118140960795 + 8362512 * 2 ^ 59
def prefixEnd_8362512 : Nat := 4983230072969 + 3 ^ 40 * 8362512 * 2
def baseEnd_8362512 : Nat := 4293988134991490867041513

theorem tailTrace_8362512 : CollatzResearch.WordTrace tailWord_8362512 prefixEnd_8362512 4293988134991490867041513 := by
  unfold tailWord_8362512
  simp only [CollatzResearch.WordTrace]
  refine ⟨152502934940027351094816895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203337246586703134793089193 152502934940027351094816895)
  ·
    refine ⟨228754402410041026642225343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152502934940027351094816895 228754402410041026642225343)
    ·
      refine ⟨343131603615061539963338015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228754402410041026642225343 343131603615061539963338015)
      ·
        refine ⟨514697405422592309945007023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343131603615061539963338015 514697405422592309945007023)
        ·
          refine ⟨772046108133888464917510535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514697405422592309945007023 772046108133888464917510535)
          ·
            refine ⟨1158069162200832697376265803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772046108133888464917510535 1158069162200832697376265803)
            ·
              refine ⟨1737103743301249046064398705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158069162200832697376265803 1737103743301249046064398705)
              ·
                refine ⟨1302827807475936784548299029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737103743301249046064398705 1302827807475936784548299029)
                ·
                  refine ⟨61070053475434536775701517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1302827807475936784548299029 61070053475434536775701517)
                  ·
                    refine ⟨22901270053287951290888069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61070053475434536775701517 22901270053287951290888069)
                    ·
                      refine ⟨4293988134991490867041513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22901270053287951290888069 4293988134991490867041513)
                      ·
                        rfl

theorem cell23_8362512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_8362512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362512 prefixEnd_8362512 := by exact prefixLift 8362512
  have htrace : WordTrace (prefixWord ++ tailWord_8362512) baseStart_8362512 baseEnd_8362512 := by
    simpa [prefixWord, tailWord_8362512, baseEnd_8362512] using wordTrace_append hprefix tailTrace_8362512
  have hstable : (prefixWord ++ tailWord_8362512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362512).length < 2 ^ (prefixWord ++ tailWord_8362512).sum := by decide
  have hdescent : baseEnd_8362512 < baseStart_8362512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362546 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_8362546 : Nat := 118140960795 + 8362546 * 2 ^ 59
def prefixEnd_8362546 : Nat := 4983230072969 + 3 ^ 40 * 8362546 * 2
def baseEnd_8362546 : Nat := 4294005593333743734016357

theorem tailTrace_8362546 : CollatzResearch.WordTrace tailWord_8362546 prefixEnd_8362546 4294005593333743734016357 := by
  unfold tailWord_8362546
  simp only [CollatzResearch.WordTrace]
  refine ⟨76251777490482881499092873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203338073307954350664247661 76251777490482881499092873)
  ·
    refine ⟨57188833117862161124319655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76251777490482881499092873 57188833117862161124319655)
    ·
      refine ⟨85783249676793241686479483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57188833117862161124319655 85783249676793241686479483)
      ·
        refine ⟨128674874515189862529719225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85783249676793241686479483 128674874515189862529719225)
        ·
          refine ⟨96506155886392396897289419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128674874515189862529719225 96506155886392396897289419)
          ·
            refine ⟨144759233829588595345934129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96506155886392396897289419 144759233829588595345934129)
            ·
              refine ⟨108569425372191446509450597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144759233829588595345934129 108569425372191446509450597)
              ·
                refine ⟨20356767257285896220521987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108569425372191446509450597 20356767257285896220521987)
                ·
                  refine ⟨30535150885928844330782981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20356767257285896220521987 30535150885928844330782981)
                  ·
                    refine ⟨5725340791111658312021809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30535150885928844330782981 5725340791111658312021809)
                    ·
                      refine ⟨4294005593333743734016357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725340791111658312021809 4294005593333743734016357)
                      ·
                        rfl

theorem cell23_8362546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_8362546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362546 prefixEnd_8362546 := by exact prefixLift 8362546
  have htrace : WordTrace (prefixWord ++ tailWord_8362546) baseStart_8362546 baseEnd_8362546 := by
    simpa [prefixWord, tailWord_8362546, baseEnd_8362546] using wordTrace_append hprefix tailTrace_8362546
  have hstable : (prefixWord ++ tailWord_8362546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362546).length < 2 ^ (prefixWord ++ tailWord_8362546).sum := by decide
  have hdescent : baseEnd_8362546 < baseStart_8362546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362549 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_8362549 : Nat := 118140960795 + 8362549 * 2 ^ 59
def prefixEnd_8362549 : Nat := 4983230072969 + 3 ^ 40 * 8362549 * 2
def baseEnd_8362549 : Nat := 4294007133775707222278843

theorem tailTrace_8362549 : CollatzResearch.WordTrace tailWord_8362549 prefixEnd_8362549 4294007133775707222278843 := by
  unfold tailWord_8362549
  simp only [CollatzResearch.WordTrace]
  refine ⟨305007219380920657508730701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203338146253947105005820467 305007219380920657508730701)
  ·
    refine ⟨114377707267845246565774013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305007219380920657508730701 114377707267845246565774013)
    ·
      refine ⟨42891640225441967462165255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114377707267845246565774013 42891640225441967462165255)
      ·
        refine ⟨64337460338162951193247883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42891640225441967462165255 64337460338162951193247883)
        ·
          refine ⟨96506190507244426789871825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64337460338162951193247883 96506190507244426789871825)
          ·
            refine ⟨72379642880433320092403869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96506190507244426789871825 72379642880433320092403869)
            ·
              refine ⟨27142366080162495034651451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72379642880433320092403869 27142366080162495034651451)
              ·
                refine ⟨40713549120243742551977177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27142366080162495034651451 40713549120243742551977177)
                ·
                  refine ⟨30535161840182806913982883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40713549120243742551977177 30535161840182806913982883)
                  ·
                    refine ⟨45802742760274210370974325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30535161840182806913982883 45802742760274210370974325)
                    ·
                      refine ⟨4294007133775707222278843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45802742760274210370974325 4294007133775707222278843)
                      ·
                        rfl

theorem cell23_8362549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_8362549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362549 prefixEnd_8362549 := by exact prefixLift 8362549
  have htrace : WordTrace (prefixWord ++ tailWord_8362549) baseStart_8362549 baseEnd_8362549 := by
    simpa [prefixWord, tailWord_8362549, baseEnd_8362549] using wordTrace_append hprefix tailTrace_8362549
  have hstable : (prefixWord ++ tailWord_8362549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362549).length < 2 ^ (prefixWord ++ tailWord_8362549).sum := by decide
  have hdescent : baseEnd_8362549 < baseStart_8362549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362550 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_8362550 : Nat := 118140960795 + 8362550 * 2 ^ 59
def prefixEnd_8362550 : Nat := 4983230072969 + 3 ^ 40 * 8362550 * 2
def baseEnd_8362550 : Nat := 4294007647256361718366339

theorem tailTrace_8362550 : CollatzResearch.WordTrace tailWord_8362550 prefixEnd_8362550 4294007647256361718366339 := by
  unfold tailWord_8362550
  simp only [CollatzResearch.WordTrace]
  refine ⟨19062953490869814667469819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203338170569278023119678069 19062953490869814667469819)
  ·
    refine ⟨28594430236304722001204729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19062953490869814667469819 28594430236304722001204729)
    ·
      refine ⟨21445822677228541500903547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28594430236304722001204729 21445822677228541500903547)
      ·
        refine ⟨32168734015842812251355321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21445822677228541500903547 32168734015842812251355321)
        ·
          refine ⟨24126550511882109188516491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32168734015842812251355321 24126550511882109188516491)
          ·
            refine ⟨36189825767823163782774737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24126550511882109188516491 36189825767823163782774737)
            ·
              refine ⟨27142369325867372837081053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36189825767823163782774737 27142369325867372837081053)
              ·
                refine ⟨10178388497200264813905395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27142369325867372837081053 10178388497200264813905395)
                ·
                  refine ⟨15267582745800397220858093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10178388497200264813905395 15267582745800397220858093)
                  ·
                    refine ⟨5725343529675148957821785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15267582745800397220858093 5725343529675148957821785)
                    ·
                      refine ⟨4294007647256361718366339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725343529675148957821785 4294007647256361718366339)
                      ·
                        rfl

theorem cell23_8362550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_8362550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362550 prefixEnd_8362550 := by exact prefixLift 8362550
  have htrace : WordTrace (prefixWord ++ tailWord_8362550) baseStart_8362550 baseEnd_8362550 := by
    simpa [prefixWord, tailWord_8362550, baseEnd_8362550] using wordTrace_append hprefix tailTrace_8362550
  have hstable : (prefixWord ++ tailWord_8362550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362550).length < 2 ^ (prefixWord ++ tailWord_8362550).sum := by decide
  have hdescent : baseEnd_8362550 < baseStart_8362550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362580 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_8362580 : Nat := 118140960795 + 8362580 * 2 ^ 59
def prefixEnd_8362580 : Nat := 4983230072969 + 3 ^ 40 * 8362580 * 2
def baseEnd_8362580 : Nat := 4294023051675996600991201

theorem tailTrace_8362580 : CollatzResearch.WordTrace tailWord_8362580 prefixEnd_8362580 4294023051675996600991201 := by
  unfold tailWord_8362580
  simp only [CollatzResearch.WordTrace]
  refine ⟨152504175021904174901554597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203338900029205566535406129 152504175021904174901554597)
  ·
    refine ⟨28594532816607032794041487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152504175021904174901554597 28594532816607032794041487)
    ·
      refine ⟨42891799224910549191062231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28594532816607032794041487 42891799224910549191062231)
      ·
        refine ⟨64337698837365823786593347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42891799224910549191062231 64337698837365823786593347)
        ·
          refine ⟨96506548256048735679890021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64337698837365823786593347 96506548256048735679890021)
          ·
            refine ⟨18094977798009137939979379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96506548256048735679890021 18094977798009137939979379)
            ·
              refine ⟨27142466697013706909969069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18094977798009137939979379 27142466697013706909969069)
              ·
                refine ⟨10178425011380140091238401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27142466697013706909969069 10178425011380140091238401)
                ·
                  refine ⟨7633818758535105068428801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10178425011380140091238401 7633818758535105068428801)
                  ·
                    refine ⟨5725364068901328801321601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7633818758535105068428801 5725364068901328801321601)
                    ·
                      refine ⟨4294023051675996600991201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725364068901328801321601 4294023051675996600991201)
                      ·
                        rfl

theorem cell23_8362580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_8362580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362580 prefixEnd_8362580 := by exact prefixLift 8362580
  have htrace : WordTrace (prefixWord ++ tailWord_8362580) baseStart_8362580 baseEnd_8362580 := by
    simpa [prefixWord, tailWord_8362580, baseEnd_8362580] using wordTrace_append hprefix tailTrace_8362580
  have hstable : (prefixWord ++ tailWord_8362580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362580).length < 2 ^ (prefixWord ++ tailWord_8362580).sum := by decide
  have hdescent : baseEnd_8362580 < baseStart_8362580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362619 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 4]
def baseStart_8362619 : Nat := 118140960795 + 8362619 * 2 ^ 59
def prefixEnd_8362619 : Nat := 4983230072969 + 3 ^ 40 * 8362619 * 2
def baseEnd_8362619 : Nat := 4294043077421521948403521

theorem tailTrace_8362619 : CollatzResearch.WordTrace tailWord_8362619 prefixEnd_8362619 4294043077421521948403521 := by
  unfold tailWord_8362619
  simp only [CollatzResearch.WordTrace]
  refine ⟨305009772490667059463778911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203339848327111372975852607 305009772490667059463778911)
  ·
    refine ⟨457514658736000589195668367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305009772490667059463778911 457514658736000589195668367)
    ·
      refine ⟨686271988104000883793502551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457514658736000589195668367 686271988104000883793502551)
      ·
        refine ⟨1029407982156001325690253827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686271988104000883793502551 1029407982156001325690253827)
        ·
          refine ⟨1544111973234001988535380741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029407982156001325690253827 1544111973234001988535380741)
          ·
            refine ⟨289520994981375372850383889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1544111973234001988535380741 289520994981375372850383889)
            ·
              refine ⟨217140746236031529637787917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289520994981375372850383889 217140746236031529637787917)
              ·
                refine ⟨81427779838511823614170469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217140746236031529637787917 81427779838511823614170469)
                ·
                  refine ⟨15267708719720966927656963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81427779838511823614170469 15267708719720966927656963)
                  ·
                    refine ⟨22901563079581450391485445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15267708719720966927656963 22901563079581450391485445)
                    ·
                      refine ⟨4294043077421521948403521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22901563079581450391485445 4294043077421521948403521)
                      ·
                        rfl

theorem cell23_8362619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 4].length) (baseStart_8362619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362619 prefixEnd_8362619 := by exact prefixLift 8362619
  have htrace : WordTrace (prefixWord ++ tailWord_8362619) baseStart_8362619 baseEnd_8362619 := by
    simpa [prefixWord, tailWord_8362619, baseEnd_8362619] using wordTrace_append hprefix tailTrace_8362619
  have hstable : (prefixWord ++ tailWord_8362619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362619).length < 2 ^ (prefixWord ++ tailWord_8362619).sum := by decide
  have hdescent : baseEnd_8362619 < baseStart_8362619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362639 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 3]
def baseStart_8362639 : Nat := 118140960795 + 8362639 * 2 ^ 59
def prefixEnd_8362639 : Nat := 4983230072969 + 3 ^ 40 * 8362639 * 2
def baseEnd_8362639 : Nat := 4294053347034611870153429

theorem tailTrace_8362639 : CollatzResearch.WordTrace tailWord_8362639 prefixEnd_8362639 4294053347034611870153429 := by
  unfold tailWord_8362639
  simp only [CollatzResearch.WordTrace]
  refine ⟨305010501950594602879506971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203340334633729735253004647 305010501950594602879506971)
  ·
    refine ⟨457515752925891904319260457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305010501950594602879506971 457515752925891904319260457)
    ·
      refine ⟨343136814694418928239445343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457515752925891904319260457 343136814694418928239445343)
      ·
        refine ⟨514705222041628392359168015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343136814694418928239445343 514705222041628392359168015)
        ·
          refine ⟨772057833062442588538752023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514705222041628392359168015 772057833062442588538752023)
          ·
            refine ⟨1158086749593663882808128035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772057833062442588538752023 1158086749593663882808128035)
            ·
              refine ⟨1737130124390495824212192053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158086749593663882808128035 1737130124390495824212192053)
              ·
                refine ⟨162855949161608983519893005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1737130124390495824212192053 162855949161608983519893005)
                ·
                  refine ⟨61070980935603368819959877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162855949161608983519893005 61070980935603368819959877)
                  ·
                    refine ⟨11450808925425631653742477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61070980935603368819959877 11450808925425631653742477)
                    ·
                      refine ⟨4294053347034611870153429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450808925425631653742477 4294053347034611870153429)
                      ·
                        rfl

theorem cell23_8362639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_8362639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362639 prefixEnd_8362639 := by exact prefixLift 8362639
  have htrace : WordTrace (prefixWord ++ tailWord_8362639) baseStart_8362639 baseEnd_8362639 := by
    simpa [prefixWord, tailWord_8362639, baseEnd_8362639] using wordTrace_append hprefix tailTrace_8362639
  have hstable : (prefixWord ++ tailWord_8362639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362639).length < 2 ^ (prefixWord ++ tailWord_8362639).sum := by decide
  have hdescent : baseEnd_8362639 < baseStart_8362639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362650 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_8362650 : Nat := 118140960795 + 8362650 * 2 ^ 59
def prefixEnd_8362650 : Nat := 4983230072969 + 3 ^ 40 * 8362650 * 2
def baseEnd_8362650 : Nat := 1431352998440603775705293

theorem tailTrace_8362650 : CollatzResearch.WordTrace tailWord_8362650 prefixEnd_8362650 1431352998440603775705293 := by
  unfold tailWord_8362650
  simp only [CollatzResearch.WordTrace]
  refine ⟨76252725788388687939539351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203340602102369834505438269 76252725788388687939539351)
  ·
    refine ⟨114379088682583031909309027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76252725788388687939539351 114379088682583031909309027)
    ·
      refine ⟨171568633023874547863963541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114379088682583031909309027 171568633023874547863963541)
      ·
        refine ⟨8042279672994119431123291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171568633023874547863963541 8042279672994119431123291)
        ·
          refine ⟨12063419509491179146684937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042279672994119431123291 12063419509491179146684937)
          ·
            refine ⟨9047564632118384360013703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12063419509491179146684937 9047564632118384360013703)
            ·
              refine ⟨13571346948177576540020555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047564632118384360013703 13571346948177576540020555)
              ·
                refine ⟨20357020422266364810030833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13571346948177576540020555 20357020422266364810030833)
                ·
                  refine ⟨15267765316699773607523125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20357020422266364810030833 15267765316699773607523125)
                  ·
                    refine ⟨1431352998440603775705293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15267765316699773607523125 1431352998440603775705293)
                    ·
                      rfl

theorem cell23_8362650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_8362650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362650 prefixEnd_8362650 := by exact prefixLift 8362650
  have htrace : WordTrace (prefixWord ++ tailWord_8362650) baseStart_8362650 baseEnd_8362650 := by
    simpa [prefixWord, tailWord_8362650, baseEnd_8362650] using wordTrace_append hprefix tailTrace_8362650
  have hstable : (prefixWord ++ tailWord_8362650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362650).length < 2 ^ (prefixWord ++ tailWord_8362650).sum := by decide
  have hdescent : baseEnd_8362650 < baseStart_8362650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362670 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_8362670 : Nat := 118140960795 + 8362670 * 2 ^ 59
def prefixEnd_8362670 : Nat := 4983230072969 + 3 ^ 40 * 8362670 * 2
def baseEnd_8362670 : Nat := 4294069264934901248865787

theorem tailTrace_8362670 : CollatzResearch.WordTrace tailWord_8362670 prefixEnd_8362670 4294069264934901248865787 := by
  unfold tailWord_8362670
  simp only [CollatzResearch.WordTrace]
  refine ⟨38126454076685286896735683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203341088408988196782590309 38126454076685286896735683)
  ·
    refine ⟨57189681115027930345103525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38126454076685286896735683 57189681115027930345103525)
    ·
      refine ⟨10723065209067736939706911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57189681115027930345103525 10723065209067736939706911)
      ·
        refine ⟨16084597813601605409560367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10723065209067736939706911 16084597813601605409560367)
        ·
          refine ⟨24126896720402408114340551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16084597813601605409560367 24126896720402408114340551)
          ·
            refine ⟨36190345080603612171510827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24126896720402408114340551 36190345080603612171510827)
            ·
              refine ⟨54285517620905418257266241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36190345080603612171510827 54285517620905418257266241)
              ·
                refine ⟨40714138215679063692949681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54285517620905418257266241 40714138215679063692949681)
                ·
                  refine ⟨30535603661759297769712261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40714138215679063692949681 30535603661759297769712261)
                  ·
                    refine ⟨5725425686579868331821049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30535603661759297769712261 5725425686579868331821049)
                    ·
                      refine ⟨4294069264934901248865787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725425686579868331821049 4294069264934901248865787)
                      ·
                        rfl

theorem cell23_8362670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_8362670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362670 prefixEnd_8362670 := by exact prefixLift 8362670
  have htrace : WordTrace (prefixWord ++ tailWord_8362670) baseStart_8362670 baseEnd_8362670 := by
    simpa [prefixWord, tailWord_8362670, baseEnd_8362670] using wordTrace_append hprefix tailTrace_8362670
  have hstable : (prefixWord ++ tailWord_8362670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362670).length < 2 ^ (prefixWord ++ tailWord_8362670).sum := by decide
  have hdescent : baseEnd_8362670 < baseStart_8362670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362713 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 2, 3, 2]
def baseStart_8362713 : Nat := 118140960795 + 8362713 * 2 ^ 59
def prefixEnd_8362713 : Nat := 4983230072969 + 3 ^ 40 * 8362713 * 2
def baseEnd_8362713 : Nat := 4294091344603044580628089

theorem tailTrace_8362713 : CollatzResearch.WordTrace tailWord_8362713 prefixEnd_8362713 4294091344603044580628089 := by
  unfold tailWord_8362713
  simp only [CollatzResearch.WordTrace]
  refine ⟨305013200952326513517700793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203342133968217675678467195 305013200952326513517700793)
  ·
    refine ⟨228759900714244885138275595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305013200952326513517700793 228759900714244885138275595)
    ·
      refine ⟨343139851071367327707413393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228759900714244885138275595 343139851071367327707413393)
      ·
        refine ⟨257354888303525495780560045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343139851071367327707413393 257354888303525495780560045)
        ·
          refine ⟨96508083113822060917710017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257354888303525495780560045 96508083113822060917710017)
          ·
            refine ⟨72381062335366545688282513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96508083113822060917710017 72381062335366545688282513)
            ·
              refine ⟨54285796751524909266211885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72381062335366545688282513 54285796751524909266211885)
              ·
                refine ⟨20357173781821840974829457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54285796751524909266211885 20357173781821840974829457)
                ·
                  refine ⟨15267880336366380731122093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20357173781821840974829457 15267880336366380731122093)
                  ·
                    refine ⟨5725455126137392774170785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15267880336366380731122093 5725455126137392774170785)
                    ·
                      refine ⟨4294091344603044580628089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725455126137392774170785 4294091344603044580628089)
                      ·
                        rfl

theorem cell23_8362713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_8362713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362713 prefixEnd_8362713 := by exact prefixLift 8362713
  have htrace : WordTrace (prefixWord ++ tailWord_8362713) baseStart_8362713 baseEnd_8362713 := by
    simpa [prefixWord, tailWord_8362713, baseEnd_8362713] using wordTrace_append hprefix tailTrace_8362713
  have hstable : (prefixWord ++ tailWord_8362713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362713).length < 2 ^ (prefixWord ++ tailWord_8362713).sum := by decide
  have hdescent : baseEnd_8362713 < baseStart_8362713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362723 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 1, 5]
def baseStart_8362723 : Nat := 118140960795 + 8362723 * 2 ^ 59
def prefixEnd_8362723 : Nat := 4983230072969 + 3 ^ 40 * 8362723 * 2
def baseEnd_8362723 : Nat := 1431365493136529847167681

theorem tailTrace_8362723 : CollatzResearch.WordTrace tailWord_8362723 prefixEnd_8362723 1431365493136529847167681 := by
  unfold tailWord_8362723
  simp only [CollatzResearch.WordTrace]
  refine ⟨305013565682290285225564823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203342377121526856817043215 305013565682290285225564823)
  ·
    refine ⟨457520348523435427838347235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305013565682290285225564823 457520348523435427838347235)
    ·
      refine ⟨686280522785153141757520853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457520348523435427838347235 686280522785153141757520853)
      ·
        refine ⟨16084699752777026759941895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 686280522785153141757520853 16084699752777026759941895)
        ·
          refine ⟨24127049629165540139912843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16084699752777026759941895 24127049629165540139912843)
          ·
            refine ⟨36190574443748310209869265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24127049629165540139912843 36190574443748310209869265)
            ·
              refine ⟨27142930832811232657401949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36190574443748310209869265 27142930832811232657401949)
              ·
                refine ⟨10178599062304212246525731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27142930832811232657401949 10178599062304212246525731)
                ·
                  refine ⟨15267898593456318369788597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10178599062304212246525731 15267898593456318369788597)
                  ·
                    refine ⟨1431365493136529847167681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15267898593456318369788597 1431365493136529847167681)
                    ·
                      rfl

theorem cell23_8362723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 5].length) (baseStart_8362723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362723 prefixEnd_8362723 := by exact prefixLift 8362723
  have htrace : WordTrace (prefixWord ++ tailWord_8362723) baseStart_8362723 baseEnd_8362723 := by
    simpa [prefixWord, tailWord_8362723, baseEnd_8362723] using wordTrace_append hprefix tailTrace_8362723
  have hstable : (prefixWord ++ tailWord_8362723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362723).length < 2 ^ (prefixWord ++ tailWord_8362723).sum := by decide
  have hdescent : baseEnd_8362723 < baseStart_8362723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362736 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 4, 4]
def baseStart_8362736 : Nat := 118140960795 + 8362736 * 2 ^ 59
def prefixEnd_8362736 : Nat := 4983230072969 + 3 ^ 40 * 8362736 * 2
def baseEnd_8362736 : Nat := 1431367718219365996880161

theorem tailTrace_8362736 : CollatzResearch.WordTrace tailWord_8362736 prefixEnd_8362736 1431367718219365996880161 := by
  unfold tailWord_8362736
  simp only [CollatzResearch.WordTrace]
  refine ⟨152507019915621594222894031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203342693220828792297192041 152507019915621594222894031)
  ·
    refine ⟨228760529873432391334341047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152507019915621594222894031 228760529873432391334341047)
    ·
      refine ⟨343140794810148587001511571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228760529873432391334341047 343140794810148587001511571)
      ·
        refine ⟨514711192215222880502267357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343140794810148587001511571 514711192215222880502267357)
        ·
          refine ⟨193016697080708580188350259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514711192215222880502267357 193016697080708580188350259)
          ·
            refine ⟨289525045621062870282525389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193016697080708580188350259 289525045621062870282525389)
            ·
              refine ⟨108571892107898576355947021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289525045621062870282525389 108571892107898576355947021)
              ·
                refine ⟨40714459540461966133480133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108571892107898576355947021 40714459540461966133480133)
                ·
                  refine ⟨7633961163836618650027525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40714459540461966133480133 7633961163836618650027525)
                  ·
                    refine ⟨1431367718219365996880161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7633961163836618650027525 1431367718219365996880161)
                    ·
                      rfl

theorem cell23_8362736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 4].length) (baseStart_8362736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362736 prefixEnd_8362736 := by exact prefixLift 8362736
  have htrace : WordTrace (prefixWord ++ tailWord_8362736) baseStart_8362736 baseEnd_8362736 := by
    simpa [prefixWord, tailWord_8362736, baseEnd_8362736] using wordTrace_append hprefix tailTrace_8362736
  have hstable : (prefixWord ++ tailWord_8362736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362736).length < 2 ^ (prefixWord ++ tailWord_8362736).sum := by decide
  have hdescent : baseEnd_8362736 < baseStart_8362736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362737 : List Nat := [1, 2, 2, 2, 2, 2, 5, 2, 1, 1, 3]
def baseStart_8362737 : Nat := 118140960795 + 8362737 * 2 ^ 59
def prefixEnd_8362737 : Nat := 4983230072969 + 3 ^ 40 * 8362737 * 2
def baseEnd_8362737 : Nat := 4294103668138752486727979

theorem tailTrace_8362737 : CollatzResearch.WordTrace tailWord_8362737 prefixEnd_8362737 4294103668138752486727979 := by
  unfold tailWord_8362737
  simp only [CollatzResearch.WordTrace]
  refine ⟨305014076304239565616574465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203342717536159710411049643 305014076304239565616574465)
  ·
    refine ⟨228760557228179674212430849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305014076304239565616574465 228760557228179674212430849)
    ·
      refine ⟨171570417921134755659323137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228760557228179674212430849 171570417921134755659323137)
      ·
        refine ⟨128677813440851066744492353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171570417921134755659323137 128677813440851066744492353)
        ·
          refine ⟨96508360080638300058369265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128677813440851066744492353 96508360080638300058369265)
          ·
            refine ⟨72381270060478725043776949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96508360080638300058369265 72381270060478725043776949)
            ·
              refine ⟨6785744068169880472854089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72381270060478725043776949 6785744068169880472854089)
              ·
                refine ⟨5089308051127410354640567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6785744068169880472854089 5089308051127410354640567)
                ·
                  refine ⟨7633962076691115531960851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089308051127410354640567 7633962076691115531960851)
                  ·
                    refine ⟨11450943115036673297941277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7633962076691115531960851 11450943115036673297941277)
                    ·
                      refine ⟨4294103668138752486727979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11450943115036673297941277 4294103668138752486727979)
                      ·
                        rfl

theorem cell23_8362737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_8362737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362737 prefixEnd_8362737 := by exact prefixLift 8362737
  have htrace : WordTrace (prefixWord ++ tailWord_8362737) baseStart_8362737 baseEnd_8362737 := by
    simpa [prefixWord, tailWord_8362737, baseEnd_8362737] using wordTrace_append hprefix tailTrace_8362737
  have hstable : (prefixWord ++ tailWord_8362737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362737).length < 2 ^ (prefixWord ++ tailWord_8362737).sum := by decide
  have hdescent : baseEnd_8362737 < baseStart_8362737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362746 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_8362746 : Nat := 118140960795 + 8362746 * 2 ^ 59
def prefixEnd_8362746 : Nat := 4983230072969 + 3 ^ 40 * 8362746 * 2
def baseEnd_8362746 : Nat := 4294108289464642951515437

theorem tailTrace_8362746 : CollatzResearch.WordTrace tailWord_8362746 prefixEnd_8362746 4294108289464642951515437 := by
  unfold tailWord_8362746
  simp only [CollatzResearch.WordTrace]
  refine ⟨76253601140301740038413023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203342936374137973435768061 76253601140301740038413023)
  ·
    refine ⟨114380401710452610057619535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76253601140301740038413023 114380401710452610057619535)
    ·
      refine ⟨171570602565678915086429303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114380401710452610057619535 171570602565678915086429303)
      ·
        refine ⟨257355903848518372629643955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171570602565678915086429303 257355903848518372629643955)
        ·
          refine ⟨386033855772777558944465933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257355903848518372629643955 386033855772777558944465933)
          ·
            refine ⟨144762695914791584604174725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386033855772777558944465933 144762695914791584604174725)
            ·
              refine ⟨27143005484023422113282761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144762695914791584604174725 27143005484023422113282761)
              ·
                refine ⟨20357254113017566584962071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27143005484023422113282761 20357254113017566584962071)
                ·
                  refine ⟨30535881169526349877443107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20357254113017566584962071 30535881169526349877443107)
                  ·
                    refine ⟨45803821754289524816164661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30535881169526349877443107 45803821754289524816164661)
                    ·
                      refine ⟨4294108289464642951515437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45803821754289524816164661 4294108289464642951515437)
                      ·
                        rfl

theorem cell23_8362746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_8362746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362746 prefixEnd_8362746 := by exact prefixLift 8362746
  have htrace : WordTrace (prefixWord ++ tailWord_8362746) baseStart_8362746 baseEnd_8362746 := by
    simpa [prefixWord, tailWord_8362746, baseEnd_8362746] using wordTrace_append hprefix tailTrace_8362746
  have hstable : (prefixWord ++ tailWord_8362746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362746).length < 2 ^ (prefixWord ++ tailWord_8362746).sum := by decide
  have hdescent : baseEnd_8362746 < baseStart_8362746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362756 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_8362756 : Nat := 118140960795 + 8362756 * 2 ^ 59
def prefixEnd_8362756 : Nat := 4983230072969 + 3 ^ 40 * 8362756 * 2
def baseEnd_8362756 : Nat := 4294113424271187912390391

theorem tailTrace_8362756 : CollatzResearch.WordTrace tailWord_8362756 prefixEnd_8362756 4294113424271187912390391 := by
  unfold tailWord_8362756
  simp only [CollatzResearch.WordTrace]
  refine ⟨152507384645585365930758061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203343179527447154574344081 152507384645585365930758061)
  ·
    refine ⟨57190269242094512224034273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152507384645585365930758061 57190269242094512224034273)
    ·
      refine ⟨42892701931570884168025705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57190269242094512224034273 42892701931570884168025705)
      ·
        refine ⟨32169526448678163126019279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42892701931570884168025705 32169526448678163126019279)
        ·
          refine ⟨48254289673017244689028919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32169526448678163126019279 48254289673017244689028919)
          ·
            refine ⟨72381434509525867033543379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48254289673017244689028919 72381434509525867033543379)
            ·
              refine ⟨108572151764288800550315069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72381434509525867033543379 108572151764288800550315069)
              ·
                refine ⟨40714556911608300206368151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108572151764288800550315069 40714556911608300206368151)
                ·
                  refine ⟨61071835367412450309552227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40714556911608300206368151 61071835367412450309552227)
                  ·
                    refine ⟨91607753051118675464328341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61071835367412450309552227 91607753051118675464328341)
                    ·
                      refine ⟨4294113424271187912390391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91607753051118675464328341 4294113424271187912390391)
                      ·
                        rfl

theorem cell23_8362756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_8362756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362756 prefixEnd_8362756 := by exact prefixLift 8362756
  have htrace : WordTrace (prefixWord ++ tailWord_8362756) baseStart_8362756 baseEnd_8362756 := by
    simpa [prefixWord, tailWord_8362756, baseEnd_8362756] using wordTrace_append hprefix tailTrace_8362756
  have hstable : (prefixWord ++ tailWord_8362756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362756).length < 2 ^ (prefixWord ++ tailWord_8362756).sum := by decide
  have hdescent : baseEnd_8362756 < baseStart_8362756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362760 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_8362760 : Nat := 118140960795 + 8362760 * 2 ^ 59
def prefixEnd_8362760 : Nat := 4983230072969 + 3 ^ 40 * 8362760 * 2
def baseEnd_8362760 : Nat := 4294115478193805896740373

theorem tailTrace_8362760 : CollatzResearch.WordTrace tailWord_8362760 prefixEnd_8362760 4294115478193805896740373 := by
  unfold tailWord_8362760
  simp only [CollatzResearch.WordTrace]
  refine ⟨152507457591578120272330867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203343276788770827029774489 152507457591578120272330867)
  ·
    refine ⟨228761186387367180408496301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152507457591578120272330867 228761186387367180408496301)
    ·
      refine ⟨85785444895262692653186113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228761186387367180408496301 85785444895262692653186113)
      ·
        refine ⟨64339083671447019489889585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85785444895262692653186113 64339083671447019489889585)
        ·
          refine ⟨48254312753585264617417189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64339083671447019489889585 48254312753585264617417189)
          ·
            refine ⟨9047683641297237115765723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48254312753585264617417189 9047683641297237115765723)
            ·
              refine ⟨13571525461945855673648585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047683641297237115765723 13571525461945855673648585)
              ·
                refine ⟨10178644096459391755236439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13571525461945855673648585 10178644096459391755236439)
                ·
                  refine ⟨15267966144689087632854659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10178644096459391755236439 15267966144689087632854659)
                  ·
                    refine ⟨22901949217033631449281989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15267966144689087632854659 22901949217033631449281989)
                    ·
                      refine ⟨4294115478193805896740373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22901949217033631449281989 4294115478193805896740373)
                      ·
                        rfl

theorem cell23_8362760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_8362760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362760 prefixEnd_8362760 := by exact prefixLift 8362760
  have htrace : WordTrace (prefixWord ++ tailWord_8362760) baseStart_8362760 baseEnd_8362760 := by
    simpa [prefixWord, tailWord_8362760, baseEnd_8362760] using wordTrace_append hprefix tailTrace_8362760
  have hstable : (prefixWord ++ tailWord_8362760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362760).length < 2 ^ (prefixWord ++ tailWord_8362760).sum := by decide
  have hdescent : baseEnd_8362760 < baseStart_8362760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362770 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_8362770 : Nat := 118140960795 + 8362770 * 2 ^ 59
def prefixEnd_8362770 : Nat := 4983230072969 + 3 ^ 40 * 8362770 * 2
def baseEnd_8362770 : Nat := 1431373537666783619205109

theorem tailTrace_8362770 : CollatzResearch.WordTrace tailWord_8362770 prefixEnd_8362770 1431373537666783619205109 := by
  unfold tailWord_8362770
  simp only [CollatzResearch.WordTrace]
  refine ⟨76253819978280003063131441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203343519942080008168350509 76253819978280003063131441)
  ·
    refine ⟨57190364983710002297348581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76253819978280003063131441 57190364983710002297348581)
    ·
      refine ⟨10723193434445625430752859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57190364983710002297348581 10723193434445625430752859)
      ·
        refine ⟨16084790151668438146129289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10723193434445625430752859 16084790151668438146129289)
        ·
          refine ⟨12063592613751328609596967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16084790151668438146129289 12063592613751328609596967)
          ·
            refine ⟨18095388920626992914395451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063592613751328609596967 18095388920626992914395451)
            ·
              refine ⟨27143083380940489371593177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18095388920626992914395451 27143083380940489371593177)
              ·
                refine ⟨20357312535705367028694883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27143083380940489371593177 20357312535705367028694883)
                ·
                  refine ⟨30535968803558050543042325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20357312535705367028694883 30535968803558050543042325)
                  ·
                    refine ⟨1431373537666783619205109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30535968803558050543042325 1431373537666783619205109)
                    ·
                      rfl

theorem cell23_8362770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_8362770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362770 prefixEnd_8362770 := by exact prefixLift 8362770
  have htrace : WordTrace (prefixWord ++ tailWord_8362770) baseStart_8362770 baseEnd_8362770 := by
    simpa [prefixWord, tailWord_8362770, baseEnd_8362770] using wordTrace_append hprefix tailTrace_8362770
  have hstable : (prefixWord ++ tailWord_8362770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362770).length < 2 ^ (prefixWord ++ tailWord_8362770).sum := by decide
  have hdescent : baseEnd_8362770 < baseStart_8362770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362779 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 3, 9]
def baseStart_8362779 : Nat := 118140960795 + 8362779 * 2 ^ 59
def prefixEnd_8362779 : Nat := 4983230072969 + 3 ^ 40 * 8362779 * 2
def baseEnd_8362779 : Nat := 1431375078108747107467595

theorem tailTrace_8362779 : CollatzResearch.WordTrace tailWord_8362779 prefixEnd_8362779 1431375078108747107467595 := by
  unfold tailWord_8362779
  simp only [CollatzResearch.WordTrace]
  refine ⟨305015608170087406789603391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203343738780058271193068927 305015608170087406789603391)
  ·
    refine ⟨457523412255131110184405087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305015608170087406789603391 457523412255131110184405087)
    ·
      refine ⟨686285118382696665276607631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457523412255131110184405087 686285118382696665276607631)
      ·
        refine ⟨1029427677574044997914911447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686285118382696665276607631 1029427677574044997914911447)
        ·
          refine ⟨1544141516361067496872367171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029427677574044997914911447 1544141516361067496872367171)
          ·
            refine ⟨2316212274541601245308550757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544141516361067496872367171 2316212274541601245308550757)
            ·
              refine ⟨434289801476550233495353267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2316212274541601245308550757 434289801476550233495353267)
              ·
                refine ⟨651434702214825350243029901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434289801476550233495353267 651434702214825350243029901)
                ·
                  refine ⟨244288013330559506341136213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651434702214825350243029901 244288013330559506341136213)
                  ·
                    refine ⟨1431375078108747107467595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 244288013330559506341136213 1431375078108747107467595)
                    ·
                      rfl

theorem cell23_8362779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 9].length) (baseStart_8362779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362779 prefixEnd_8362779 := by exact prefixLift 8362779
  have htrace : WordTrace (prefixWord ++ tailWord_8362779) baseStart_8362779 baseEnd_8362779 := by
    simpa [prefixWord, tailWord_8362779, baseEnd_8362779] using wordTrace_append hprefix tailTrace_8362779
  have hstable : (prefixWord ++ tailWord_8362779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362779).length < 2 ^ (prefixWord ++ tailWord_8362779).sum := by decide
  have hdescent : baseEnd_8362779 < baseStart_8362779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362810 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_8362810 : Nat := 118140960795 + 8362810 * 2 ^ 59
def prefixEnd_8362810 : Nat := 4983230072969 + 3 ^ 40 * 8362810 * 2
def baseEnd_8362810 : Nat := 4294141152226530701115143

theorem tailTrace_8362810 : CollatzResearch.WordTrace tailWord_8362810 prefixEnd_8362810 4294141152226530701115143 := by
  unfold tailWord_8362810
  simp only [CollatzResearch.WordTrace]
  refine ⟨76254184708243774770995471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203344492555316732722654589 76254184708243774770995471)
  ·
    refine ⟨114381277062365662156493207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76254184708243774770995471 114381277062365662156493207)
    ·
      refine ⟨171571915593548493234739811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114381277062365662156493207 171571915593548493234739811)
      ·
        refine ⟨257357873390322739852109717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171571915593548493234739811 257357873390322739852109717)
        ·
          refine ⟨12063650315171378430567643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 257357873390322739852109717 12063650315171378430567643)
          ·
            refine ⟨18095475472757067645851465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063650315171378430567643 18095475472757067645851465)
            ·
              refine ⟨13571606604567800734388599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18095475472757067645851465 13571606604567800734388599)
              ·
                refine ⟨20357409906851701101582899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13571606604567800734388599 20357409906851701101582899)
                ·
                  refine ⟨30536114860277551652374349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20357409906851701101582899 30536114860277551652374349)
                  ·
                    refine ⟨11451043072604081869640381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30536114860277551652374349 11451043072604081869640381)
                    ·
                      refine ⟨4294141152226530701115143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11451043072604081869640381 4294141152226530701115143)
                      ·
                        rfl

theorem cell23_8362810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_8362810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362810 prefixEnd_8362810 := by exact prefixLift 8362810
  have htrace : WordTrace (prefixWord ++ tailWord_8362810) baseStart_8362810 baseEnd_8362810 := by
    simpa [prefixWord, tailWord_8362810, baseEnd_8362810] using wordTrace_append hprefix tailTrace_8362810
  have hstable : (prefixWord ++ tailWord_8362810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362810).length < 2 ^ (prefixWord ++ tailWord_8362810).sum := by decide
  have hdescent : baseEnd_8362810 < baseStart_8362810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362844 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_8362844 : Nat := 118140960795 + 8362844 * 2 ^ 59
def prefixEnd_8362844 : Nat := 4983230072969 + 3 ^ 40 * 8362844 * 2
def baseEnd_8362844 : Nat := 4294158610568783568089987

theorem tailTrace_8362844 : CollatzResearch.WordTrace tailWord_8362844 prefixEnd_8362844 4294158610568783568089987 := by
  unfold tailWord_8362844
  simp only [CollatzResearch.WordTrace]
  refine ⟨152508989457425961445359793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203345319276567948593813057 152508989457425961445359793)
  ·
    refine ⟨114381742093069471084019845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152508989457425961445359793 114381742093069471084019845)
    ·
      refine ⟨21446576642450525828253721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114381742093069471084019845 21446576642450525828253721)
      ·
        refine ⟨16084932481837894371190291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21446576642450525828253721 16084932481837894371190291)
        ·
          refine ⟨24127398722756841556785437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16084932481837894371190291 24127398722756841556785437)
          ·
            refine ⟨9047774521033815583794539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24127398722756841556785437 9047774521033815583794539)
            ·
              refine ⟨13571661781550723375691809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047774521033815583794539 13571661781550723375691809)
              ·
                refine ⟨10178746336163042531768857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13571661781550723375691809 10178746336163042531768857)
                ·
                  refine ⟨7634059752122281898826643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10178746336163042531768857 7634059752122281898826643)
                  ·
                    refine ⟨11451089628183422848239965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7634059752122281898826643 11451089628183422848239965)
                    ·
                      refine ⟨4294158610568783568089987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11451089628183422848239965 4294158610568783568089987)
                      ·
                        rfl

theorem cell23_8362844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_8362844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362844 prefixEnd_8362844 := by exact prefixLift 8362844
  have htrace : WordTrace (prefixWord ++ tailWord_8362844) baseStart_8362844 baseEnd_8362844 := by
    simpa [prefixWord, tailWord_8362844, baseEnd_8362844] using wordTrace_append hprefix tailTrace_8362844
  have hstable : (prefixWord ++ tailWord_8362844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362844).length < 2 ^ (prefixWord ++ tailWord_8362844).sum := by decide
  have hdescent : baseEnd_8362844 < baseStart_8362844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362903 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 2, 5]
def baseStart_8362903 : Nat := 118140960795 + 8362903 * 2 ^ 59
def prefixEnd_8362903 : Nat := 4983230072969 + 3 ^ 40 * 8362903 * 2
def baseEnd_8362903 : Nat := 1431396301975799612417405

theorem tailTrace_8362903 : CollatzResearch.WordTrace tailWord_8362903 prefixEnd_8362903 1431396301975799612417405 := by
  unfold tailWord_8362903
  simp only [CollatzResearch.WordTrace]
  refine ⟨305020130821638175967117363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203346753881092117311411575 305020130821638175967117363)
  ·
    refine ⟨457530196232457263950676045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305020130821638175967117363 457530196232457263950676045)
    ·
      refine ⟨171573823587171473981503517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457530196232457263950676045 171573823587171473981503517)
      ·
        refine ⟨64340183845189302743063819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171573823587171473981503517 64340183845189302743063819)
        ·
          refine ⟨96510275767783954114595729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64340183845189302743063819 96510275767783954114595729)
          ·
            refine ⟨72382706825837965585946797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96510275767783954114595729 72382706825837965585946797)
            ·
              refine ⟨27143515059689237094730049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72382706825837965585946797 27143515059689237094730049)
              ·
                refine ⟨20357636294766927821047537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27143515059689237094730049 20357636294766927821047537)
                ·
                  refine ⟨15268227221075195865785653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20357636294766927821047537 15268227221075195865785653)
                  ·
                    refine ⟨1431396301975799612417405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15268227221075195865785653 1431396301975799612417405)
                    ·
                      rfl

theorem cell23_8362903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_8362903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362903 prefixEnd_8362903 := by exact prefixLift 8362903
  have htrace : WordTrace (prefixWord ++ tailWord_8362903) baseStart_8362903 baseEnd_8362903 := by
    simpa [prefixWord, tailWord_8362903, baseEnd_8362903] using wordTrace_append hprefix tailTrace_8362903
  have hstable : (prefixWord ++ tailWord_8362903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362903).length < 2 ^ (prefixWord ++ tailWord_8362903).sum := by decide
  have hdescent : baseEnd_8362903 < baseStart_8362903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8362913 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_8362913 : Nat := 118140960795 + 8362913 * 2 ^ 59
def prefixEnd_8362913 : Nat := 4983230072969 + 3 ^ 40 * 8362913 * 2
def baseEnd_8362913 : Nat := 4294194040733943798127169

theorem tailTrace_8362913 : CollatzResearch.WordTrace tailWord_8362913 prefixEnd_8362913 4294194040733943798127169 := by
  unfold tailWord_8362913
  simp only [CollatzResearch.WordTrace]
  refine ⟨305020495551601947674981393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203346997034401298449987595 305020495551601947674981393)
  ·
    refine ⟨228765371663701460756236045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305020495551601947674981393 228765371663701460756236045)
    ·
      refine ⟨85787014373888047783588517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228765371663701460756236045 85787014373888047783588517)
      ·
        refine ⟨16085065195104008959422847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85787014373888047783588517 16085065195104008959422847)
        ·
          refine ⟨24127597792656013439134271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16085065195104008959422847 24127597792656013439134271)
          ·
            refine ⟨36191396688984020158701407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24127597792656013439134271 36191396688984020158701407)
            ·
              refine ⟨54287095033476030238052111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36191396688984020158701407 54287095033476030238052111)
              ·
                refine ⟨81430642550214045357078167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54287095033476030238052111 81430642550214045357078167)
                ·
                  refine ⟨122145963825321068035617251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81430642550214045357078167 122145963825321068035617251)
                  ·
                    refine ⟨183218945737981602053425877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122145963825321068035617251 183218945737981602053425877)
                    ·
                      refine ⟨4294194040733943798127169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183218945737981602053425877 4294194040733943798127169)
                      ·
                        rfl

theorem cell23_8362913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_8362913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8362913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8362913 prefixEnd_8362913 := by exact prefixLift 8362913
  have htrace : WordTrace (prefixWord ++ tailWord_8362913) baseStart_8362913 baseEnd_8362913 := by
    simpa [prefixWord, tailWord_8362913, baseEnd_8362913] using wordTrace_append hprefix tailTrace_8362913
  have hstable : (prefixWord ++ tailWord_8362913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8362913).length < 2 ^ (prefixWord ++ tailWord_8362913).sum := by decide
  have hdescent : baseEnd_8362913 < baseStart_8362913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8362913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363033 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_8363033 : Nat := 118140960795 + 8363033 * 2 ^ 59
def prefixEnd_8363033 : Nat := 4983230072969 + 3 ^ 40 * 8363033 * 2
def baseEnd_8363033 : Nat := 4294255658412483328626617

theorem tailTrace_8363033 : CollatzResearch.WordTrace tailWord_8363033 prefixEnd_8363033 4294255658412483328626617 := by
  unfold tailWord_8363033
  simp only [CollatzResearch.WordTrace]
  refine ⟨305024872311167208169349753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203349914874111472112899835 305024872311167208169349753)
  ·
    refine ⟨228768654233375406127012315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305024872311167208169349753 228768654233375406127012315)
    ·
      refine ⟨343152981350063109190518473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228768654233375406127012315 343152981350063109190518473)
      ·
        refine ⟨257364736012547331892888855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343152981350063109190518473 257364736012547331892888855)
        ·
          refine ⟨386047104018820997839333283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257364736012547331892888855 386047104018820997839333283)
          ·
            refine ⟨579070656028231496758999925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386047104018820997839333283 579070656028231496758999925)
            ·
              refine ⟨54287874002646702821156243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 579070656028231496758999925 54287874002646702821156243)
              ·
                refine ⟨81431811003970054231734365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54287874002646702821156243 81431811003970054231734365)
                ·
                  refine ⟨30536929126488770336900387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81431811003970054231734365 30536929126488770336900387)
                  ·
                    refine ⟨45805393689733155505350581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30536929126488770336900387 45805393689733155505350581)
                    ·
                      refine ⟨4294255658412483328626617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45805393689733155505350581 4294255658412483328626617)
                      ·
                        rfl

theorem cell23_8363033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_8363033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363033 prefixEnd_8363033 := by exact prefixLift 8363033
  have htrace : WordTrace (prefixWord ++ tailWord_8363033) baseStart_8363033 baseEnd_8363033 := by
    simpa [prefixWord, tailWord_8363033, baseEnd_8363033] using wordTrace_append hprefix tailTrace_8363033
  have hstable : (prefixWord ++ tailWord_8363033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363033).length < 2 ^ (prefixWord ++ tailWord_8363033).sum := by decide
  have hdescent : baseEnd_8363033 < baseStart_8363033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363070 : List Nat := [4, 2, 1, 3, 1, 1, 11]
def baseStart_8363070 : Nat := 118140960795 + 8363070 * 2 ^ 59
def prefixEnd_8363070 : Nat := 4983230072969 + 3 ^ 40 * 8363070 * 2
def baseEnd_8363070 : Nat := 53015736508601230664987

theorem tailTrace_8363070 : CollatzResearch.WordTrace tailWord_8363070 prefixEnd_8363070 53015736508601230664987 := by
  unfold tailWord_8363070
  simp only [CollatzResearch.WordTrace]
  refine ⟨38128277726504145436055833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203350814541355442325631109 38128277726504145436055833)
  ·
    refine ⟨28596208294878109077041875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38128277726504145436055833 28596208294878109077041875)
    ·
      refine ⟨42894312442317163615562813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28596208294878109077041875 42894312442317163615562813)
      ·
        refine ⟨16085367165868936355836055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42894312442317163615562813 16085367165868936355836055)
        ·
          refine ⟨24128050748803404533754083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16085367165868936355836055 24128050748803404533754083)
          ·
            refine ⟨36192076123205106800631125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24128050748803404533754083 36192076123205106800631125)
            ·
              refine ⟨53015736508601230664987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 36192076123205106800631125 53015736508601230664987)
              ·
                rfl

theorem cell23_8363070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 11].length) (baseStart_8363070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363070 prefixEnd_8363070 := by exact prefixLift 8363070
  have htrace : WordTrace (prefixWord ++ tailWord_8363070) baseStart_8363070 baseEnd_8363070 := by
    simpa [prefixWord, tailWord_8363070, baseEnd_8363070] using wordTrace_append hprefix tailTrace_8363070
  have hstable : (prefixWord ++ tailWord_8363070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363070).length < 2 ^ (prefixWord ++ tailWord_8363070).sum := by decide
  have hdescent : baseEnd_8363070 < baseStart_8363070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363154 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_8363154 : Nat := 118140960795 + 8363154 * 2 ^ 59
def prefixEnd_8363154 : Nat := 4983230072969 + 3 ^ 40 * 8363154 * 2
def baseEnd_8363154 : Nat := 4294317789571677355213561

theorem tailTrace_8363154 : CollatzResearch.WordTrace tailWord_8363154 prefixEnd_8363154 4294317789571677355213561 := by
  unfold tailWord_8363154
  simp only [CollatzResearch.WordTrace]
  refine ⟨76257321385932211458626129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203352857029152563889669677 76257321385932211458626129)
  ·
    refine ⟨57192991039449158593969597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76257321385932211458626129 57192991039449158593969597)
    ·
      refine ⟨21447371639793434472738599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57192991039449158593969597 21447371639793434472738599)
      ·
        refine ⟨32171057459690151709107899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21447371639793434472738599 32171057459690151709107899)
        ·
          refine ⟨48256586189535227563661849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32171057459690151709107899 48256586189535227563661849)
          ·
            refine ⟨36192439642151420672746387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48256586189535227563661849 36192439642151420672746387)
            ·
              refine ⟨54288659463227131009119581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36192439642151420672746387 54288659463227131009119581)
              ·
                refine ⟨20358247298710174128419843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54288659463227131009119581 20358247298710174128419843)
                ·
                  refine ⟨30537370948065261192629765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20358247298710174128419843 30537370948065261192629765)
                  ·
                    refine ⟨5725757052762236473618081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30537370948065261192629765 5725757052762236473618081)
                    ·
                      refine ⟨4294317789571677355213561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725757052762236473618081 4294317789571677355213561)
                      ·
                        rfl

theorem cell23_8363154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_8363154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363154 prefixEnd_8363154 := by exact prefixLift 8363154
  have htrace : WordTrace (prefixWord ++ tailWord_8363154) baseStart_8363154 baseEnd_8363154 := by
    simpa [prefixWord, tailWord_8363154, baseEnd_8363154] using wordTrace_append hprefix tailTrace_8363154
  have hstable : (prefixWord ++ tailWord_8363154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363154).length < 2 ^ (prefixWord ++ tailWord_8363154).sum := by decide
  have hdescent : baseEnd_8363154 < baseStart_8363154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363160 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 9]
def baseStart_8363160 : Nat := 118140960795 + 8363160 * 2 ^ 59
def prefixEnd_8363160 : Nat := 4983230072969 + 3 ^ 40 * 8363160 * 2
def baseEnd_8363160 : Nat := 477146763383956036859837

theorem tailTrace_8363160 : CollatzResearch.WordTrace tailWord_8363160 prefixEnd_8363160 477146763383956036859837 := by
  unfold tailWord_8363160
  simp only [CollatzResearch.WordTrace]
  refine ⟨152514752190853554429611467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203353002921138072572815289 152514752190853554429611467)
  ·
    refine ⟨228772128286280331644417201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152514752190853554429611467 228772128286280331644417201)
    ·
      refine ⟨171579096214710248733312901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228772128286280331644417201 171579096214710248733312901)
      ·
        refine ⟨32171080540258171637496169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171579096214710248733312901 32171080540258171637496169)
        ·
          refine ⟨24128310405193628728122127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32171080540258171637496169 24128310405193628728122127)
          ·
            refine ⟨36192465607790443092183191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24128310405193628728122127 36192465607790443092183191)
            ·
              refine ⟨54288698411685664638274787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36192465607790443092183191 54288698411685664638274787)
              ·
                refine ⟨81433047617528496957412181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54288698411685664638274787 81433047617528496957412181)
                ·
                  refine ⟨477146763383956036859837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81433047617528496957412181 477146763383956036859837)
                  ·
                    rfl

theorem cell23_8363160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 9].length) (baseStart_8363160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363160 prefixEnd_8363160 := by exact prefixLift 8363160
  have htrace : WordTrace (prefixWord ++ tailWord_8363160) baseStart_8363160 baseEnd_8363160 := by
    simpa [prefixWord, tailWord_8363160, baseEnd_8363160] using wordTrace_append hprefix tailTrace_8363160
  have hstable : (prefixWord ++ tailWord_8363160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363160).length < 2 ^ (prefixWord ++ tailWord_8363160).sum := by decide
  have hdescent : baseEnd_8363160 < baseStart_8363160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363197 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_8363197 : Nat := 118140960795 + 8363197 * 2 ^ 59
def prefixEnd_8363197 : Nat := 4983230072969 + 3 ^ 40 * 8363197 * 2
def baseEnd_8363197 : Nat := 4294339869239820686975863

theorem tailTrace_8363197 : CollatzResearch.WordTrace tailWord_8363197 prefixEnd_8363197 4294339869239820686975863 := by
  unfold tailWord_8363197
  simp only [CollatzResearch.WordTrace]
  refine ⟨305030853882573064178319845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203353902588382042785546563 305030853882573064178319845)
  ·
    refine ⟨57193285102982449533434971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305030853882573064178319845 57193285102982449533434971)
    ·
      refine ⟨85789927654473674300152457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57193285102982449533434971 85789927654473674300152457)
      ·
        refine ⟨64342445740855255725114343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85789927654473674300152457 64342445740855255725114343)
        ·
          refine ⟨96513668611282883587671515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64342445740855255725114343 96513668611282883587671515)
          ·
            refine ⟨144770502916924325381507273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96513668611282883587671515 144770502916924325381507273)
            ·
              refine ⟨108577877187693244036130455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144770502916924325381507273 108577877187693244036130455)
              ·
                refine ⟨162866815781539866054195683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108577877187693244036130455 162866815781539866054195683)
                ·
                  refine ⟨244300223672309799081293525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162866815781539866054195683 244300223672309799081293525)
                  ·
                    refine ⟨5725786492319760915967817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 244300223672309799081293525 5725786492319760915967817)
                    ·
                      refine ⟨4294339869239820686975863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725786492319760915967817 4294339869239820686975863)
                      ·
                        rfl

theorem cell23_8363197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_8363197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363197 prefixEnd_8363197 := by exact prefixLift 8363197
  have htrace : WordTrace (prefixWord ++ tailWord_8363197) baseStart_8363197 baseEnd_8363197 := by
    simpa [prefixWord, tailWord_8363197, baseEnd_8363197] using wordTrace_append hprefix tailTrace_8363197
  have hstable : (prefixWord ++ tailWord_8363197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363197).length < 2 ^ (prefixWord ++ tailWord_8363197).sum := by decide
  have hdescent : baseEnd_8363197 < baseStart_8363197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363267 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 6]
def baseStart_8363267 : Nat := 118140960795 + 8363267 * 2 ^ 59
def prefixEnd_8363267 : Nat := 4983230072969 + 3 ^ 40 * 8363267 * 2
def baseEnd_8363267 : Nat := 477152868098403934788949

theorem tailTrace_8363267 : CollatzResearch.WordTrace tailWord_8363267 prefixEnd_8363267 477152868098403934788949 := by
  unfold tailWord_8363267
  simp only [CollatzResearch.WordTrace]
  refine ⟨305033406992319466133368055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203355604661546310755578703 305033406992319466133368055)
  ·
    refine ⟨457550110488479199200052083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305033406992319466133368055 457550110488479199200052083)
    ·
      refine ⟨686325165732718798800078125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457550110488479199200052083 686325165732718798800078125)
      ·
        refine ⟨257371937149769549550029297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686325165732718798800078125 257371937149769549550029297)
        ·
          refine ⟨193028952862327162162521973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257371937149769549550029297 193028952862327162162521973)
          ·
            refine ⟨18096464330843171452736435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193028952862327162162521973 18096464330843171452736435)
            ·
              refine ⟨27144696496264757179104653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18096464330843171452736435 27144696496264757179104653)
              ·
                refine ⟨10179261186099283942164245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27144696496264757179104653 10179261186099283942164245)
                ·
                  refine ⟨477152868098403934788949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10179261186099283942164245 477152868098403934788949)
                  ·
                    rfl

theorem cell23_8363267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 6].length) (baseStart_8363267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363267 prefixEnd_8363267 := by exact prefixLift 8363267
  have htrace : WordTrace (prefixWord ++ tailWord_8363267) baseStart_8363267 baseEnd_8363267 := by
    simpa [prefixWord, tailWord_8363267, baseEnd_8363267] using wordTrace_append hprefix tailTrace_8363267
  have hstable : (prefixWord ++ tailWord_8363267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363267).length < 2 ^ (prefixWord ++ tailWord_8363267).sum := by decide
  have hdescent : baseEnd_8363267 < baseStart_8363267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363327 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 1, 6]
def baseStart_8363327 : Nat := 118140960795 + 8363327 * 2 ^ 59
def prefixEnd_8363327 : Nat := 4983230072969 + 3 ^ 40 * 8363327 * 2
def baseEnd_8363327 : Nat := 1431468873908301726116755

theorem tailTrace_8363327 : CollatzResearch.WordTrace tailWord_8363327 prefixEnd_8363327 1431468873908301726116755 := by
  unfold tailWord_8363327
  simp only [CollatzResearch.WordTrace]
  refine ⟨305035595372102096380552235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203357063581401397587034823 305035595372102096380552235)
  ·
    refine ⟨457553393058153144570828353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305035595372102096380552235 457553393058153144570828353)
    ·
      refine ⟨343165044793614858428121265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457553393058153144570828353 343165044793614858428121265)
      ·
        refine ⟨257373783595211143821090949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343165044793614858428121265 257373783595211143821090949)
        ·
          refine ⟨48257584424102089466454553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257373783595211143821090949 48257584424102089466454553)
          ·
            refine ⟨36193188318076567099840915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48257584424102089466454553 36193188318076567099840915)
            ·
              refine ⟨54289782477114850649761373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36193188318076567099840915 54289782477114850649761373)
              ·
                refine ⟨20358668428918068993660515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54289782477114850649761373 20358668428918068993660515)
                ·
                  refine ⟨30538002643377103490490773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20358668428918068993660515 30538002643377103490490773)
                  ·
                    refine ⟨1431468873908301726116755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30538002643377103490490773 1431468873908301726116755)
                    ·
                      rfl

theorem cell23_8363327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_8363327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363327 prefixEnd_8363327 := by exact prefixLift 8363327
  have htrace : WordTrace (prefixWord ++ tailWord_8363327) baseStart_8363327 baseEnd_8363327 := by
    simpa [prefixWord, tailWord_8363327, baseEnd_8363327] using wordTrace_append hprefix tailTrace_8363327
  have hstable : (prefixWord ++ tailWord_8363327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363327).length < 2 ^ (prefixWord ++ tailWord_8363327).sum := by decide
  have hdescent : baseEnd_8363327 < baseStart_8363327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363347 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 4]
def baseStart_8363347 : Nat := 118140960795 + 8363347 * 2 ^ 59
def prefixEnd_8363347 : Nat := 4983230072969 + 3 ^ 40 * 8363347 * 2
def baseEnd_8363347 : Nat := 4294416891337995100100173

theorem tailTrace_8363347 : CollatzResearch.WordTrace tailWord_8363347 prefixEnd_8363347 4294416891337995100100173 := by
  unfold tailWord_8363347
  simp only [CollatzResearch.WordTrace]
  refine ⟨305036324832029639796280295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203357549888019759864186863 305036324832029639796280295)
  ·
    refine ⟨457554487248044459694420443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305036324832029639796280295 457554487248044459694420443)
    ·
      refine ⟨686331730872066689541630665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457554487248044459694420443 686331730872066689541630665)
      ·
        refine ⟨514748798154050017156222999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686331730872066689541630665 514748798154050017156222999)
        ·
          refine ⟨772123197231075025734334499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514748798154050017156222999 772123197231075025734334499)
          ·
            refine ⟨1158184795846612538601501749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772123197231075025734334499 1158184795846612538601501749)
            ·
              refine ⟨108579824610619925493890789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1158184795846612538601501749 108579824610619925493890789)
              ·
                refine ⟨20358717114491236030104523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108579824610619925493890789 20358717114491236030104523)
                ·
                  refine ⟨30538075671736854045156785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20358717114491236030104523 30538075671736854045156785)
                  ·
                    refine ⟨22903556753802640533867589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30538075671736854045156785 22903556753802640533867589)
                    ·
                      refine ⟨4294416891337995100100173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22903556753802640533867589 4294416891337995100100173)
                      ·
                        rfl

theorem cell23_8363347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_8363347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363347 prefixEnd_8363347 := by exact prefixLift 8363347
  have htrace : WordTrace (prefixWord ++ tailWord_8363347) baseStart_8363347 baseEnd_8363347 := by
    simpa [prefixWord, tailWord_8363347, baseEnd_8363347] using wordTrace_append hprefix tailTrace_8363347
  have hstable : (prefixWord ++ tailWord_8363347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363347).length < 2 ^ (prefixWord ++ tailWord_8363347).sum := by decide
  have hdescent : baseEnd_8363347 < baseStart_8363347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363351 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 1, 1, 4]
def baseStart_8363351 : Nat := 118140960795 + 8363351 * 2 ^ 59
def prefixEnd_8363351 : Nat := 4983230072969 + 3 ^ 40 * 8363351 * 2
def baseEnd_8363351 : Nat := 4294418945260613084450155

theorem tailTrace_8363351 : CollatzResearch.WordTrace tailWord_8363351 prefixEnd_8363351 4294418945260613084450155 := by
  unfold tailWord_8363351
  simp only [CollatzResearch.WordTrace]
  refine ⟨305036470724015148479425907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203357647149343432319617271 305036470724015148479425907)
  ·
    refine ⟨457554706086022722719138861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305036470724015148479425907 457554706086022722719138861)
    ·
      refine ⟨171583014782258521019677073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457554706086022722719138861 171583014782258521019677073)
      ·
        refine ⟨128687261086693890764757805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171583014782258521019677073 128687261086693890764757805)
        ·
          refine ⟨48257722907510209036784177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128687261086693890764757805 48257722907510209036784177)
          ·
            refine ⟨36193292180632656777588133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48257722907510209036784177 36193292180632656777588133)
            ·
              refine ⟨6786242283868623145797775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36193292180632656777588133 6786242283868623145797775)
              ·
                refine ⟨10179363425802934718696663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786242283868623145797775 10179363425802934718696663)
                ·
                  refine ⟨15269045138704402078044995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10179363425802934718696663 15269045138704402078044995)
                  ·
                    refine ⟨22903567708056603117067493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15269045138704402078044995 22903567708056603117067493)
                    ·
                      refine ⟨4294418945260613084450155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22903567708056603117067493 4294418945260613084450155)
                      ·
                        rfl

theorem cell23_8363351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_8363351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363351 prefixEnd_8363351 := by exact prefixLift 8363351
  have htrace : WordTrace (prefixWord ++ tailWord_8363351) baseStart_8363351 baseEnd_8363351 := by
    simpa [prefixWord, tailWord_8363351, baseEnd_8363351] using wordTrace_append hprefix tailTrace_8363351
  have hstable : (prefixWord ++ tailWord_8363351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363351).length < 2 ^ (prefixWord ++ tailWord_8363351).sum := by decide
  have hdescent : baseEnd_8363351 < baseStart_8363351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363397 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_8363397 : Nat := 118140960795 + 8363397 * 2 ^ 59
def prefixEnd_8363397 : Nat := 4983230072969 + 3 ^ 40 * 8363397 * 2
def baseEnd_8363397 : Nat := 4294442565370719904474943

theorem tailTrace_8363397 : CollatzResearch.WordTrace tailWord_8363397 prefixEnd_8363397 4294442565370719904474943 := by
  unfold tailWord_8363397
  simp only [CollatzResearch.WordTrace]
  refine ⟨305038148481848498335600445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203358765654565665557066963 305038148481848498335600445)
  ·
    refine ⟨114389305680693186875850167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305038148481848498335600445 114389305680693186875850167)
    ·
      refine ⟨171583958521039780313775251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114389305680693186875850167 171583958521039780313775251)
      ·
        refine ⟨257375937781559670470662877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171583958521039780313775251 257375937781559670470662877)
        ·
          refine ⟨96515976668084876426498579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257375937781559670470662877 96515976668084876426498579)
          ·
            refine ⟨144773965002127314639747869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96515976668084876426498579 144773965002127314639747869)
            ·
              refine ⟨54290236875797742989905451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144773965002127314639747869 54290236875797742989905451)
              ·
                refine ⟨81435355313696614484858177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54290236875797742989905451 81435355313696614484858177)
                ·
                  refine ⟨61076516485272460863643633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81435355313696614484858177 61076516485272460863643633)
                  ·
                    refine ⟨45807387363954345647732725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61076516485272460863643633 45807387363954345647732725)
                    ·
                      refine ⟨4294442565370719904474943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45807387363954345647732725 4294442565370719904474943)
                      ·
                        rfl

theorem cell23_8363397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_8363397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363397 prefixEnd_8363397 := by exact prefixLift 8363397
  have htrace : WordTrace (prefixWord ++ tailWord_8363397) baseStart_8363397 baseEnd_8363397 := by
    simpa [prefixWord, tailWord_8363397, baseEnd_8363397] using wordTrace_append hprefix tailTrace_8363397
  have hstable : (prefixWord ++ tailWord_8363397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363397).length < 2 ^ (prefixWord ++ tailWord_8363397).sum := by decide
  have hdescent : baseEnd_8363397 < baseStart_8363397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363427 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 5]
def baseStart_8363427 : Nat := 118140960795 + 8363427 * 2 ^ 59
def prefixEnd_8363427 : Nat := 4983230072969 + 3 ^ 40 * 8363427 * 2
def baseEnd_8363427 : Nat := 4294457969790354787099805

theorem tailTrace_8363427 : CollatzResearch.WordTrace tailWord_8363427 prefixEnd_8363427 4294457969790354787099805 := by
  unfold tailWord_8363427
  simp only [CollatzResearch.WordTrace]
  refine ⟨305039242671739813459192535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203359495114493208972795023 305039242671739813459192535)
  ·
    refine ⟨457558864007609720188788803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305039242671739813459192535 457558864007609720188788803)
    ·
      refine ⟨686338296011414580283183205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457558864007609720188788803 686338296011414580283183205)
      ·
        refine ⟨128688430502140233803096851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 686338296011414580283183205 128688430502140233803096851)
        ·
          refine ⟨193032645753210350704645277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128688430502140233803096851 193032645753210350704645277)
          ·
            refine ⟨72387242157453881514241979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193032645753210350704645277 72387242157453881514241979)
            ·
              refine ⟨108580863236180822271362969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72387242157453881514241979 108580863236180822271362969)
              ·
                refine ⟨81435647427135616703522227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108580863236180822271362969 81435647427135616703522227)
                ·
                  refine ⟨122153471140703425055283341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81435647427135616703522227 122153471140703425055283341)
                  ·
                    refine ⟨45807551677763784395731253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122153471140703425055283341 45807551677763784395731253)
                    ·
                      refine ⟨4294457969790354787099805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45807551677763784395731253 4294457969790354787099805)
                      ·
                        rfl

theorem cell23_8363427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_8363427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363427 prefixEnd_8363427 := by exact prefixLift 8363427
  have htrace : WordTrace (prefixWord ++ tailWord_8363427) baseStart_8363427 baseEnd_8363427 := by
    simpa [prefixWord, tailWord_8363427, baseEnd_8363427] using wordTrace_append hprefix tailTrace_8363427
  have hstable : (prefixWord ++ tailWord_8363427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363427).length < 2 ^ (prefixWord ++ tailWord_8363427).sum := by decide
  have hdescent : baseEnd_8363427 < baseStart_8363427 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363441 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 1, 4, 2]
def baseStart_8363441 : Nat := 118140960795 + 8363441 * 2 ^ 59
def prefixEnd_8363441 : Nat := 4983230072969 + 3 ^ 40 * 8363441 * 2
def baseEnd_8363441 : Nat := 4294465158519517732324741

theorem tailTrace_8363441 : CollatzResearch.WordTrace tailWord_8363441 prefixEnd_8363441 4294465158519517732324741 := by
  unfold tailWord_8363441
  simp only [CollatzResearch.WordTrace]
  refine ⟨305039753293689093850202177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203359835529126062566801451 305039753293689093850202177)
  ·
    refine ⟨228779814970266820387651633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305039753293689093850202177 228779814970266820387651633)
    ·
      refine ⟨171584861227700115290738725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228779814970266820387651633 171584861227700115290738725)
      ·
        refine ⟨32172161480193771617013511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171584861227700115290738725 32172161480193771617013511)
        ·
          refine ⟨48258242220290657425520267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32172161480193771617013511 48258242220290657425520267)
          ·
            refine ⟨72387363330435986138280401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48258242220290657425520267 72387363330435986138280401)
            ·
              refine ⟨54290522497826989603710301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72387363330435986138280401 54290522497826989603710301)
              ·
                refine ⟨20358945936685121101391363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54290522497826989603710301 20358945936685121101391363)
                ·
                  refine ⟨30538418905027681652087045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20358945936685121101391363 30538418905027681652087045)
                  ·
                    refine ⟨5725953544692690309766321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30538418905027681652087045 5725953544692690309766321)
                    ·
                      refine ⟨4294465158519517732324741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725953544692690309766321 4294465158519517732324741)
                      ·
                        rfl

theorem cell23_8363441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_8363441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363441 prefixEnd_8363441 := by exact prefixLift 8363441
  have htrace : WordTrace (prefixWord ++ tailWord_8363441) baseStart_8363441 baseEnd_8363441 := by
    simpa [prefixWord, tailWord_8363441, baseEnd_8363441] using wordTrace_append hprefix tailTrace_8363441
  have hstable : (prefixWord ++ tailWord_8363441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363441).length < 2 ^ (prefixWord ++ tailWord_8363441).sum := by decide
  have hdescent : baseEnd_8363441 < baseStart_8363441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363445 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_8363445 : Nat := 118140960795 + 8363445 * 2 ^ 59
def prefixEnd_8363445 : Nat := 4983230072969 + 3 ^ 40 * 8363445 * 2
def baseEnd_8363445 : Nat := 4294467212442135716674723

theorem tailTrace_8363445 : CollatzResearch.WordTrace tailWord_8363445 prefixEnd_8363445 4294467212442135716674723 := by
  unfold tailWord_8363445
  simp only [CollatzResearch.WordTrace]
  refine ⟨305039899185674602533347789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203359932790449735022231859 305039899185674602533347789)
  ·
    refine ⟨114389962194627975950005421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305039899185674602533347789 114389962194627975950005421)
    ·
      refine ⟨42896235822985490981252033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114389962194627975950005421 42896235822985490981252033)
      ·
        refine ⟨32172176867239118235939025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42896235822985490981252033 32172176867239118235939025)
        ·
          refine ⟨24129132650429338676954269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32172176867239118235939025 24129132650429338676954269)
          ·
            refine ⟨9048424743911002003857851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24129132650429338676954269 9048424743911002003857851)
            ·
              refine ⟨13572637115866503005786777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048424743911002003857851 13572637115866503005786777)
              ·
                refine ⟨10179477836899877254340083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13572637115866503005786777 10179477836899877254340083)
                ·
                  refine ⟨15269216755349815881510125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10179477836899877254340083 15269216755349815881510125)
                  ·
                    refine ⟨5725956283256180955566297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15269216755349815881510125 5725956283256180955566297)
                    ·
                      refine ⟨4294467212442135716674723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5725956283256180955566297 4294467212442135716674723)
                      ·
                        rfl

theorem cell23_8363445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_8363445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363445 prefixEnd_8363445 := by exact prefixLift 8363445
  have htrace : WordTrace (prefixWord ++ tailWord_8363445) baseStart_8363445 baseEnd_8363445 := by
    simpa [prefixWord, tailWord_8363445, baseEnd_8363445] using wordTrace_append hprefix tailTrace_8363445
  have hstable : (prefixWord ++ tailWord_8363445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363445).length < 2 ^ (prefixWord ++ tailWord_8363445).sum := by decide
  have hdescent : baseEnd_8363445 < baseStart_8363445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363447 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 9]
def baseStart_8363447 : Nat := 118140960795 + 8363447 * 2 ^ 59
def prefixEnd_8363447 : Nat := 4983230072969 + 3 ^ 40 * 8363447 * 2
def baseEnd_8363447 : Nat := 477163137711493856538857

theorem tailTrace_8363447 : CollatzResearch.WordTrace tailWord_8363447 prefixEnd_8363447 477163137711493856538857 := by
  unfold tailWord_8363447
  simp only [CollatzResearch.WordTrace]
  refine ⟨305039972131667356874920595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203359981421111571249947063 305039972131667356874920595)
  ·
    refine ⟨457559958197501035312380893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305039972131667356874920595 457559958197501035312380893)
    ·
      refine ⟨171584984324062888242142835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457559958197501035312380893 171584984324062888242142835)
      ·
        refine ⟨257377476486094332363214253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171584984324062888242142835 257377476486094332363214253)
        ·
          refine ⟨96516553682285374636205345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257377476486094332363214253 96516553682285374636205345)
          ·
            refine ⟨72387415261714030977154009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96516553682285374636205345 72387415261714030977154009)
            ·
              refine ⟨54290561446285523232865507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72387415261714030977154009 54290561446285523232865507)
              ·
                refine ⟨81435842169428284849298261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54290561446285523232865507 81435842169428284849298261)
                ·
                  refine ⟨477163137711493856538857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81435842169428284849298261 477163137711493856538857)
                  ·
                    rfl

theorem cell23_8363447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 9].length) (baseStart_8363447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363447 prefixEnd_8363447 := by exact prefixLift 8363447
  have htrace : WordTrace (prefixWord ++ tailWord_8363447) baseStart_8363447 baseEnd_8363447 := by
    simpa [prefixWord, tailWord_8363447, baseEnd_8363447] using wordTrace_append hprefix tailTrace_8363447
  have hstable : (prefixWord ++ tailWord_8363447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363447).length < 2 ^ (prefixWord ++ tailWord_8363447).sum := by decide
  have hdescent : baseEnd_8363447 < baseStart_8363447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363454 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_8363454 : Nat := 118140960795 + 8363454 * 2 ^ 59
def prefixEnd_8363454 : Nat := 4983230072969 + 3 ^ 40 * 8363454 * 2
def baseEnd_8363454 : Nat := 4294471833768026181462181

theorem tailTrace_8363454 : CollatzResearch.WordTrace tailWord_8363454 prefixEnd_8363454 4294471833768026181462181 := by
  unfold tailWord_8363454
  simp only [CollatzResearch.WordTrace]
  refine ⟨38130028430330249633803177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203360151628427998046950277 38130028430330249633803177)
  ·
    refine ⟨28597521322747687225352383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38130028430330249633803177 28597521322747687225352383)
    ·
      refine ⟨42896281984121530838028575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28597521322747687225352383 42896281984121530838028575)
      ·
        refine ⟨64344422976182296257042863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42896281984121530838028575 64344422976182296257042863)
        ·
          refine ⟨96516634464273444385564295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64344422976182296257042863 96516634464273444385564295)
          ·
            refine ⟨144774951696410166578346443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96516634464273444385564295 144774951696410166578346443)
            ·
              refine ⟨217162427544615249867519665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144774951696410166578346443 217162427544615249867519665)
              ·
                refine ⟨162871820658461437400639749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217162427544615249867519665 162871820658461437400639749)
                ·
                  refine ⟨30538466373461519512619953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162871820658461437400639749 30538466373461519512619953)
                  ·
                    refine ⟨22903849780096139634464965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30538466373461519512619953 22903849780096139634464965)
                    ·
                      refine ⟨4294471833768026181462181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22903849780096139634464965 4294471833768026181462181)
                      ·
                        rfl

theorem cell23_8363454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_8363454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363454 prefixEnd_8363454 := by exact prefixLift 8363454
  have htrace : WordTrace (prefixWord ++ tailWord_8363454) baseStart_8363454 baseEnd_8363454 := by
    simpa [prefixWord, tailWord_8363454, baseEnd_8363454] using wordTrace_append hprefix tailTrace_8363454
  have hstable : (prefixWord ++ tailWord_8363454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363454).length < 2 ^ (prefixWord ++ tailWord_8363454).sum := by decide
  have hdescent : baseEnd_8363454 < baseStart_8363454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363481 : List Nat := [1, 2, 1, 2, 4, 3, 1, 4, 5]
def baseStart_8363481 : Nat := 118140960795 + 8363481 * 2 ^ 59
def prefixEnd_8363481 : Nat := 4983230072969 + 3 ^ 40 * 8363481 * 2
def baseEnd_8363481 : Nat := 477165077527299730647173

theorem tailTrace_8363481 : CollatzResearch.WordTrace tailWord_8363481 prefixEnd_8363481 477165077527299730647173 := by
  unfold tailWord_8363481
  simp only [CollatzResearch.WordTrace]
  refine ⟨305041212213544180681658297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203360808142362787121105531 305041212213544180681658297)
  ·
    refine ⟨228780909160158135511243723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305041212213544180681658297 228780909160158135511243723)
    ·
      refine ⟨343171363740237203266865585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228780909160158135511243723 343171363740237203266865585)
      ·
        refine ⟨257378522805177902450149189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343171363740237203266865585 257378522805177902450149189)
        ·
          refine ⟨48258473025970856709402973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257378522805177902450149189 48258473025970856709402973)
          ·
            refine ⟨18096927384739071266026115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48258473025970856709402973 18096927384739071266026115)
            ·
              refine ⟨27145391077108606899039173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18096927384739071266026115 27145391077108606899039173)
              ·
                refine ⟨5089760826957863793569845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27145391077108606899039173 5089760826957863793569845)
                ·
                  refine ⟨477165077527299730647173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5089760826957863793569845 477165077527299730647173)
                  ·
                    rfl

theorem cell23_8363481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 5].length) (baseStart_8363481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363481 prefixEnd_8363481 := by exact prefixLift 8363481
  have htrace : WordTrace (prefixWord ++ tailWord_8363481) baseStart_8363481 baseEnd_8363481 := by
    simpa [prefixWord, tailWord_8363481, baseEnd_8363481] using wordTrace_append hprefix tailTrace_8363481
  have hstable : (prefixWord ++ tailWord_8363481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363481).length < 2 ^ (prefixWord ++ tailWord_8363481).sum := by decide
  have hdescent : baseEnd_8363481 < baseStart_8363481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363491 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 3]
def baseStart_8363491 : Nat := 118140960795 + 8363491 * 2 ^ 59
def prefixEnd_8363491 : Nat := 4983230072969 + 3 ^ 40 * 8363491 * 2
def baseEnd_8363491 : Nat := 4294490832552242536699511

theorem tailTrace_8363491 : CollatzResearch.WordTrace tailWord_8363491 prefixEnd_8363491 4294490832552242536699511 := by
  unfold tailWord_8363491
  simp only [CollatzResearch.WordTrace]
  refine ⟨305041576943507952389522327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203361051295671968259681551 305041576943507952389522327)
  ·
    refine ⟨457562365415261928584283491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305041576943507952389522327 457562365415261928584283491)
    ·
      refine ⟨686343548122892892876425237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457562365415261928584283491 686343548122892892876425237)
      ·
        refine ⟨32172353818260604353582433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 686343548122892892876425237 32172353818260604353582433)
        ·
          refine ⟨24129265363695453265186825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32172353818260604353582433 24129265363695453265186825)
          ·
            refine ⟨18096949022771589948890119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24129265363695453265186825 18096949022771589948890119)
            ·
              refine ⟨27145423534157384923335179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18096949022771589948890119 27145423534157384923335179)
              ·
                refine ⟨40718135301236077385002769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27145423534157384923335179 40718135301236077385002769)
                ·
                  refine ⟨30538601475927058038752077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40718135301236077385002769 30538601475927058038752077)
                  ·
                    refine ⟨11451975553472646764532029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30538601475927058038752077 11451975553472646764532029)
                    ·
                      refine ⟨4294490832552242536699511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11451975553472646764532029 4294490832552242536699511)
                      ·
                        rfl

theorem cell23_8363491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_8363491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363491 prefixEnd_8363491 := by exact prefixLift 8363491
  have htrace : WordTrace (prefixWord ++ tailWord_8363491) baseStart_8363491 baseEnd_8363491 := by
    simpa [prefixWord, tailWord_8363491, baseEnd_8363491] using wordTrace_append hprefix tailTrace_8363491
  have hstable : (prefixWord ++ tailWord_8363491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363491).length < 2 ^ (prefixWord ++ tailWord_8363491).sum := by decide
  have hdescent : baseEnd_8363491 < baseStart_8363491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363507 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 10]
def baseStart_8363507 : Nat := 118140960795 + 8363507 * 2 ^ 59
def prefixEnd_8363507 : Nat := 4983230072969 + 3 ^ 40 * 8363507 * 2
def baseEnd_8363507 : Nat := 1431499682747571491366479

theorem tailTrace_8363507 : CollatzResearch.WordTrace tailWord_8363507 prefixEnd_8363507 1431499682747571491366479 := by
  unfold tailWord_8363507
  simp only [CollatzResearch.WordTrace]
  refine ⟨305042160511449987122104775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203361440340966658081403183 305042160511449987122104775)
  ·
    refine ⟨457563240767174980683157163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305042160511449987122104775 457563240767174980683157163)
    ·
      refine ⟨686344861150762471024735745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457563240767174980683157163 686344861150762471024735745)
      ·
        refine ⟨514758645863071853268551809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686344861150762471024735745 514758645863071853268551809)
        ·
          refine ⟨386068984397303889951413857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514758645863071853268551809 386068984397303889951413857)
          ·
            refine ⟨289551738297977917463560393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386068984397303889951413857 289551738297977917463560393)
            ·
              refine ⟨217163803723483438097670295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289551738297977917463560393 217163803723483438097670295)
              ·
                refine ⟨325745705585225157146505443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217163803723483438097670295 325745705585225157146505443)
                ·
                  refine ⟨488618558377837735719758165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325745705585225157146505443 488618558377837735719758165)
                  ·
                    refine ⟨1431499682747571491366479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 488618558377837735719758165 1431499682747571491366479)
                    ·
                      rfl

theorem cell23_8363507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 10].length) (baseStart_8363507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363507 prefixEnd_8363507 := by exact prefixLift 8363507
  have htrace : WordTrace (prefixWord ++ tailWord_8363507) baseStart_8363507 baseEnd_8363507 := by
    simpa [prefixWord, tailWord_8363507, baseEnd_8363507] using wordTrace_append hprefix tailTrace_8363507
  have hstable : (prefixWord ++ tailWord_8363507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363507).length < 2 ^ (prefixWord ++ tailWord_8363507).sum := by decide
  have hdescent : baseEnd_8363507 < baseStart_8363507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363514 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_8363514 : Nat := 118140960795 + 8363514 * 2 ^ 59
def prefixEnd_8363514 : Nat := 4983230072969 + 3 ^ 40 * 8363514 * 2
def baseEnd_8363514 : Nat := 4294502642607295946711905

theorem tailTrace_8363514 : CollatzResearch.WordTrace tailWord_8363514 prefixEnd_8363514 4294502642607295946711905 := by
  unfold tailWord_8363514
  simp only [CollatzResearch.WordTrace]
  refine ⟨76260603955606156829402399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203361610548283084878406397 76260603955606156829402399)
  ·
    refine ⟨114390905933409235244103599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76260603955606156829402399 114390905933409235244103599)
    ·
      refine ⟨171586358900113852866155399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114390905933409235244103599 171586358900113852866155399)
      ·
        refine ⟨257379538350170779299233099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171586358900113852866155399 257379538350170779299233099)
        ·
          refine ⟨386069307525256168948849649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257379538350170779299233099 386069307525256168948849649)
          ·
            refine ⟨289551980643942126711637237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386069307525256168948849649 289551980643942126711637237)
            ·
              refine ⟨27145498185369574379215991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289551980643942126711637237 27145498185369574379215991)
              ·
                refine ⟨40718247278054361568823987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27145498185369574379215991 40718247278054361568823987)
                ·
                  refine ⟨61077370917081542353235981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40718247278054361568823987 61077370917081542353235981)
                  ·
                    refine ⟨22904014093905578382463493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61077370917081542353235981 22904014093905578382463493)
                    ·
                      refine ⟨4294502642607295946711905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22904014093905578382463493 4294502642607295946711905)
                      ·
                        rfl

theorem cell23_8363514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_8363514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363514 prefixEnd_8363514 := by exact prefixLift 8363514
  have htrace : WordTrace (prefixWord ++ tailWord_8363514) baseStart_8363514 baseEnd_8363514 := by
    simpa [prefixWord, tailWord_8363514, baseEnd_8363514] using wordTrace_append hprefix tailTrace_8363514
  have hstable : (prefixWord ++ tailWord_8363514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363514).length < 2 ^ (prefixWord ++ tailWord_8363514).sum := by decide
  have hdescent : baseEnd_8363514 < baseStart_8363514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363541 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_8363541 : Nat := 118140960795 + 8363541 * 2 ^ 59
def prefixEnd_8363541 : Nat := 4983230072969 + 3 ^ 40 * 8363541 * 2
def baseEnd_8363541 : Nat := 1431505502194989113691427

theorem tailTrace_8363541 : CollatzResearch.WordTrace tailWord_8363541 prefixEnd_8363541 1431505502194989113691427 := by
  unfold tailWord_8363541
  simp only [CollatzResearch.WordTrace]
  refine ⟨305043400593326810928842477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203362267062217873952561651 305043400593326810928842477)
  ·
    refine ⟨114391275222497554098315929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305043400593326810928842477 114391275222497554098315929)
    ·
      refine ⟨85793456416873165573736947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114391275222497554098315929 85793456416873165573736947)
      ·
        refine ⟨128690184625309748360605421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85793456416873165573736947 128690184625309748360605421)
        ·
          refine ⟨48258819234491155635227033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128690184625309748360605421 48258819234491155635227033)
          ·
            refine ⟨36194114425868366726420275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48258819234491155635227033 36194114425868366726420275)
            ·
              refine ⟨54291171638802550089630413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36194114425868366726420275 54291171638802550089630413)
              ·
                refine ⟨20359189364550956283611405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54291171638802550089630413 20359189364550956283611405)
                ·
                  refine ⟨7634696011706608606354277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20359189364550956283611405 7634696011706608606354277)
                  ·
                    refine ⟨1431505502194989113691427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7634696011706608606354277 1431505502194989113691427)
                    ·
                      rfl

theorem cell23_8363541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_8363541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363541 prefixEnd_8363541 := by exact prefixLift 8363541
  have htrace : WordTrace (prefixWord ++ tailWord_8363541) baseStart_8363541 baseEnd_8363541 := by
    simpa [prefixWord, tailWord_8363541, baseEnd_8363541] using wordTrace_append hprefix tailTrace_8363541
  have hstable : (prefixWord ++ tailWord_8363541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363541).length < 2 ^ (prefixWord ++ tailWord_8363541).sum := by decide
  have hdescent : baseEnd_8363541 < baseStart_8363541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363575 : List Nat := [1, 1, 3, 1, 2, 6, 1, 3, 1, 4]
def baseStart_8363575 : Nat := 118140960795 + 8363575 * 2 ^ 59
def prefixEnd_8363575 : Nat := 4983230072969 + 3 ^ 40 * 8363575 * 2
def baseEnd_8363575 : Nat := 1431511321642406736016375

theorem tailTrace_8363575 : CollatzResearch.WordTrace tailWord_8363575 prefixEnd_8363575 1431511321642406736016375 := by
  unfold tailWord_8363575
  simp only [CollatzResearch.WordTrace]
  refine ⟨305044640675203634735580179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203363093783469089823720119 305044640675203634735580179)
  ·
    refine ⟨457566961012805452103370269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305044640675203634735580179 457566961012805452103370269)
    ·
      refine ⟨171587610379802044538763851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457566961012805452103370269 171587610379802044538763851)
      ·
        refine ⟨257381415569703066808145777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171587610379802044538763851 257381415569703066808145777)
        ·
          refine ⟨193036061677277300106109333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257381415569703066808145777 193036061677277300106109333)
          ·
            refine ⟨9048565391122373442473875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193036061677277300106109333 9048565391122373442473875)
            ·
              refine ⟨13572848086683560163710813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048565391122373442473875 13572848086683560163710813)
              ·
                refine ⟨5089818032506335061391555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13572848086683560163710813 5089818032506335061391555)
                ·
                  refine ⟨7634727048759502592087333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089818032506335061391555 7634727048759502592087333)
                  ·
                    refine ⟨1431511321642406736016375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7634727048759502592087333 1431511321642406736016375)
                    ·
                      rfl

theorem cell23_8363575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_8363575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363575 prefixEnd_8363575 := by exact prefixLift 8363575
  have htrace : WordTrace (prefixWord ++ tailWord_8363575) baseStart_8363575 baseEnd_8363575 := by
    simpa [prefixWord, tailWord_8363575, baseEnd_8363575] using wordTrace_append hprefix tailTrace_8363575
  have hstable : (prefixWord ++ tailWord_8363575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363575).length < 2 ^ (prefixWord ++ tailWord_8363575).sum := by decide
  have hdescent : baseEnd_8363575 < baseStart_8363575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363584 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 5, 5]
def baseStart_8363584 : Nat := 118140960795 + 8363584 * 2 ^ 59
def prefixEnd_8363584 : Nat := 4983230072969 + 3 ^ 40 * 8363584 * 2
def baseEnd_8363584 : Nat := 1431512862084370224278861

theorem tailTrace_8363584 : CollatzResearch.WordTrace tailWord_8363584 prefixEnd_8363584 1431512862084370224278861 := by
  unfold tailWord_8363584
  simp only [CollatzResearch.WordTrace]
  refine ⟨152522484466085514636328903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203363312621447352848438537 152522484466085514636328903)
  ·
    refine ⟨228783726699128271954493355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152522484466085514636328903 228783726699128271954493355)
    ·
      refine ⟨343175590048692407931740033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228783726699128271954493355 343175590048692407931740033)
      ·
        refine ⟨257381692536519305948805025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343175590048692407931740033 257381692536519305948805025)
        ·
          refine ⟨193036269402389479461603769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257381692536519305948805025 193036269402389479461603769)
          ·
            refine ⟨144777202051792109596202827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193036269402389479461603769 144777202051792109596202827)
            ·
              refine ⟨217165803077688164394304241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144777202051792109596202827 217165803077688164394304241)
              ·
                refine ⟨162874352308266123295728181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217165803077688164394304241 162874352308266123295728181)
                ·
                  refine ⟨15269470528899949058974517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162874352308266123295728181 15269470528899949058974517)
                  ·
                    refine ⟨1431512862084370224278861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15269470528899949058974517 1431512862084370224278861)
                    ·
                      rfl

theorem cell23_8363584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_8363584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363584 prefixEnd_8363584 := by exact prefixLift 8363584
  have htrace : WordTrace (prefixWord ++ tailWord_8363584) baseStart_8363584 baseEnd_8363584 := by
    simpa [prefixWord, tailWord_8363584, baseEnd_8363584] using wordTrace_append hprefix tailTrace_8363584
  have hstable : (prefixWord ++ tailWord_8363584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363584).length < 2 ^ (prefixWord ++ tailWord_8363584).sum := by decide
  have hdescent : baseEnd_8363584 < baseStart_8363584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363648 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 2, 4]
def baseStart_8363648 : Nat := 118140960795 + 8363648 * 2 ^ 59
def prefixEnd_8363648 : Nat := 4983230072969 + 3 ^ 40 * 8363648 * 2
def baseEnd_8363648 : Nat := 1431523816338332807478763

theorem tailTrace_8363648 : CollatzResearch.WordTrace tailWord_8363648 prefixEnd_8363648 1431523816338332807478763 := by
  unfold tailWord_8363648
  simp only [CollatzResearch.WordTrace]
  refine ⟨152523651601969584101493799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203364868802626112135325065 152523651601969584101493799)
  ·
    refine ⟨228785477402954376152240699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152523651601969584101493799 228785477402954376152240699)
    ·
      refine ⟨343178216104431564228361049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228785477402954376152240699 343178216104431564228361049)
      ·
        refine ⟨257383662078323673171270787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343178216104431564228361049 257383662078323673171270787)
        ·
          refine ⟨386075493117485509756906181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257383662078323673171270787 386075493117485509756906181)
          ·
            refine ⟨72389154959528533079419909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386075493117485509756906181 72389154959528533079419909)
            ·
              refine ⟨13572966554911599952391233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72389154959528533079419909 13572966554911599952391233)
              ·
                refine ⟨10179724916183699964293425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13572966554911599952391233 10179724916183699964293425)
                ·
                  refine ⟨7634793687137774973220069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10179724916183699964293425 7634793687137774973220069)
                  ·
                    refine ⟨1431523816338332807478763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7634793687137774973220069 1431523816338332807478763)
                    ·
                      rfl

theorem cell23_8363648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 4].length) (baseStart_8363648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363648 prefixEnd_8363648 := by exact prefixLift 8363648
  have htrace : WordTrace (prefixWord ++ tailWord_8363648) baseStart_8363648 baseEnd_8363648 := by
    simpa [prefixWord, tailWord_8363648, baseEnd_8363648] using wordTrace_append hprefix tailTrace_8363648
  have hstable : (prefixWord ++ tailWord_8363648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363648).length < 2 ^ (prefixWord ++ tailWord_8363648).sum := by decide
  have hdescent : baseEnd_8363648 < baseStart_8363648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363649 : List Nat := [1, 2, 4, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_8363649 : Nat := 118140960795 + 8363649 * 2 ^ 59
def prefixEnd_8363649 : Nat := 4983230072969 + 3 ^ 40 * 8363649 * 2
def baseEnd_8363649 : Nat := 4294571962495652918523785

theorem tailTrace_8363649 : CollatzResearch.WordTrace tailWord_8363649 prefixEnd_8363649 4294571962495652918523785 := by
  unfold tailWord_8363649
  simp only [CollatzResearch.WordTrace]
  refine ⟨305047339676935545373774001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203364893117957030249182667 305047339676935545373774001)
  ·
    refine ⟨228785504757701659030330501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305047339676935545373774001 228785504757701659030330501)
    ·
      refine ⟨42897282142069061068186969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228785504757701659030330501 42897282142069061068186969)
      ·
        refine ⟨32172961606551795801140227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42897282142069061068186969 32172961606551795801140227)
        ·
          refine ⟨48259442409827693701710341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32172961606551795801140227 48259442409827693701710341)
          ·
            refine ⟨9048645451842692569070689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48259442409827693701710341 9048645451842692569070689)
            ·
              refine ⟨6786484088882019426803017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9048645451842692569070689 6786484088882019426803017)
              ·
                refine ⟨5089863066661514570102263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6786484088882019426803017 5089863066661514570102263)
                ·
                  refine ⟨7634794599992271855153395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089863066661514570102263 7634794599992271855153395)
                  ·
                    refine ⟨11452191899988407782730093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7634794599992271855153395 11452191899988407782730093)
                    ·
                      refine ⟨4294571962495652918523785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11452191899988407782730093 4294571962495652918523785)
                      ·
                        rfl

theorem cell23_8363649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_8363649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363649 prefixEnd_8363649 := by exact prefixLift 8363649
  have htrace : WordTrace (prefixWord ++ tailWord_8363649) baseStart_8363649 baseEnd_8363649 := by
    simpa [prefixWord, tailWord_8363649, baseEnd_8363649] using wordTrace_append hprefix tailTrace_8363649
  have hstable : (prefixWord ++ tailWord_8363649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363649).length < 2 ^ (prefixWord ++ tailWord_8363649).sum := by decide
  have hdescent : baseEnd_8363649 < baseStart_8363649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363658 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_8363658 : Nat := 118140960795 + 8363658 * 2 ^ 59
def prefixEnd_8363658 : Nat := 4983230072969 + 3 ^ 40 * 8363658 * 2
def baseEnd_8363658 : Nat := 4294576583821543383311243

theorem tailTrace_8363658 : CollatzResearch.WordTrace tailWord_8363658 prefixEnd_8363658 4294576583821543383311243 := by
  unfold tailWord_8363658
  simp only [CollatzResearch.WordTrace]
  refine ⟨76261916983475734977712907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203365111955935293273901085 76261916983475734977712907)
  ·
    refine ⟨114392875475213602466569361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76261916983475734977712907 114392875475213602466569361)
    ·
      refine ⟨85794656606410201849927021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114392875475213602466569361 85794656606410201849927021)
      ·
        refine ⟨32172996227403825693722633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85794656606410201849927021 32172996227403825693722633)
        ·
          refine ⟨24129747170552869270291975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32172996227403825693722633 24129747170552869270291975)
          ·
            refine ⟨36194620755829303905437963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24129747170552869270291975 36194620755829303905437963)
            ·
              refine ⟨54291931133743955858156945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36194620755829303905437963 54291931133743955858156945)
              ·
                refine ⟨40718948350307966893617709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54291931133743955858156945 40718948350307966893617709)
                ·
                  refine ⟨15269605631365487585106641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40718948350307966893617709 15269605631365487585106641)
                  ·
                    refine ⟨11452204223524115688829981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15269605631365487585106641 11452204223524115688829981)
                    ·
                      refine ⟨4294576583821543383311243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11452204223524115688829981 4294576583821543383311243)
                      ·
                        rfl

theorem cell23_8363658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_8363658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363658 prefixEnd_8363658 := by exact prefixLift 8363658
  have htrace : WordTrace (prefixWord ++ tailWord_8363658) baseStart_8363658 baseEnd_8363658 := by
    simpa [prefixWord, tailWord_8363658, baseEnd_8363658] using wordTrace_append hprefix tailTrace_8363658
  have hstable : (prefixWord ++ tailWord_8363658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363658).length < 2 ^ (prefixWord ++ tailWord_8363658).sum := by decide
  have hdescent : baseEnd_8363658 < baseStart_8363658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363664 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_8363664 : Nat := 118140960795 + 8363664 * 2 ^ 59
def prefixEnd_8363664 : Nat := 4983230072969 + 3 ^ 40 * 8363664 * 2
def baseEnd_8363664 : Nat := 4294579664705470359836215

theorem tailTrace_8363664 : CollatzResearch.WordTrace tailWord_8363664 prefixEnd_8363664 4294579664705470359836215 := by
  unfold tailWord_8363664
  simp only [CollatzResearch.WordTrace]
  refine ⟨152523943385940601467785023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203365257847920801957046697 152523943385940601467785023)
  ·
    refine ⟨228785915078910902201677535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152523943385940601467785023 228785915078910902201677535)
    ·
      refine ⟨343178872618366353302516303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228785915078910902201677535 343178872618366353302516303)
      ·
        refine ⟨514768308927549529953774455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343178872618366353302516303 514768308927549529953774455)
        ·
          refine ⟨772152463391324294930661683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514768308927549529953774455 772152463391324294930661683)
          ·
            refine ⟨1158228695086986442395992525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772152463391324294930661683 1158228695086986442395992525)
            ·
              refine ⟨434335760657619915898497197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1158228695086986442395992525 434335760657619915898497197)
              ·
                refine ⟨162875910246607468461936449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434335760657619915898497197 162875910246607468461936449)
                ·
                  refine ⟨122156932684955601346452337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162875910246607468461936449 122156932684955601346452337)
                  ·
                    refine ⟨91617699513716701009839253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122156932684955601346452337 91617699513716701009839253)
                    ·
                      refine ⟨4294579664705470359836215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91617699513716701009839253 4294579664705470359836215)
                      ·
                        rfl

theorem cell23_8363664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_8363664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363664 prefixEnd_8363664 := by exact prefixLift 8363664
  have htrace : WordTrace (prefixWord ++ tailWord_8363664) baseStart_8363664 baseEnd_8363664 := by
    simpa [prefixWord, tailWord_8363664, baseEnd_8363664] using wordTrace_append hprefix tailTrace_8363664
  have hstable : (prefixWord ++ tailWord_8363664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363664).length < 2 ^ (prefixWord ++ tailWord_8363664).sum := by decide
  have hdescent : baseEnd_8363664 < baseStart_8363664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363705 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 3]
def baseStart_8363705 : Nat := 118140960795 + 8363705 * 2 ^ 59
def prefixEnd_8363705 : Nat := 4983230072969 + 3 ^ 40 * 8363705 * 2
def baseEnd_8363705 : Nat := 4294600717412304699423527

theorem tailTrace_8363705 : CollatzResearch.WordTrace tailWord_8363705 prefixEnd_8363705 4294600717412304699423527 := by
  unfold tailWord_8363705
  simp only [CollatzResearch.WordTrace]
  refine ⟨305049382164732666937812569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203366254776488444625208379 305049382164732666937812569)
  ·
    refine ⟨228787036623549500203359427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305049382164732666937812569 228787036623549500203359427)
    ·
      refine ⟨343180554935324250305039141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228787036623549500203359427 343180554935324250305039141)
      ·
        refine ⟨64346354050373296932194839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343180554935324250305039141 64346354050373296932194839)
        ·
          refine ⟨96519531075559945398292259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64346354050373296932194839 96519531075559945398292259)
          ·
            refine ⟨144779296613339918097438389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96519531075559945398292259 144779296613339918097438389)
            ·
              refine ⟨13573059057500617321634849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144779296613339918097438389 13573059057500617321634849)
              ·
                refine ⟨10179794293125462991226137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13573059057500617321634849 10179794293125462991226137)
                ·
                  refine ⟨7634845719844097243419603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10179794293125462991226137 7634845719844097243419603)
                  ·
                    refine ⟨11452268579766145865129405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7634845719844097243419603 11452268579766145865129405)
                    ·
                      refine ⟨4294600717412304699423527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11452268579766145865129405 4294600717412304699423527)
                      ·
                        rfl

theorem cell23_8363705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_8363705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363705 prefixEnd_8363705 := by exact prefixLift 8363705
  have htrace : WordTrace (prefixWord ++ tailWord_8363705) baseStart_8363705 baseEnd_8363705 := by
    simpa [prefixWord, tailWord_8363705, baseEnd_8363705] using wordTrace_append hprefix tailTrace_8363705
  have hstable : (prefixWord ++ tailWord_8363705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363705).length < 2 ^ (prefixWord ++ tailWord_8363705).sum := by decide
  have hdescent : baseEnd_8363705 < baseStart_8363705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363722 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_8363722 : Nat := 118140960795 + 8363722 * 2 ^ 59
def prefixEnd_8363722 : Nat := 4983230072969 + 3 ^ 40 * 8363722 * 2
def baseEnd_8363722 : Nat := 4294609446583431132910949

theorem tailTrace_8363722 : CollatzResearch.WordTrace tailWord_8363722 prefixEnd_8363722 4294609446583431132910949 := by
  unfold tailWord_8363722
  simp only [CollatzResearch.WordTrace]
  refine ⟨76262500551417769710295355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203366668137114052560787613 76262500551417769710295355)
  ·
    refine ⟨114393750827126654565443033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76262500551417769710295355 114393750827126654565443033)
    ·
      refine ⟨85795313120344990924082275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114393750827126654565443033 85795313120344990924082275)
      ·
        refine ⟨128692969680517486386123413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85795313120344990924082275 128692969680517486386123413)
        ·
          refine ⟨6032482953774257174349535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128692969680517486386123413 6032482953774257174349535)
          ·
            refine ⟨9048724430661385761524303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032482953774257174349535 9048724430661385761524303)
            ·
              refine ⟨13573086645992078642286455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048724430661385761524303 13573086645992078642286455)
              ·
                refine ⟨20359629968988117963429683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13573086645992078642286455 20359629968988117963429683)
                ·
                  refine ⟨30539444953482176945144525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20359629968988117963429683 30539444953482176945144525)
                  ·
                    refine ⟨11452291857555816354429197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30539444953482176945144525 11452291857555816354429197)
                    ·
                      refine ⟨4294609446583431132910949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11452291857555816354429197 4294609446583431132910949)
                      ·
                        rfl

theorem cell23_8363722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_8363722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363722 prefixEnd_8363722 := by exact prefixLift 8363722
  have htrace : WordTrace (prefixWord ++ tailWord_8363722) baseStart_8363722 baseEnd_8363722 := by
    simpa [prefixWord, tailWord_8363722, baseEnd_8363722] using wordTrace_append hprefix tailTrace_8363722
  have hstable : (prefixWord ++ tailWord_8363722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363722).length < 2 ^ (prefixWord ++ tailWord_8363722).sum := by decide
  have hdescent : baseEnd_8363722 < baseStart_8363722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363728 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 1, 4, 2]
def baseStart_8363728 : Nat := 118140960795 + 8363728 * 2 ^ 59
def prefixEnd_8363728 : Nat := 4983230072969 + 3 ^ 40 * 8363728 * 2
def baseEnd_8363728 : Nat := 4294612527467358109435921

theorem tailTrace_8363728 : CollatzResearch.WordTrace tailWord_8363728 prefixEnd_8363728 4294612527467358109435921 := by
  unfold tailWord_8363728
  simp only [CollatzResearch.WordTrace]
  refine ⟨152525110521824670932949919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203366814029099561243933225 152525110521824670932949919)
  ·
    refine ⟨228787665782737006399424879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152525110521824670932949919 228787665782737006399424879)
    ·
      refine ⟨343181498674105509599137319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228787665782737006399424879 343181498674105509599137319)
      ·
        refine ⟨514772248011158264398705979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343181498674105509599137319 514772248011158264398705979)
        ·
          refine ⟨772158372016737396598058969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514772248011158264398705979 772158372016737396598058969)
          ·
            refine ⟨579118779012553047448544227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772158372016737396598058969 579118779012553047448544227)
            ·
              refine ⟨868678168518829571172816341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579118779012553047448544227 868678168518829571172816341)
              ·
                refine ⟨20359644574660068074362883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 868678168518829571172816341 20359644574660068074362883)
                ·
                  refine ⟨30539466861990102111544325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20359644574660068074362883 30539466861990102111544325)
                  ·
                    refine ⟨5726150036623144145914561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30539466861990102111544325 5726150036623144145914561)
                    ·
                      refine ⟨4294612527467358109435921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726150036623144145914561 4294612527467358109435921)
                      ·
                        rfl

theorem cell23_8363728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 4, 2].length) (baseStart_8363728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363728 prefixEnd_8363728 := by exact prefixLift 8363728
  have htrace : WordTrace (prefixWord ++ tailWord_8363728) baseStart_8363728 baseEnd_8363728 := by
    simpa [prefixWord, tailWord_8363728, baseEnd_8363728] using wordTrace_append hprefix tailTrace_8363728
  have hstable : (prefixWord ++ tailWord_8363728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363728).length < 2 ^ (prefixWord ++ tailWord_8363728).sum := by decide
  have hdescent : baseEnd_8363728 < baseStart_8363728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363732 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_8363732 : Nat := 118140960795 + 8363732 * 2 ^ 59
def prefixEnd_8363732 : Nat := 4983230072969 + 3 ^ 40 * 8363732 * 2
def baseEnd_8363732 : Nat := 4294614581389976093785903

theorem tailTrace_8363732 : CollatzResearch.WordTrace tailWord_8363732 prefixEnd_8363732 4294614581389976093785903 := by
  unfold tailWord_8363732
  simp only [CollatzResearch.WordTrace]
  refine ⟨152525183467817425274522725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203366911290423233699363633 152525183467817425274522725)
  ·
    refine ⟨28598471900215767238973011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152525183467817425274522725 28598471900215767238973011)
    ·
      refine ⟨42897707850323650858459517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28598471900215767238973011 42897707850323650858459517)
      ·
        refine ⟨16086640443871369071922319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42897707850323650858459517 16086640443871369071922319)
        ·
          refine ⟨24129960665807053607883479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16086640443871369071922319 24129960665807053607883479)
          ·
            refine ⟨36194940998710580411825219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24129960665807053607883479 36194940998710580411825219)
            ·
              refine ⟨54292411498065870617737829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36194940998710580411825219 54292411498065870617737829)
              ·
                refine ⟨10179827155887350740825843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54292411498065870617737829 10179827155887350740825843)
                ·
                  refine ⟨15269740733831026111238765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10179827155887350740825843 15269740733831026111238765)
                  ·
                    refine ⟨5726152775186634791714537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15269740733831026111238765 5726152775186634791714537)
                    ·
                      refine ⟨4294614581389976093785903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726152775186634791714537 4294614581389976093785903)
                      ·
                        rfl

theorem cell23_8363732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_8363732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363732 prefixEnd_8363732 := by exact prefixLift 8363732
  have htrace : WordTrace (prefixWord ++ tailWord_8363732) baseStart_8363732 baseEnd_8363732 := by
    simpa [prefixWord, tailWord_8363732, baseEnd_8363732] using wordTrace_append hprefix tailTrace_8363732
  have hstable : (prefixWord ++ tailWord_8363732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363732).length < 2 ^ (prefixWord ++ tailWord_8363732).sum := by decide
  have hdescent : baseEnd_8363732 < baseStart_8363732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363762 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_8363762 : Nat := 118140960795 + 8363762 * 2 ^ 59
def prefixEnd_8363762 : Nat := 4983230072969 + 3 ^ 40 * 8363762 * 2
def baseEnd_8363762 : Nat := 4294629985809610976410765

theorem tailTrace_8363762 : CollatzResearch.WordTrace tailWord_8363762 prefixEnd_8363762 4294629985809610976410765 := by
  unfold tailWord_8363762
  simp only [CollatzResearch.WordTrace]
  refine ⟨76262865281381541418159385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203367640750350777115091693 76262865281381541418159385)
  ·
    refine ⟨57197148961036156063619539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76262865281381541418159385 57197148961036156063619539)
    ·
      refine ⟨85795723441554234095429309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57197148961036156063619539 85795723441554234095429309)
      ·
        refine ⟨32173396290582837785785991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85795723441554234095429309 32173396290582837785785991)
        ·
          refine ⟨48260094435874256678678987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32173396290582837785785991 48260094435874256678678987)
          ·
            refine ⟨72390141653811385018018481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48260094435874256678678987 72390141653811385018018481)
            ·
              refine ⟨54292606240358538763513861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72390141653811385018018481 54292606240358538763513861)
              ·
                refine ⟨10179863670067226018158849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54292606240358538763513861 10179863670067226018158849)
                ·
                  refine ⟨7634897752550419513619137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10179863670067226018158849 7634897752550419513619137)
                  ·
                    refine ⟨5726173314412814635214353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7634897752550419513619137 5726173314412814635214353)
                    ·
                      refine ⟨4294629985809610976410765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726173314412814635214353 4294629985809610976410765)
                      ·
                        rfl

theorem cell23_8363762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_8363762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363762 prefixEnd_8363762 := by exact prefixLift 8363762
  have htrace : WordTrace (prefixWord ++ tailWord_8363762) baseStart_8363762 baseEnd_8363762 := by
    simpa [prefixWord, tailWord_8363762, baseEnd_8363762] using wordTrace_append hprefix tailTrace_8363762
  have hstable : (prefixWord ++ tailWord_8363762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363762).length < 2 ^ (prefixWord ++ tailWord_8363762).sum := by decide
  have hdescent : baseEnd_8363762 < baseStart_8363762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363796 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_8363796 : Nat := 118140960795 + 8363796 * 2 ^ 59
def prefixEnd_8363796 : Nat := 4983230072969 + 3 ^ 40 * 8363796 * 2
def baseEnd_8363796 : Nat := 4294647444151863843385609

theorem tailTrace_8363796 : CollatzResearch.WordTrace tailWord_8363796 prefixEnd_8363796 4294647444151863843385609 := by
  unfold tailWord_8363796
  simp only [CollatzResearch.WordTrace]
  refine ⟨152526350603701494739687621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203368467471601992986250161 152526350603701494739687621)
  ·
    refine ⟨28598690738194030263691429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152526350603701494739687621 28598690738194030263691429)
    ·
      refine ⟨5362254513411380674442143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28598690738194030263691429 5362254513411380674442143)
      ·
        refine ⟨8043381770117071011663215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362254513411380674442143 8043381770117071011663215)
        ·
          refine ⟨12065072655175606517494823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043381770117071011663215 12065072655175606517494823)
          ·
            refine ⟨18097608982763409776242235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12065072655175606517494823 18097608982763409776242235)
            ·
              refine ⟨27146413474145114664363353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18097608982763409776242235 27146413474145114664363353)
              ·
                refine ⟨20359810105608835998272515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27146413474145114664363353 20359810105608835998272515)
                ·
                  refine ⟨30539715158413253997408773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20359810105608835998272515 30539715158413253997408773)
                  ·
                    refine ⟨5726196592202485124514145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30539715158413253997408773 5726196592202485124514145)
                    ·
                      refine ⟨4294647444151863843385609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726196592202485124514145 4294647444151863843385609)
                      ·
                        rfl

theorem cell23_8363796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_8363796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363796 prefixEnd_8363796 := by exact prefixLift 8363796
  have htrace : WordTrace (prefixWord ++ tailWord_8363796) baseStart_8363796 baseEnd_8363796 := by
    simpa [prefixWord, tailWord_8363796, baseEnd_8363796] using wordTrace_append hprefix tailTrace_8363796
  have hstable : (prefixWord ++ tailWord_8363796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363796).length < 2 ^ (prefixWord ++ tailWord_8363796).sum := by decide
  have hdescent : baseEnd_8363796 < baseStart_8363796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363801 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_8363801 : Nat := 118140960795 + 8363801 * 2 ^ 59
def prefixEnd_8363801 : Nat := 4983230072969 + 3 ^ 40 * 8363801 * 2
def baseEnd_8363801 : Nat := 4294650011555136323823085

theorem tailTrace_8363801 : CollatzResearch.WordTrace tailWord_8363801 prefixEnd_8363801 4294650011555136323823085 := by
  unfold tailWord_8363801
  simp only [CollatzResearch.WordTrace]
  refine ⟨305052883572384875333307257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203368589048256583555538171 305052883572384875333307257)
  ·
    refine ⟨228789662679288656499980443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305052883572384875333307257 228789662679288656499980443)
    ·
      refine ⟨343184494018932984749970665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228789662679288656499980443 343184494018932984749970665)
      ·
        refine ⟨257388370514199738562477999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343184494018932984749970665 257388370514199738562477999)
        ·
          refine ⟨386082555771299607843716999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257388370514199738562477999 386082555771299607843716999)
          ·
            refine ⟨579123833656949411765575499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386082555771299607843716999 579123833656949411765575499)
            ·
              refine ⟨868685750485424117648363249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579123833656949411765575499 868685750485424117648363249)
              ·
                refine ⟨651514312864068088236272437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868685750485424117648363249 651514312864068088236272437)
                ·
                  refine ⟨61079466831006383272150541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 651514312864068088236272437 61079466831006383272150541)
                  ·
                    refine ⟨22904800061627393727056453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61079466831006383272150541 22904800061627393727056453)
                    ·
                      refine ⟨4294650011555136323823085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22904800061627393727056453 4294650011555136323823085)
                      ·
                        rfl

theorem cell23_8363801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_8363801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363801 prefixEnd_8363801 := by exact prefixLift 8363801
  have htrace : WordTrace (prefixWord ++ tailWord_8363801) baseStart_8363801 baseEnd_8363801 := by
    simpa [prefixWord, tailWord_8363801, baseEnd_8363801] using wordTrace_append hprefix tailTrace_8363801
  have hstable : (prefixWord ++ tailWord_8363801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363801).length < 2 ^ (prefixWord ++ tailWord_8363801).sum := by decide
  have hdescent : baseEnd_8363801 < baseStart_8363801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363831 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_8363831 : Nat := 118140960795 + 8363831 * 2 ^ 59
def prefixEnd_8363831 : Nat := 4983230072969 + 3 ^ 40 * 8363831 * 2
def baseEnd_8363831 : Nat := 4294665415974771206447947

theorem tailTrace_8363831 : CollatzResearch.WordTrace tailWord_8363831 prefixEnd_8363831 4294665415974771206447947 := by
  unfold tailWord_8363831
  simp only [CollatzResearch.WordTrace]
  refine ⟨305053977762276190456899347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203369318508184126971266231 305053977762276190456899347)
  ·
    refine ⟨457580966643414285685349021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305053977762276190456899347 457580966643414285685349021)
    ·
      refine ⟨171592862491280357132005883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457580966643414285685349021 171592862491280357132005883)
      ·
        refine ⟨257389293736920535698008825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171592862491280357132005883 257389293736920535698008825)
        ·
          refine ⟨193041970302690401773506619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257389293736920535698008825 193041970302690401773506619)
          ·
            refine ⟨289562955454035602660259929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193041970302690401773506619 289562955454035602660259929)
            ·
              refine ⟨217172216590526701995194947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289562955454035602660259929 217172216590526701995194947)
              ·
                refine ⟨325758324885790052992792421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217172216590526701995194947 325758324885790052992792421)
                ·
                  refine ⟨61079685916085634936148579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325758324885790052992792421 61079685916085634936148579)
                  ·
                    refine ⟨91619528874128452404222869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61079685916085634936148579 91619528874128452404222869)
                    ·
                      refine ⟨4294665415974771206447947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91619528874128452404222869 4294665415974771206447947)
                      ·
                        rfl

theorem cell23_8363831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_8363831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363831 prefixEnd_8363831 := by exact prefixLift 8363831
  have htrace : WordTrace (prefixWord ++ tailWord_8363831) baseStart_8363831 baseEnd_8363831 := by
    simpa [prefixWord, tailWord_8363831, baseEnd_8363831] using wordTrace_append hprefix tailTrace_8363831
  have hstable : (prefixWord ++ tailWord_8363831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363831).length < 2 ^ (prefixWord ++ tailWord_8363831).sum := by decide
  have hdescent : baseEnd_8363831 < baseStart_8363831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363852 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_8363852 : Nat := 118140960795 + 8363852 * 2 ^ 59
def prefixEnd_8363852 : Nat := 4983230072969 + 3 ^ 40 * 8363852 * 2
def baseEnd_8363852 : Nat := 4294676199068515624285351

theorem tailTrace_8363852 : CollatzResearch.WordTrace tailWord_8363852 prefixEnd_8363852 4294676199068515624285351 := by
  unfold tailWord_8363852
  simp only [CollatzResearch.WordTrace]
  refine ⟨152527371847600055521706905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203369829130133407362275873 152527371847600055521706905)
  ·
    refine ⟨114395528885700041641280179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152527371847600055521706905 114395528885700041641280179)
    ·
      refine ⟨171593293328550062461920269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114395528885700041641280179 171593293328550062461920269)
      ·
        refine ⟨64347484998206273423220101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171593293328550062461920269 64347484998206273423220101)
        ·
          refine ⟨12065153437163676266853769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64347484998206273423220101 12065153437163676266853769)
          ·
            refine ⟨9048865077872757200140327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12065153437163676266853769 9048865077872757200140327)
            ·
              refine ⟨13573297616809135800210491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048865077872757200140327 13573297616809135800210491)
              ·
                refine ⟨20359946425213703700315737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13573297616809135800210491 20359946425213703700315737)
                ·
                  refine ⟨15269959818910277775236803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20359946425213703700315737 15269959818910277775236803)
                  ·
                    refine ⟨22904939728365416662855205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15269959818910277775236803 22904939728365416662855205)
                    ·
                      refine ⟨4294676199068515624285351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22904939728365416662855205 4294676199068515624285351)
                      ·
                        rfl

theorem cell23_8363852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_8363852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363852 prefixEnd_8363852 := by exact prefixLift 8363852
  have htrace : WordTrace (prefixWord ++ tailWord_8363852) baseStart_8363852 baseEnd_8363852 := by
    simpa [prefixWord, tailWord_8363852, baseEnd_8363852] using wordTrace_append hprefix tailTrace_8363852
  have hstable : (prefixWord ++ tailWord_8363852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363852).length < 2 ^ (prefixWord ++ tailWord_8363852).sum := by decide
  have hdescent : baseEnd_8363852 < baseStart_8363852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363922 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_8363922 : Nat := 118140960795 + 8363922 * 2 ^ 59
def prefixEnd_8363922 : Nat := 4983230072969 + 3 ^ 40 * 8363922 * 2
def baseEnd_8363922 : Nat := 1431570714238110116803343

theorem tailTrace_8363922 : CollatzResearch.WordTrace tailWord_8363922 prefixEnd_8363922 1431570714238110116803343 := by
  unfold tailWord_8363922
  simp only [CollatzResearch.WordTrace]
  refine ⟨76264324201236628249615505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203371531203297675332308013 76264324201236628249615505)
  ·
    refine ⟨57198243150927471187211629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76264324201236628249615505 57198243150927471187211629)
    ·
      refine ⟨21449341181597801695204361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57198243150927471187211629 21449341181597801695204361)
      ·
        refine ⟨16087005886198351271403271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21449341181597801695204361 16087005886198351271403271)
        ·
          refine ⟨24130508829297526907104907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16087005886198351271403271 24130508829297526907104907)
          ·
            refine ⟨36195763243946290360657361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24130508829297526907104907 36195763243946290360657361)
            ·
              refine ⟨27146822432959717770493021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36195763243946290360657361 27146822432959717770493021)
              ·
                refine ⟨10180058412359894163934883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27146822432959717770493021 10180058412359894163934883)
                ·
                  refine ⟨15270087618539841245902325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180058412359894163934883 15270087618539841245902325)
                  ·
                    refine ⟨1431570714238110116803343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15270087618539841245902325 1431570714238110116803343)
                    ·
                      rfl

theorem cell23_8363922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_8363922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363922 prefixEnd_8363922 := by exact prefixLift 8363922
  have htrace : WordTrace (prefixWord ++ tailWord_8363922) baseStart_8363922 baseEnd_8363922 := by
    simpa [prefixWord, tailWord_8363922, baseEnd_8363922] using wordTrace_append hprefix tailTrace_8363922
  have hstable : (prefixWord ++ tailWord_8363922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363922).length < 2 ^ (prefixWord ++ tailWord_8363922).sum := by decide
  have hdescent : baseEnd_8363922 < baseStart_8363922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363925 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_8363925 : Nat := 118140960795 + 8363925 * 2 ^ 59
def prefixEnd_8363925 : Nat := 4983230072969 + 3 ^ 40 * 8363925 * 2
def baseEnd_8363925 : Nat := 4294713683156293838672515

theorem tailTrace_8363925 : CollatzResearch.WordTrace tailWord_8363925 prefixEnd_8363925 4294713683156293838672515 := by
  unfold tailWord_8363925
  simp only [CollatzResearch.WordTrace]
  refine ⟨305057406223935644510821229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203371604149290429673880819 305057406223935644510821229)
  ·
    refine ⟨114396527333975866691557961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305057406223935644510821229 114396527333975866691557961)
    ·
      refine ⟨85797395500481900018668471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114396527333975866691557961 85797395500481900018668471)
      ·
        refine ⟨128696093250722850028002707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85797395500481900018668471 128696093250722850028002707)
        ·
          refine ⟨193044139876084275042004061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128696093250722850028002707 193044139876084275042004061)
          ·
            refine ⟨72391552453531603140751523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193044139876084275042004061 72391552453531603140751523)
            ·
              refine ⟨108587328680297404711127285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72391552453531603140751523 108587328680297404711127285)
              ·
                refine ⟨10180062063777881691668183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108587328680297404711127285 10180062063777881691668183)
                ·
                  refine ⟨15270093095666822537502275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180062063777881691668183 15270093095666822537502275)
                  ·
                    refine ⟨22905139643500233806253413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15270093095666822537502275 22905139643500233806253413)
                    ·
                      refine ⟨4294713683156293838672515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22905139643500233806253413 4294713683156293838672515)
                      ·
                        rfl

theorem cell23_8363925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_8363925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363925 prefixEnd_8363925 := by exact prefixLift 8363925
  have htrace : WordTrace (prefixWord ++ tailWord_8363925) baseStart_8363925 baseEnd_8363925 := by
    simpa [prefixWord, tailWord_8363925, baseEnd_8363925] using wordTrace_append hprefix tailTrace_8363925
  have hstable : (prefixWord ++ tailWord_8363925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363925).length < 2 ^ (prefixWord ++ tailWord_8363925).sum := by decide
  have hdescent : baseEnd_8363925 < baseStart_8363925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8363956 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_8363956 : Nat := 118140960795 + 8363956 * 2 ^ 59
def prefixEnd_8363956 : Nat := 4983230072969 + 3 ^ 40 * 8363956 * 2
def baseEnd_8363956 : Nat := 1431576533685527739128291

theorem tailTrace_8363956 : CollatzResearch.WordTrace tailWord_8363956 prefixEnd_8363956 1431576533685527739128291 := by
  unfold tailWord_8363956
  simp only [CollatzResearch.WordTrace]
  refine ⟨152529268443411668402599861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203372357924548891203466481 152529268443411668402599861)
  ·
    refine ⟨14299618916569843912743737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152529268443411668402599861 14299618916569843912743737)
    ·
      refine ⟨10724714187427382934557803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14299618916569843912743737 10724714187427382934557803)
      ·
        refine ⟨16087071281141074401836705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10724714187427382934557803 16087071281141074401836705)
        ·
          refine ⟨12065303460855805801377529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16087071281141074401836705 12065303460855805801377529)
          ·
            refine ⟨9048977595641854351033147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12065303460855805801377529 9048977595641854351033147)
            ·
              refine ⟨13573466393462781526549721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048977595641854351033147 13573466393462781526549721)
              ·
                refine ⟨10180099795097086144912291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13573466393462781526549721 10180099795097086144912291)
                ·
                  refine ⟨15270149692645629217368437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180099795097086144912291 15270149692645629217368437)
                  ·
                    refine ⟨1431576533685527739128291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15270149692645629217368437 1431576533685527739128291)
                    ·
                      rfl

theorem cell23_8363956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_8363956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8363956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8363956 prefixEnd_8363956 := by exact prefixLift 8363956
  have htrace : WordTrace (prefixWord ++ tailWord_8363956) baseStart_8363956 baseEnd_8363956 := by
    simpa [prefixWord, tailWord_8363956, baseEnd_8363956] using wordTrace_append hprefix tailTrace_8363956
  have hstable : (prefixWord ++ tailWord_8363956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8363956).length < 2 ^ (prefixWord ++ tailWord_8363956).sum := by decide
  have hdescent : baseEnd_8363956 < baseStart_8363956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8363956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364048 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_8364048 : Nat := 118140960795 + 8364048 * 2 ^ 59
def prefixEnd_8364048 : Nat := 4983230072969 + 3 ^ 40 * 8364048 * 2
def baseEnd_8364048 : Nat := 4294776841276796857434449

theorem tailTrace_8364048 : CollatzResearch.WordTrace tailWord_8364048 prefixEnd_8364048 4294776841276796857434449 := by
  unfold tailWord_8364048
  simp only [CollatzResearch.WordTrace]
  refine ⟨152530946201245018258774399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203374594934993357678365865 152530946201245018258774399)
  ·
    refine ⟨228796419301867527388161599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152530946201245018258774399 228796419301867527388161599)
    ·
      refine ⟨343194628952801291082242399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228796419301867527388161599 343194628952801291082242399)
      ·
        refine ⟨514791943429201936623363599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343194628952801291082242399 514791943429201936623363599)
        ·
          refine ⟨772187915143802904935045399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514791943429201936623363599 772187915143802904935045399)
          ·
            refine ⟨1158281872715704357402568099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772187915143802904935045399 1158281872715704357402568099)
            ·
              refine ⟨1737422809073556536103852149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158281872715704357402568099 1737422809073556536103852149)
              ·
                refine ⟨162883388350645925259736139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1737422809073556536103852149 162883388350645925259736139)
                ·
                  refine ⟨244325082525968887889604209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162883388350645925259736139 244325082525968887889604209)
                  ·
                    refine ⟨183243811894476665917203157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244325082525968887889604209 183243811894476665917203157)
                    ·
                      refine ⟨4294776841276796857434449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183243811894476665917203157 4294776841276796857434449)
                      ·
                        rfl

theorem cell23_8364048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_8364048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364048 prefixEnd_8364048 := by exact prefixLift 8364048
  have htrace : WordTrace (prefixWord ++ tailWord_8364048) baseStart_8364048 baseEnd_8364048 := by
    simpa [prefixWord, tailWord_8364048, baseEnd_8364048] using wordTrace_append hprefix tailTrace_8364048
  have hstable : (prefixWord ++ tailWord_8364048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364048).length < 2 ^ (prefixWord ++ tailWord_8364048).sum := by decide
  have hdescent : baseEnd_8364048 < baseStart_8364048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364085 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_8364085 : Nat := 118140960795 + 8364085 * 2 ^ 59
def prefixEnd_8364085 : Nat := 4983230072969 + 3 ^ 40 * 8364085 * 2
def baseEnd_8364085 : Nat := 1431598613353671070890593

theorem tailTrace_8364085 : CollatzResearch.WordTrace tailWord_8364085 prefixEnd_8364085 1431598613353671070890593 := by
  unfold tailWord_8364085
  simp only [CollatzResearch.WordTrace]
  refine ⟨305063241903355991836645709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203375494602237327891097139 305063241903355991836645709)
  ·
    refine ⟨114398715713758496938742141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305063241903355991836645709 114398715713758496938742141)
    ·
      refine ⟨42899518392659436352028303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114398715713758496938742141 42899518392659436352028303)
      ·
        refine ⟨64349277588989154528042455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42899518392659436352028303 64349277588989154528042455)
        ·
          refine ⟨96523916383483731792063683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64349277588989154528042455 96523916383483731792063683)
          ·
            refine ⟨144785874575225597688095525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96523916383483731792063683 144785874575225597688095525)
            ·
              refine ⟨27147351482854799566517911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144785874575225597688095525 27147351482854799566517911)
              ·
                refine ⟨40721027224282199349776867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27147351482854799566517911 40721027224282199349776867)
                ·
                  refine ⟨61081540836423299024665301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40721027224282199349776867 61081540836423299024665301)
                  ·
                    refine ⟨1431598613353671070890593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61081540836423299024665301 1431598613353671070890593)
                    ·
                      rfl

theorem cell23_8364085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_8364085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364085 prefixEnd_8364085 := by exact prefixLift 8364085
  have htrace : WordTrace (prefixWord ++ tailWord_8364085) baseStart_8364085 baseEnd_8364085 := by
    simpa [prefixWord, tailWord_8364085, baseEnd_8364085] using wordTrace_append hprefix tailTrace_8364085
  have hstable : (prefixWord ++ tailWord_8364085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364085).length < 2 ^ (prefixWord ++ tailWord_8364085).sum := by decide
  have hdescent : baseEnd_8364085 < baseStart_8364085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364109 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_8364109 : Nat := 118140960795 + 8364109 * 2 ^ 59
def prefixEnd_8364109 : Nat := 4983230072969 + 3 ^ 40 * 8364109 * 2
def baseEnd_8364109 : Nat := 4294808163596721118771669

theorem tailTrace_8364109 : CollatzResearch.WordTrace tailWord_8364109 prefixEnd_8364109 4294808163596721118771669 := by
  unfold tailWord_8364109
  simp only [CollatzResearch.WordTrace]
  refine ⟨305064117255269043935519381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203376078170179362623679587 305064117255269043935519381)
  ·
    refine ⟨14299880496340736434477471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305064117255269043935519381 14299880496340736434477471)
    ·
      refine ⟨21449820744511104651716207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14299880496340736434477471 21449820744511104651716207)
      ·
        refine ⟨32174731116766656977574311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21449820744511104651716207 32174731116766656977574311)
        ·
          refine ⟨48262096675149985466361467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32174731116766656977574311 48262096675149985466361467)
          ·
            refine ⟨72393145012724978199542201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48262096675149985466361467 72393145012724978199542201)
            ·
              refine ⟨54294858759543733649656651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72393145012724978199542201 54294858759543733649656651)
              ·
                refine ⟨81442288139315600474484977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54294858759543733649656651 81442288139315600474484977)
                ·
                  refine ⟨61081716104486700355863733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81442288139315600474484977 61081716104486700355863733)
                  ·
                    refine ⟨5726410884795628158362225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61081716104486700355863733 5726410884795628158362225)
                    ·
                      refine ⟨4294808163596721118771669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726410884795628158362225 4294808163596721118771669)
                      ·
                        rfl

theorem cell23_8364109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_8364109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364109 prefixEnd_8364109 := by exact prefixLift 8364109
  have htrace : WordTrace (prefixWord ++ tailWord_8364109) baseStart_8364109 baseEnd_8364109 := by
    simpa [prefixWord, tailWord_8364109, baseEnd_8364109] using wordTrace_append hprefix tailTrace_8364109
  have hstable : (prefixWord ++ tailWord_8364109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364109).length < 2 ^ (prefixWord ++ tailWord_8364109).sum := by decide
  have hdescent : baseEnd_8364109 < baseStart_8364109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364122 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2]
def baseStart_8364122 : Nat := 118140960795 + 8364122 * 2 ^ 59
def prefixEnd_8364122 : Nat := 4983230072969 + 3 ^ 40 * 8364122 * 2
def baseEnd_8364122 : Nat := 4294814838845229567909109

theorem tailTrace_8364122 : CollatzResearch.WordTrace tailWord_8364122 prefixEnd_8364122 4294814838845229567909109 := by
  unfold tailWord_8364122
  simp only [CollatzResearch.WordTrace]
  refine ⟨76266147851055486788935655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203376394269481298103828413 76266147851055486788935655)
  ·
    refine ⟨114399221776583230183403483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76266147851055486788935655 114399221776583230183403483)
    ·
      refine ⟨171598832664874845275105225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114399221776583230183403483 171598832664874845275105225)
      ·
        refine ⟨128699124498656133956328919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171598832664874845275105225 128699124498656133956328919)
        ·
          refine ⟨193048686747984200934493379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128699124498656133956328919 193048686747984200934493379)
          ·
            refine ⟨289573030121976301401740069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193048686747984200934493379 289573030121976301401740069)
            ·
              refine ⟨54294943147870556512826263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289573030121976301401740069 54294943147870556512826263)
              ·
                refine ⟨81442414721805834769239395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54294943147870556512826263 81442414721805834769239395)
                ·
                  refine ⟨122163622082708752153859093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81442414721805834769239395 122163622082708752153859093)
                  ·
                    refine ⟨5726419785126972757212145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122163622082708752153859093 5726419785126972757212145)
                    ·
                      refine ⟨4294814838845229567909109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726419785126972757212145 4294814838845229567909109)
                      ·
                        rfl

theorem cell23_8364122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_8364122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364122 prefixEnd_8364122 := by exact prefixLift 8364122
  have htrace : WordTrace (prefixWord ++ tailWord_8364122) baseStart_8364122 baseEnd_8364122 := by
    simpa [prefixWord, tailWord_8364122, baseEnd_8364122] using wordTrace_append hprefix tailTrace_8364122
  have hstable : (prefixWord ++ tailWord_8364122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364122).length < 2 ^ (prefixWord ++ tailWord_8364122).sum := by decide
  have hdescent : baseEnd_8364122 < baseStart_8364122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364132 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_8364132 : Nat := 118140960795 + 8364132 * 2 ^ 59
def prefixEnd_8364132 : Nat := 4983230072969 + 3 ^ 40 * 8364132 * 2
def baseEnd_8364132 : Nat := 1431606657883924842928021

theorem tailTrace_8364132 : CollatzResearch.WordTrace tailWord_8364132 prefixEnd_8364132 1431606657883924842928021 := by
  unfold tailWord_8364132
  simp only [CollatzResearch.WordTrace]
  refine ⟨152532478067092859431803325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203376637422790479242404433 152532478067092859431803325)
  ·
    refine ⟨57199679275159822286926247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152532478067092859431803325 57199679275159822286926247)
    ·
      refine ⟨85799518912739733430389371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57199679275159822286926247 85799518912739733430389371)
      ·
        refine ⟨128699278369109600145584057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85799518912739733430389371 128699278369109600145584057)
        ·
          refine ⟨96524458776832200109188043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128699278369109600145584057 96524458776832200109188043)
          ·
            refine ⟨144786688165248300163782065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96524458776832200109188043 144786688165248300163782065)
            ·
              refine ⟨108590016123936225122836549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144786688165248300163782065 108590016123936225122836549)
              ·
                refine ⟨20360628023238042210531853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108590016123936225122836549 20360628023238042210531853)
                ·
                  refine ⟨7635235508714265828949445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20360628023238042210531853 7635235508714265828949445)
                  ·
                    refine ⟨1431606657883924842928021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635235508714265828949445 1431606657883924842928021)
                    ·
                      rfl

theorem cell23_8364132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_8364132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364132 prefixEnd_8364132 := by exact prefixLift 8364132
  have htrace : WordTrace (prefixWord ++ tailWord_8364132) baseStart_8364132 baseEnd_8364132 := by
    simpa [prefixWord, tailWord_8364132, baseEnd_8364132] using wordTrace_append hprefix tailTrace_8364132
  have hstable : (prefixWord ++ tailWord_8364132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364132).length < 2 ^ (prefixWord ++ tailWord_8364132).sum := by decide
  have hdescent : baseEnd_8364132 < baseStart_8364132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364189 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_8364189 : Nat := 118140960795 + 8364189 * 2 ^ 59
def prefixEnd_8364189 : Nat := 4983230072969 + 3 ^ 40 * 8364189 * 2
def baseEnd_8364189 : Nat := 4294849242049080805771301

theorem tailTrace_8364189 : CollatzResearch.WordTrace tailWord_8364189 prefixEnd_8364189 4294849242049080805771301 := by
  unfold tailWord_8364189
  simp only [CollatzResearch.WordTrace]
  refine ⟨305067035094979217598431621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203378023396652811732287747 305067035094979217598431621)
  ·
    refine ⟨57200069080308603299705929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305067035094979217598431621 57200069080308603299705929)
    ·
      refine ⟨42900051810231452474779447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57200069080308603299705929 42900051810231452474779447)
      ·
        refine ⟨64350077715347178712169171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42900051810231452474779447 64350077715347178712169171)
        ·
          refine ⟨96525116573020768068253757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64350077715347178712169171 96525116573020768068253757)
          ·
            refine ⟨36196918714882788025595159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96525116573020768068253757 36196918714882788025595159)
            ·
              refine ⟨54295378072324182038392739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36196918714882788025595159 54295378072324182038392739)
              ·
                refine ⟨81443067108486273057589109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54295378072324182038392739 81443067108486273057589109)
                ·
                  refine ⟨7635287541420588099148979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81443067108486273057589109 7635287541420588099148979)
                  ·
                    refine ⟨11452931312130882148723469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7635287541420588099148979 11452931312130882148723469)
                    ·
                      refine ⟨4294849242049080805771301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11452931312130882148723469 4294849242049080805771301)
                      ·
                        rfl

theorem cell23_8364189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_8364189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364189 prefixEnd_8364189 := by exact prefixLift 8364189
  have htrace : WordTrace (prefixWord ++ tailWord_8364189) baseStart_8364189 baseEnd_8364189 := by
    simpa [prefixWord, tailWord_8364189, baseEnd_8364189] using wordTrace_append hprefix tailTrace_8364189
  have hstable : (prefixWord ++ tailWord_8364189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364189).length < 2 ^ (prefixWord ++ tailWord_8364189).sum := by decide
  have hdescent : baseEnd_8364189 < baseStart_8364189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364192 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 3, 5]
def baseStart_8364192 : Nat := 118140960795 + 8364192 * 2 ^ 59
def prefixEnd_8364192 : Nat := 4983230072969 + 3 ^ 40 * 8364192 * 2
def baseEnd_8364192 : Nat := 1431616927497014764677929

theorem tailTrace_8364192 : CollatzResearch.WordTrace tailWord_8364192 prefixEnd_8364192 1431616927497014764677929 := by
  unfold tailWord_8364192
  simp only [CollatzResearch.WordTrace]
  refine ⟨152533572256984174555395415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203378096342645566073860553 152533572256984174555395415)
  ·
    refine ⟨228800358385476261833093123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152533572256984174555395415 228800358385476261833093123)
    ·
      refine ⟨343200537578214392749639685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228800358385476261833093123 343200537578214392749639685)
      ·
        refine ⟨64350100795915198640557441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343200537578214392749639685 64350100795915198640557441)
        ·
          refine ⟨48262575596936398980418081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64350100795915198640557441 48262575596936398980418081)
          ·
            refine ⟨36196931697702299235313561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48262575596936398980418081 36196931697702299235313561)
            ·
              refine ⟨27147698773276724426485171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36196931697702299235313561 27147698773276724426485171)
              ·
                refine ⟨40721548159915086639727757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27147698773276724426485171 40721548159915086639727757)
                ·
                  refine ⟨15270580559968157489897909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40721548159915086639727757 15270580559968157489897909)
                  ·
                    refine ⟨1431616927497014764677929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15270580559968157489897909 1431616927497014764677929)
                    ·
                      rfl

theorem cell23_8364192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_8364192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364192 prefixEnd_8364192 := by exact prefixLift 8364192
  have htrace : WordTrace (prefixWord ++ tailWord_8364192) baseStart_8364192 baseEnd_8364192 := by
    simpa [prefixWord, tailWord_8364192, baseEnd_8364192] using wordTrace_append hprefix tailTrace_8364192
  have hstable : (prefixWord ++ tailWord_8364192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364192).length < 2 ^ (prefixWord ++ tailWord_8364192).sum := by decide
  have hdescent : baseEnd_8364192 < baseStart_8364192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364213 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 6]
def baseStart_8364213 : Nat := 118140960795 + 8364213 * 2 ^ 59
def prefixEnd_8364213 : Nat := 4983230072969 + 3 ^ 40 * 8364213 * 2
def baseEnd_8364213 : Nat := 477206840620532079096799

theorem tailTrace_8364213 : CollatzResearch.WordTrace tailWord_8364213 prefixEnd_8364213 477206840620532079096799 := by
  unfold tailWord_8364213
  simp only [CollatzResearch.WordTrace]
  refine ⟨305067910446892269697305293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203378606964594846464870195 305067910446892269697305293)
  ·
    refine ⟨114400466417584601136489485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305067910446892269697305293 114400466417584601136489485)
    ·
      refine ⟨42900174906594225426183557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114400466417584601136489485 42900174906594225426183557)
      ·
        refine ⟨8043782794986417267409417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42900174906594225426183557 8043782794986417267409417)
        ·
          refine ⟨6032837096239812950557063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8043782794986417267409417 6032837096239812950557063)
          ·
            refine ⟨9049255644359719425835595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032837096239812950557063 9049255644359719425835595)
            ·
              refine ⟨13573883466539579138753393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9049255644359719425835595 13573883466539579138753393)
              ·
                refine ⟨10180412599904684354065045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13573883466539579138753393 10180412599904684354065045)
                ·
                  refine ⟨477206840620532079096799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10180412599904684354065045 477206840620532079096799)
                  ·
                    rfl

theorem cell23_8364213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_8364213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364213 prefixEnd_8364213 := by exact prefixLift 8364213
  have htrace : WordTrace (prefixWord ++ tailWord_8364213) baseStart_8364213 baseEnd_8364213 := by
    simpa [prefixWord, tailWord_8364213, baseEnd_8364213] using wordTrace_append hprefix tailTrace_8364213
  have hstable : (prefixWord ++ tailWord_8364213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364213).length < 2 ^ (prefixWord ++ tailWord_8364213).sum := by decide
  have hdescent : baseEnd_8364213 < baseStart_8364213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364235 : List Nat := [1, 1, 1, 1, 3, 2, 4, 10]
def baseStart_8364235 : Nat := 118140960795 + 8364235 * 2 ^ 59
def prefixEnd_8364235 : Nat := 4983230072969 + 3 ^ 40 * 8364235 * 2
def baseEnd_8364235 : Nat := 159069365265155097251707

theorem tailTrace_8364235 : CollatzResearch.WordTrace tailWord_8364235 prefixEnd_8364235 159069365265155097251707 := by
  unfold tailWord_8364235
  simp only [CollatzResearch.WordTrace]
  refine ⟨305068712852812567454606159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203379141901875044969737439 305068712852812567454606159)
  ·
    refine ⟨457603069279218851181909239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305068712852812567454606159 457603069279218851181909239)
    ·
      refine ⟨686404603918828276772863859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457603069279218851181909239 686404603918828276772863859)
      ·
        refine ⟨1029606905878242415159295789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686404603918828276772863859 1029606905878242415159295789)
        ·
          refine ⟨386102589704340905684735921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1029606905878242415159295789 386102589704340905684735921)
          ·
            refine ⟨289576942278255679263551941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386102589704340905684735921 289576942278255679263551941)
            ·
              refine ⟨54295676677172939861915989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289576942278255679263551941 54295676677172939861915989)
              ·
                refine ⟨159069365265155097251707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54295676677172939861915989 159069365265155097251707)
                ·
                  rfl

theorem cell23_8364235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 10].length) (baseStart_8364235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364235 prefixEnd_8364235 := by exact prefixLift 8364235
  have htrace : WordTrace (prefixWord ++ tailWord_8364235) baseStart_8364235 baseEnd_8364235 := by
    simpa [prefixWord, tailWord_8364235, baseEnd_8364235] using wordTrace_append hprefix tailTrace_8364235
  have hstable : (prefixWord ++ tailWord_8364235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364235).length < 2 ^ (prefixWord ++ tailWord_8364235).sum := by decide
  have hdescent : baseEnd_8364235 < baseStart_8364235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364249 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 3]
def baseStart_8364249 : Nat := 118140960795 + 8364249 * 2 ^ 59
def prefixEnd_8364249 : Nat := 4983230072969 + 3 ^ 40 * 8364249 * 2
def baseEnd_8364249 : Nat := 4294880050888350571021025

theorem tailTrace_8364249 : CollatzResearch.WordTrace tailWord_8364249 prefixEnd_8364249 4294880050888350571021025 := by
  unfold tailWord_8364249
  simp only [CollatzResearch.WordTrace]
  refine ⟨305069223474761847845615801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203379482316507898563743867 305069223474761847845615801)
  ·
    refine ⟨228801917606071385884211851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305069223474761847845615801 228801917606071385884211851)
    ·
      refine ⟨343202876409107078826317777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228801917606071385884211851 343202876409107078826317777)
      ·
        refine ⟨257402157306830309119738333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343202876409107078826317777 257402157306830309119738333)
        ·
          refine ⟨96525808990061365919901875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257402157306830309119738333 96525808990061365919901875)
          ·
            refine ⟨144788713485092048879852813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96525808990061365919901875 144788713485092048879852813)
            ·
              refine ⟨54295767556909518329944805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144788713485092048879852813 54295767556909518329944805)
              ·
                refine ⟨10180456416920534686864651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54295767556909518329944805 10180456416920534686864651)
                ·
                  refine ⟨15270684625380802030296977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180456416920534686864651 15270684625380802030296977)
                  ·
                    refine ⟨11453013469035601522722733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15270684625380802030296977 11453013469035601522722733)
                    ·
                      refine ⟨4294880050888350571021025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11453013469035601522722733 4294880050888350571021025)
                      ·
                        rfl

theorem cell23_8364249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_8364249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364249 prefixEnd_8364249 := by exact prefixLift 8364249
  have htrace : WordTrace (prefixWord ++ tailWord_8364249) baseStart_8364249 baseEnd_8364249 := by
    simpa [prefixWord, tailWord_8364249, baseEnd_8364249] using wordTrace_append hprefix tailTrace_8364249
  have hstable : (prefixWord ++ tailWord_8364249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364249).length < 2 ^ (prefixWord ++ tailWord_8364249).sum := by decide
  have hdescent : baseEnd_8364249 < baseStart_8364249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364269 : List Nat := [1, 5, 1, 2, 3, 2, 9]
def baseStart_8364269 : Nat := 118140960795 + 8364269 * 2 ^ 59
def prefixEnd_8364269 : Nat := 4983230072969 + 3 ^ 40 * 8364269 * 2
def baseEnd_8364269 : Nat := 53023337290141240651493

theorem tailTrace_8364269 : CollatzResearch.WordTrace tailWord_8364269 prefixEnd_8364269 53023337290141240651493 := by
  unfold tailWord_8364269
  simp only [CollatzResearch.WordTrace]
  refine ⟨305069952934689391261343861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203379968623126260840895907 305069952934689391261343861)
  ·
    refine ⟨28600308087627130430750987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305069952934689391261343861 28600308087627130430750987)
    ·
      refine ⟨42900462131440695646126481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28600308087627130430750987 42900462131440695646126481)
      ·
        refine ⟨32175346598580521734594861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42900462131440695646126481 32175346598580521734594861)
        ·
          refine ⟨12065754974467695650473073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32175346598580521734594861 12065754974467695650473073)
          ·
            refine ⟨9049316230850771737854805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12065754974467695650473073 9049316230850771737854805)
            ·
              refine ⟨53023337290141240651493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9049316230850771737854805 53023337290141240651493)
              ·
                rfl

theorem cell23_8364269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 9].length) (baseStart_8364269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364269 prefixEnd_8364269 := by exact prefixLift 8364269
  have htrace : WordTrace (prefixWord ++ tailWord_8364269) baseStart_8364269 baseEnd_8364269 := by
    simpa [prefixWord, tailWord_8364269, baseEnd_8364269] using wordTrace_append hprefix tailTrace_8364269
  have hstable : (prefixWord ++ tailWord_8364269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364269).length < 2 ^ (prefixWord ++ tailWord_8364269).sum := by decide
  have hdescent : baseEnd_8364269 < baseStart_8364269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364290 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_8364290 : Nat := 118140960795 + 8364290 * 2 ^ 59
def prefixEnd_8364290 : Nat := 4983230072969 + 3 ^ 40 * 8364290 * 2
def baseEnd_8364290 : Nat := 1431633701198394970202779

theorem tailTrace_8364290 : CollatzResearch.WordTrace tailWord_8364290 prefixEnd_8364290 1431633701198394970202779 := by
  unfold tailWord_8364290
  simp only [CollatzResearch.WordTrace]
  refine ⟨76267679716903327961964581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203380479245075541231905549 76267679716903327961964581)
  ·
    refine ⟨14300189946919373992868359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76267679716903327961964581 14300189946919373992868359)
    ·
      refine ⟨21450284920379060989302539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14300189946919373992868359 21450284920379060989302539)
      ·
        refine ⟨32175427380568591483953809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21450284920379060989302539 32175427380568591483953809)
        ·
          refine ⟨24131570535426443612965357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32175427380568591483953809 24131570535426443612965357)
          ·
            refine ⟨9049338950784916354862009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24131570535426443612965357 9049338950784916354862009)
            ·
              refine ⟨6787004213088687266146507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9049338950784916354862009 6787004213088687266146507)
              ·
                refine ⟨10180506319633030899219761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787004213088687266146507 10180506319633030899219761)
                ·
                  refine ⟨7635379739724773174414821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10180506319633030899219761 7635379739724773174414821)
                  ·
                    refine ⟨1431633701198394970202779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635379739724773174414821 1431633701198394970202779)
                    ·
                      rfl

theorem cell23_8364290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_8364290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364290 prefixEnd_8364290 := by exact prefixLift 8364290
  have htrace : WordTrace (prefixWord ++ tailWord_8364290) baseStart_8364290 baseEnd_8364290 := by
    simpa [prefixWord, tailWord_8364290, baseEnd_8364290] using wordTrace_append hprefix tailTrace_8364290
  have hstable : (prefixWord ++ tailWord_8364290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364290).length < 2 ^ (prefixWord ++ tailWord_8364290).sum := by decide
  have hdescent : baseEnd_8364290 < baseStart_8364290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364323 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 1, 3, 2]
def baseStart_8364323 : Nat := 118140960795 + 8364323 * 2 ^ 59
def prefixEnd_8364323 : Nat := 4983230072969 + 3 ^ 40 * 8364323 * 2
def baseEnd_8364323 : Nat := 4294918048456783281495685

theorem tailTrace_8364323 : CollatzResearch.WordTrace tailWord_8364323 prefixEnd_8364323 4294918048456783281495685 := by
  unfold tailWord_8364323
  simp only [CollatzResearch.WordTrace]
  refine ⟨305071922476493758483809623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203381281650995838989206415 305071922476493758483809623)
  ·
    refine ⟨457607883714740637725714435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305071922476493758483809623 457607883714740637725714435)
    ·
      refine ⟨686411825572110956588571653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457607883714740637725714435 686411825572110956588571653)
      ·
        refine ⟨128702217294770804360357185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 686411825572110956588571653 128702217294770804360357185)
        ·
          refine ⟨96526662971078103270267889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128702217294770804360357185 96526662971078103270267889)
          ·
            refine ⟨72394997228308577452700917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96526662971078103270267889 72394997228308577452700917)
            ·
              refine ⟨6787030990153929136190711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72394997228308577452700917 6787030990153929136190711)
              ·
                refine ⟨10180546485230893704286067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787030990153929136190711 10180546485230893704286067)
                ·
                  refine ⟨15270819727846340556429101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180546485230893704286067 15270819727846340556429101)
                  ·
                    refine ⟨5726557397942377708660913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15270819727846340556429101 5726557397942377708660913)
                    ·
                      refine ⟨4294918048456783281495685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726557397942377708660913 4294918048456783281495685)
                      ·
                        rfl

theorem cell23_8364323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_8364323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364323 prefixEnd_8364323 := by exact prefixLift 8364323
  have htrace : WordTrace (prefixWord ++ tailWord_8364323) baseStart_8364323 baseEnd_8364323 := by
    simpa [prefixWord, tailWord_8364323, baseEnd_8364323] using wordTrace_append hprefix tailTrace_8364323
  have hstable : (prefixWord ++ tailWord_8364323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364323).length < 2 ^ (prefixWord ++ tailWord_8364323).sum := by decide
  have hdescent : baseEnd_8364323 < baseStart_8364323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364330 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_8364330 : Nat := 118140960795 + 8364330 * 2 ^ 59
def prefixEnd_8364330 : Nat := 4983230072969 + 3 ^ 40 * 8364330 * 2
def baseEnd_8364330 : Nat := 4294921642821364754108153

theorem tailTrace_8364330 : CollatzResearch.WordTrace tailWord_8364330 prefixEnd_8364330 4294921642821364754108153 := by
  unfold tailWord_8364330
  simp only [CollatzResearch.WordTrace]
  refine ⟨76268044446867099669828611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203381451858312265786209629 76268044446867099669828611)
  ·
    refine ⟨114402066670300649504742917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76268044446867099669828611 114402066670300649504742917)
    ·
      refine ⟨21450387500681371782139297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114402066670300649504742917 21450387500681371782139297)
      ·
        refine ⟨16087790625511028836604473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21450387500681371782139297 16087790625511028836604473)
        ·
          refine ⟨12065842969133271627453355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16087790625511028836604473 12065842969133271627453355)
          ·
            refine ⟨18098764453699907441180033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12065842969133271627453355 18098764453699907441180033)
            ·
              refine ⟨13574073340274930580885025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18098764453699907441180033 13574073340274930580885025)
              ·
                refine ⟨10180555005206197935663769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13574073340274930580885025 10180555005206197935663769)
                ·
                  refine ⟨7635416253904648451747827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10180555005206197935663769 7635416253904648451747827)
                  ·
                    refine ⟨11453124380856972677621741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7635416253904648451747827 11453124380856972677621741)
                    ·
                      refine ⟨4294921642821364754108153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11453124380856972677621741 4294921642821364754108153)
                      ·
                        rfl

theorem cell23_8364330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_8364330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364330 prefixEnd_8364330 := by exact prefixLift 8364330
  have htrace : WordTrace (prefixWord ++ tailWord_8364330) baseStart_8364330 baseEnd_8364330 := by
    simpa [prefixWord, tailWord_8364330, baseEnd_8364330] using wordTrace_append hprefix tailTrace_8364330
  have hstable : (prefixWord ++ tailWord_8364330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364330).length < 2 ^ (prefixWord ++ tailWord_8364330).sum := by decide
  have hdescent : baseEnd_8364330 < baseStart_8364330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364386 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_8364386 : Nat := 118140960795 + 8364386 * 2 ^ 59
def prefixEnd_8364386 : Nat := 4983230072969 + 3 ^ 40 * 8364386 * 2
def baseEnd_8364386 : Nat := 4294950397738016535007895

theorem tailTrace_8364386 : CollatzResearch.WordTrace tailWord_8364386 prefixEnd_8364386 4294950397738016535007895 := by
  unfold tailWord_8364386
  simp only [CollatzResearch.WordTrace]
  refine ⟨76268555068816380060838253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203382813516843680162235341 76268555068816380060838253)
  ·
    refine ⟨28600708150806142522814345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76268555068816380060838253 28600708150806142522814345)
    ·
      refine ⟨21450531113104606892110759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28600708150806142522814345 21450531113104606892110759)
      ·
        refine ⟨32175796669656910338166139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21450531113104606892110759 32175796669656910338166139)
        ·
          refine ⟨48263695004485365507249209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32175796669656910338166139 48263695004485365507249209)
          ·
            refine ⟨36197771253364024130436907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48263695004485365507249209 36197771253364024130436907)
            ·
              refine ⟨54296656880046036195655361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36197771253364024130436907 54296656880046036195655361)
              ·
                refine ⟨40722492660034527146741521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54296656880046036195655361 40722492660034527146741521)
                ·
                  refine ⟨30541869495025895360056141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40722492660034527146741521 30541869495025895360056141)
                  ·
                    refine ⟨11453201060634710760021053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30541869495025895360056141 11453201060634710760021053)
                    ·
                      refine ⟨4294950397738016535007895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11453201060634710760021053 4294950397738016535007895)
                      ·
                        rfl

theorem cell23_8364386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_8364386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364386 prefixEnd_8364386 := by exact prefixLift 8364386
  have htrace : WordTrace (prefixWord ++ tailWord_8364386) baseStart_8364386 baseEnd_8364386 := by
    simpa [prefixWord, tailWord_8364386, baseEnd_8364386] using wordTrace_append hprefix tailTrace_8364386
  have hstable : (prefixWord ++ tailWord_8364386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364386).length < 2 ^ (prefixWord ++ tailWord_8364386).sum := by decide
  have hdescent : baseEnd_8364386 < baseStart_8364386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364516 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_8364516 : Nat := 118140960795 + 8364516 * 2 ^ 59
def prefixEnd_8364516 : Nat := 4983230072969 + 3 ^ 40 * 8364516 * 2
def baseEnd_8364516 : Nat := 4295017150223101026382297

theorem tailTrace_8364516 : CollatzResearch.WordTrace tailWord_8364516 prefixEnd_8364516 4295017150223101026382297 := by
  unfold tailWord_8364516
  simp only [CollatzResearch.WordTrace]
  refine ⟨152539480882397276222792701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203385974509863034963723601 152539480882397276222792701)
  ·
    refine ⟨57202305330898978583547263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152539480882397276222792701 57202305330898978583547263)
    ·
      refine ⟨85803457996348467875320895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57202305330898978583547263 85803457996348467875320895)
      ·
        refine ⟨128705186994522701812981343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85803457996348467875320895 128705186994522701812981343)
        ·
          refine ⟨193057780491784052719472015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128705186994522701812981343 193057780491784052719472015)
          ·
            refine ⟨289586670737676079079208023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193057780491784052719472015 289586670737676079079208023)
            ·
              refine ⟨434380006106514118618812035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289586670737676079079208023 434380006106514118618812035)
              ·
                refine ⟨651570009159771177928218053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434380006106514118618812035 651570009159771177928218053)
                ·
                  refine ⟨122169376717457095861540885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651570009159771177928218053 122169376717457095861540885)
                  ·
                    refine ⟨5726689533630801368509729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122169376717457095861540885 5726689533630801368509729)
                    ·
                      refine ⟨4295017150223101026382297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726689533630801368509729 4295017150223101026382297)
                      ·
                        rfl

theorem cell23_8364516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_8364516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364516 prefixEnd_8364516 := by exact prefixLift 8364516
  have htrace : WordTrace (prefixWord ++ tailWord_8364516) baseStart_8364516 baseEnd_8364516 := by
    simpa [prefixWord, tailWord_8364516, baseEnd_8364516] using wordTrace_append hprefix tailTrace_8364516
  have hstable : (prefixWord ++ tailWord_8364516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364516).length < 2 ^ (prefixWord ++ tailWord_8364516).sum := by decide
  have hdescent : baseEnd_8364516 < baseStart_8364516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364526 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_8364526 : Nat := 118140960795 + 8364526 * 2 ^ 59
def prefixEnd_8364526 : Nat := 4983230072969 + 3 ^ 40 * 8364526 * 2
def baseEnd_8364526 : Nat := 1431674095009881995752417

theorem tailTrace_8364526 : CollatzResearch.WordTrace tailWord_8364526 prefixEnd_8364526 1431674095009881995752417 := by
  unfold tailWord_8364526
  simp only [CollatzResearch.WordTrace]
  refine ⟨38134915811844790519181179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203386217663172216102299621 38134915811844790519181179)
  ·
    refine ⟨57202373717767185778771769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38134915811844790519181179 57202373717767185778771769)
    ·
      refine ⟨42901780288325389334078827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57202373717767185778771769 42901780288325389334078827)
      ·
        refine ⟨64352670432488084001118241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42901780288325389334078827 64352670432488084001118241)
        ·
          refine ⟨48264502824366063000838681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64352670432488084001118241 48264502824366063000838681)
          ·
            refine ⟨36198377118274547250629011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48264502824366063000838681 36198377118274547250629011)
            ·
              refine ⟨54297565677411820875943517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36198377118274547250629011 54297565677411820875943517)
              ·
                refine ⟨20361587129029432828478819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54297565677411820875943517 20361587129029432828478819)
                ·
                  refine ⟨30542380693544149242718229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20361587129029432828478819 30542380693544149242718229)
                  ·
                    refine ⟨1431674095009881995752417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30542380693544149242718229 1431674095009881995752417)
                    ·
                      rfl

theorem cell23_8364526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_8364526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364526 prefixEnd_8364526 := by exact prefixLift 8364526
  have htrace : WordTrace (prefixWord ++ tailWord_8364526) baseStart_8364526 baseEnd_8364526 := by
    simpa [prefixWord, tailWord_8364526, baseEnd_8364526] using wordTrace_append hprefix tailTrace_8364526
  have hstable : (prefixWord ++ tailWord_8364526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364526).length < 2 ^ (prefixWord ++ tailWord_8364526).sum := by decide
  have hdescent : baseEnd_8364526 < baseStart_8364526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364536 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_8364536 : Nat := 118140960795 + 8364536 * 2 ^ 59
def prefixEnd_8364536 : Nat := 4983230072969 + 3 ^ 40 * 8364536 * 2
def baseEnd_8364536 : Nat := 4295027419836190948132205

theorem tailTrace_8364536 : CollatzResearch.WordTrace tailWord_8364536 prefixEnd_8364536 4295027419836190948132205 := by
  unfold tailWord_8364536
  simp only [CollatzResearch.WordTrace]
  refine ⟨152539845612361047930656731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203386460816481397240875641 152539845612361047930656731)
  ·
    refine ⟨228809768418541571895985097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152539845612361047930656731 228809768418541571895985097)
    ·
      refine ⟨171607326313906178921988823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228809768418541571895985097 171607326313906178921988823)
      ·
        refine ⟨257410989470859268382983235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171607326313906178921988823 257410989470859268382983235)
        ·
          refine ⟨386116484206288902574474853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257410989470859268382983235 386116484206288902574474853)
          ·
            refine ⟨72396840788679169232714035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386116484206288902574474853 72396840788679169232714035)
            ·
              refine ⟨108595261183018753849071053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72396840788679169232714035 108595261183018753849071053)
              ·
                refine ⟨40723222943632032693401645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108595261183018753849071053 40723222943632032693401645)
                ·
                  refine ⟨15271208603862012260025617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40723222943632032693401645 15271208603862012260025617)
                  ·
                    refine ⟨11453406452896509195019213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15271208603862012260025617 11453406452896509195019213)
                    ·
                      refine ⟨4295027419836190948132205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11453406452896509195019213 4295027419836190948132205)
                      ·
                        rfl

theorem cell23_8364536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_8364536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364536 prefixEnd_8364536 := by exact prefixLift 8364536
  have htrace : WordTrace (prefixWord ++ tailWord_8364536) baseStart_8364536 baseEnd_8364536 := by
    simpa [prefixWord, tailWord_8364536, baseEnd_8364536] using wordTrace_append hprefix tailTrace_8364536
  have hstable : (prefixWord ++ tailWord_8364536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364536).length < 2 ^ (prefixWord ++ tailWord_8364536).sum := by decide
  have hdescent : baseEnd_8364536 < baseStart_8364536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364590 : List Nat := [4, 1, 3, 1, 3, 2, 2, 7]
def baseStart_8364590 : Nat := 118140960795 + 8364590 * 2 ^ 59
def prefixEnd_8364590 : Nat := 4983230072969 + 3 ^ 40 * 8364590 * 2
def baseEnd_8364590 : Nat := 159076116584871619883591

theorem tailTrace_8364590 : CollatzResearch.WordTrace tailWord_8364590 prefixEnd_8364590 159076116584871619883591 := by
  unfold tailWord_8364590
  simp only [CollatzResearch.WordTrace]
  refine ⟨38135207595815807885472403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203387773844350975389186149 38135207595815807885472403)
  ·
    refine ⟨57202811393723711828208605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38135207595815807885472403 57202811393723711828208605)
    ·
      refine ⟨21451054272646391935578227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57202811393723711828208605 21451054272646391935578227)
      ·
        refine ⟨32176581408969587903367341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21451054272646391935578227 32176581408969587903367341)
        ·
          refine ⟨12066218028363595463762753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32176581408969587903367341 12066218028363595463762753)
          ·
            refine ⟨9049663521272696597822065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12066218028363595463762753 9049663521272696597822065)
            ·
              refine ⟨6787247640954522448366549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9049663521272696597822065 6787247640954522448366549)
              ·
                refine ⟨159076116584871619883591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6787247640954522448366549 159076116584871619883591)
                ·
                  rfl

theorem cell23_8364590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_8364590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364590 prefixEnd_8364590 := by exact prefixLift 8364590
  have htrace : WordTrace (prefixWord ++ tailWord_8364590) baseStart_8364590 baseEnd_8364590 := by
    simpa [prefixWord, tailWord_8364590, baseEnd_8364590] using wordTrace_append hprefix tailTrace_8364590
  have hstable : (prefixWord ++ tailWord_8364590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364590).length < 2 ^ (prefixWord ++ tailWord_8364590).sum := by decide
  have hdescent : baseEnd_8364590 < baseStart_8364590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364593 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 3, 3, 2]
def baseStart_8364593 : Nat := 118140960795 + 8364593 * 2 ^ 59
def prefixEnd_8364593 : Nat := 4983230072969 + 3 ^ 40 * 8364593 * 2
def baseEnd_8364593 : Nat := 4295056688233497225119443

theorem tailTrace_8364593 : CollatzResearch.WordTrace tailWord_8364593 prefixEnd_8364593 4295056688233497225119443 := by
  unfold tailWord_8364593
  simp only [CollatzResearch.WordTrace]
  refine ⟨305081770185515594596138433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203387846790343729730758955 305081770185515594596138433)
  ·
    refine ⟨228811327639136695947103825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305081770185515594596138433 228811327639136695947103825)
    ·
      refine ⟨171608495729352521960327869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228811327639136695947103825 171608495729352521960327869)
      ·
        refine ⟨64353185898507195735122951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171608495729352521960327869 64353185898507195735122951)
        ·
          refine ⟨96529778847760793602684427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64353185898507195735122951 96529778847760793602684427)
          ·
            refine ⟨144794668271641190404026641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96529778847760793602684427 144794668271641190404026641)
            ·
              refine ⟨108596001203730892803019981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144794668271641190404026641 108596001203730892803019981)
              ·
                refine ⟨40723500451399084801132493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108596001203730892803019981 40723500451399084801132493)
                ·
                  refine ⟨15271312669274656800424685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40723500451399084801132493 15271312669274656800424685)
                  ·
                    refine ⟨5726742250977996300159257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15271312669274656800424685 5726742250977996300159257)
                    ·
                      refine ⟨4295056688233497225119443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726742250977996300159257 4295056688233497225119443)
                      ·
                        rfl

theorem cell23_8364593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_8364593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364593 prefixEnd_8364593 := by exact prefixLift 8364593
  have htrace : WordTrace (prefixWord ++ tailWord_8364593) baseStart_8364593 baseEnd_8364593 := by
    simpa [prefixWord, tailWord_8364593, baseEnd_8364593] using wordTrace_append hprefix tailTrace_8364593
  have hstable : (prefixWord ++ tailWord_8364593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364593).length < 2 ^ (prefixWord ++ tailWord_8364593).sum := by decide
  have hdescent : baseEnd_8364593 < baseStart_8364593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364626 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_8364626 : Nat := 118140960795 + 8364626 * 2 ^ 59
def prefixEnd_8364626 : Nat := 4983230072969 + 3 ^ 40 * 8364626 * 2
def baseEnd_8364626 : Nat := 4295073633095095596006791

theorem tailTrace_8364626 : CollatzResearch.WordTrace tailWord_8364626 prefixEnd_8364626 4295073633095095596006791 := by
  unfold tailWord_8364626
  simp only [CollatzResearch.WordTrace]
  refine ⟨76270743448599010308022433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203388649196264027488059821 76270743448599010308022433)
  ·
    refine ⟨57203057586449257731016825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76270743448599010308022433 57203057586449257731016825)
    ·
      refine ⟨42902293189836943298262619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57203057586449257731016825 42902293189836943298262619)
      ·
        refine ⟨64353439784755414947393929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42902293189836943298262619 64353439784755414947393929)
        ·
          refine ⟨48265079838566561210545447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64353439784755414947393929 48265079838566561210545447)
          ·
            refine ⟨72397619757849841815818171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48265079838566561210545447 72397619757849841815818171)
            ·
              refine ⟨108596429636774762723727257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72397619757849841815818171 108596429636774762723727257)
              ·
                refine ⟨81447322227581072042795443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108596429636774762723727257 81447322227581072042795443)
                ·
                  refine ⟨122170983341371608064193165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81447322227581072042795443 122170983341371608064193165)
                  ·
                    refine ⟨45814118753014353024072437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122170983341371608064193165 45814118753014353024072437)
                    ·
                      refine ⟨4295073633095095596006791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45814118753014353024072437 4295073633095095596006791)
                      ·
                        rfl

theorem cell23_8364626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_8364626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364626 prefixEnd_8364626 := by exact prefixLift 8364626
  have htrace : WordTrace (prefixWord ++ tailWord_8364626) baseStart_8364626 baseEnd_8364626 := by
    simpa [prefixWord, tailWord_8364626, baseEnd_8364626] using wordTrace_append hprefix tailTrace_8364626
  have hstable : (prefixWord ++ tailWord_8364626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364626).length < 2 ^ (prefixWord ++ tailWord_8364626).sum := by decide
  have hdescent : baseEnd_8364626 < baseStart_8364626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364638 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_8364638 : Nat := 118140960795 + 8364638 * 2 ^ 59
def prefixEnd_8364638 : Nat := 4983230072969 + 3 ^ 40 * 8364638 * 2
def baseEnd_8364638 : Nat := 4295079794862949549056737

theorem tailTrace_8364638 : CollatzResearch.WordTrace tailWord_8364638 prefixEnd_8364638 4295079794862949549056737 := by
  unfold tailWord_8364638
  simp only [CollatzResearch.WordTrace]
  refine ⟨38135426433794070910190821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203388940980235044854351045 38135426433794070910190821)
  ·
    refine ⟨7150392456336388295660779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38135426433794070910190821 7150392456336388295660779)
    ·
      refine ⟨10725588684504582443491169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7150392456336388295660779 10725588684504582443491169)
      ·
        refine ⟨8044191513378436832618377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10725588684504582443491169 8044191513378436832618377)
        ·
          refine ⟨6033143635033827624463783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8044191513378436832618377 6033143635033827624463783)
          ·
            refine ⟨9049715452550741436695675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6033143635033827624463783 9049715452550741436695675)
            ·
              refine ⟨13574573178826112155043513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9049715452550741436695675 13574573178826112155043513)
              ·
                refine ⟨10180929884119584116282635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13574573178826112155043513 10180929884119584116282635)
                ·
                  refine ⟨15271394826179376174423953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180929884119584116282635 15271394826179376174423953)
                  ·
                    refine ⟨11453546119634532130817965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15271394826179376174423953 11453546119634532130817965)
                    ·
                      refine ⟨4295079794862949549056737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11453546119634532130817965 4295079794862949549056737)
                      ·
                        rfl

theorem cell23_8364638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_8364638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364638 prefixEnd_8364638 := by exact prefixLift 8364638
  have htrace : WordTrace (prefixWord ++ tailWord_8364638) baseStart_8364638 baseEnd_8364638 := by
    simpa [prefixWord, tailWord_8364638, baseEnd_8364638] using wordTrace_append hprefix tailTrace_8364638
  have hstable : (prefixWord ++ tailWord_8364638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364638).length < 2 ^ (prefixWord ++ tailWord_8364638).sum := by decide
  have hdescent : baseEnd_8364638 < baseStart_8364638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364673 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_8364673 : Nat := 118140960795 + 8364673 * 2 ^ 59
def prefixEnd_8364673 : Nat := 4983230072969 + 3 ^ 40 * 8364673 * 2
def baseEnd_8364673 : Nat := 4295097766685856912119075

theorem tailTrace_8364673 : CollatzResearch.WordTrace tailWord_8364673 prefixEnd_8364673 4295097766685856912119075 := by
  unfold tailWord_8364673
  simp only [CollatzResearch.WordTrace]
  refine ⟨305084688025225768259050673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203389792016817178839367115 305084688025225768259050673)
  ·
    refine ⟨228813516018919326194288005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305084688025225768259050673 228813516018919326194288005)
    ·
      refine ⟨42902534253547373661429001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228813516018919326194288005 42902534253547373661429001)
      ·
        refine ⟨32176900690160530246071751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42902534253547373661429001 32176900690160530246071751)
        ·
          refine ⟨48265351035240795369107627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32176900690160530246071751 48265351035240795369107627)
          ·
            refine ⟨72398026552861193053661441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48265351035240795369107627 72398026552861193053661441)
            ·
              refine ⟨54298519914645894790246081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72398026552861193053661441 54298519914645894790246081)
              ·
                refine ⟨40723889935984421092684561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54298519914645894790246081 40723889935984421092684561)
                ·
                  refine ⟨30542917451988315819513421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40723889935984421092684561 30542917451988315819513421)
                  ·
                    refine ⟨11453594044495618432317533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30542917451988315819513421 11453594044495618432317533)
                    ·
                      refine ⟨4295097766685856912119075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11453594044495618432317533 4295097766685856912119075)
                      ·
                        rfl

theorem cell23_8364673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_8364673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364673 prefixEnd_8364673 := by exact prefixLift 8364673
  have htrace : WordTrace (prefixWord ++ tailWord_8364673) baseStart_8364673 baseEnd_8364673 := by
    simpa [prefixWord, tailWord_8364673, baseEnd_8364673] using wordTrace_append hprefix tailTrace_8364673
  have hstable : (prefixWord ++ tailWord_8364673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364673).length < 2 ^ (prefixWord ++ tailWord_8364673).sum := by decide
  have hdescent : baseEnd_8364673 < baseStart_8364673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364690 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_8364690 : Nat := 118140960795 + 8364690 * 2 ^ 59
def prefixEnd_8364690 : Nat := 4983230072969 + 3 ^ 40 * 8364690 * 2
def baseEnd_8364690 : Nat := 4295106495856983345606497

theorem tailTrace_8364690 : CollatzResearch.WordTrace tailWord_8364690 prefixEnd_8364690 4295106495856983345606497 := by
  unfold tailWord_8364690
  simp only [CollatzResearch.WordTrace]
  refine ⟨76271327016541045040604881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203390205377442786774946349 76271327016541045040604881)
  ·
    refine ⟨57203495262405783780453661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76271327016541045040604881 57203495262405783780453661)
    ·
      refine ⟨21451310723402168917670123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57203495262405783780453661 21451310723402168917670123)
      ·
        refine ⟨32176966085103253376505185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21451310723402168917670123 32176966085103253376505185)
        ·
          refine ⟨24132724563827440032378889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32176966085103253376505185 24132724563827440032378889)
          ·
            refine ⟨18099543422870580024284167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24132724563827440032378889 18099543422870580024284167)
            ·
              refine ⟨27149315134305870036426251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18099543422870580024284167 27149315134305870036426251)
              ·
                refine ⟨40723972701458805054639377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27149315134305870036426251 40723972701458805054639377)
                ·
                  refine ⟨30542979526094103790979533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40723972701458805054639377 30542979526094103790979533)
                  ·
                    refine ⟨11453617322285288921617325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30542979526094103790979533 11453617322285288921617325)
                    ·
                      refine ⟨4295106495856983345606497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11453617322285288921617325 4295106495856983345606497)
                      ·
                        rfl

theorem cell23_8364690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_8364690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364690 prefixEnd_8364690 := by exact prefixLift 8364690
  have htrace : WordTrace (prefixWord ++ tailWord_8364690) baseStart_8364690 baseEnd_8364690 := by
    simpa [prefixWord, tailWord_8364690, baseEnd_8364690] using wordTrace_append hprefix tailTrace_8364690
  have hstable : (prefixWord ++ tailWord_8364690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364690).length < 2 ^ (prefixWord ++ tailWord_8364690).sum := by decide
  have hdescent : baseEnd_8364690 < baseStart_8364690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364713 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 4, 4, 2]
def baseStart_8364713 : Nat := 118140960795 + 8364713 * 2 ^ 59
def prefixEnd_8364713 : Nat := 4983230072969 + 3 ^ 40 * 8364713 * 2
def baseEnd_8364713 : Nat := 4295118305912036755618891

theorem tailTrace_8364713 : CollatzResearch.WordTrace tailWord_8364713 prefixEnd_8364713 4295118305912036755618891 := by
  unfold tailWord_8364713
  simp only [CollatzResearch.WordTrace]
  refine ⟨305086146945080855090506793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203390764630053903393671195 305086146945080855090506793)
  ·
    refine ⟨228814610208810641317880095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305086146945080855090506793 228814610208810641317880095)
    ·
      refine ⟨343221915313215961976820143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228814610208810641317880095 343221915313215961976820143)
      ·
        refine ⟨514832872969823942965230215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343221915313215961976820143 514832872969823942965230215)
        ·
          refine ⟨772249309454735914447845323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514832872969823942965230215 772249309454735914447845323)
          ·
            refine ⟨1158373964182103871671767985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772249309454735914447845323 1158373964182103871671767985)
            ·
              refine ⟨868780473136577903753825989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158373964182103871671767985 868780473136577903753825989)
              ·
                refine ⟨162896338713108356953842373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 868780473136577903753825989 162896338713108356953842373)
                ·
                  refine ⟨30543063508707816928845445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162896338713108356953842373 30543063508707816928845445)
                  ·
                    refine ⟨5726824407882715674158521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30543063508707816928845445 5726824407882715674158521)
                    ·
                      refine ⟨4295118305912036755618891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726824407882715674158521 4295118305912036755618891)
                      ·
                        rfl

theorem cell23_8364713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 4, 2].length) (baseStart_8364713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364713 prefixEnd_8364713 := by exact prefixLift 8364713
  have htrace : WordTrace (prefixWord ++ tailWord_8364713) baseStart_8364713 baseEnd_8364713 := by
    simpa [prefixWord, tailWord_8364713, baseEnd_8364713] using wordTrace_append hprefix tailTrace_8364713
  have hstable : (prefixWord ++ tailWord_8364713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364713).length < 2 ^ (prefixWord ++ tailWord_8364713).sum := by decide
  have hdescent : baseEnd_8364713 < baseStart_8364713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364714 : List Nat := [3, 1, 5, 2, 1, 1, 2, 3, 5]
def baseStart_8364714 : Nat := 118140960795 + 8364714 * 2 ^ 59
def prefixEnd_8364714 : Nat := 4983230072969 + 3 ^ 40 * 8364714 * 2
def baseEnd_8364714 : Nat := 477235424376965694634043

theorem tailTrace_8364714 : CollatzResearch.WordTrace tailWord_8364714 prefixEnd_8364714 477235424376965694634043 := by
  unfold tailWord_8364714
  simp only [CollatzResearch.WordTrace]
  refine ⟨76271545854519308065323299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203390788945384821507528797 76271545854519308065323299)
  ·
    refine ⟨114407318781778962097984949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76271545854519308065323299 114407318781778962097984949)
    ·
      refine ⟨10725686135791777696686089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114407318781778962097984949 10725686135791777696686089)
      ·
        refine ⟨8044264601843833272514567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10725686135791777696686089 8044264601843833272514567)
        ·
          refine ⟨12066396902765749908771851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044264601843833272514567 12066396902765749908771851)
          ·
            refine ⟨18099595354148624863157777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12066396902765749908771851 18099595354148624863157777)
            ·
              refine ⟨13574696515611468647368333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18099595354148624863157777 13574696515611468647368333)
              ·
                refine ⟨5090511193354300742763125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13574696515611468647368333 5090511193354300742763125)
                ·
                  refine ⟨477235424376965694634043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5090511193354300742763125 477235424376965694634043)
                  ·
                    rfl

theorem cell23_8364714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_8364714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364714 prefixEnd_8364714 := by exact prefixLift 8364714
  have htrace : WordTrace (prefixWord ++ tailWord_8364714) baseStart_8364714 baseEnd_8364714 := by
    simpa [prefixWord, tailWord_8364714, baseEnd_8364714] using wordTrace_append hprefix tailTrace_8364714
  have hstable : (prefixWord ++ tailWord_8364714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364714).length < 2 ^ (prefixWord ++ tailWord_8364714).sum := by decide
  have hdescent : baseEnd_8364714 < baseStart_8364714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364740 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_8364740 : Nat := 118140960795 + 8364740 * 2 ^ 59
def prefixEnd_8364740 : Nat := 4983230072969 + 3 ^ 40 * 8364740 * 2
def baseEnd_8364740 : Nat := 1431710723296569383327089

theorem tailTrace_8364740 : CollatzResearch.WordTrace tailWord_8364740 prefixEnd_8364740 1431710723296569383327089 := by
  unfold tailWord_8364740
  simp only [CollatzResearch.WordTrace]
  refine ⟨152543565857991519350869837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203391421143988692467826449 152543565857991519350869837)
  ·
    refine ⟨57203837196746819756576189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152543565857991519350869837 57203837196746819756576189)
    ·
      refine ⟨21451438948780057408716071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57203837196746819756576189 21451438948780057408716071)
      ·
        refine ⟨32177158423170086113074107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21451438948780057408716071 32177158423170086113074107)
        ·
          refine ⟨48265737634755129169611161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32177158423170086113074107 48265737634755129169611161)
          ·
            refine ⟨36199303226066346877208371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48265737634755129169611161 36199303226066346877208371)
            ·
              refine ⟨54298954839099520315812557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36199303226066346877208371 54298954839099520315812557)
              ·
                refine ⟨20362108064662320118429709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54298954839099520315812557 20362108064662320118429709)
                ·
                  refine ⟨7635790524248370044411141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20362108064662320118429709 7635790524248370044411141)
                  ·
                    refine ⟨1431710723296569383327089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635790524248370044411141 1431710723296569383327089)
                    ·
                      rfl

theorem cell23_8364740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_8364740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364740 prefixEnd_8364740 := by exact prefixLift 8364740
  have htrace : WordTrace (prefixWord ++ tailWord_8364740) baseStart_8364740 baseEnd_8364740 := by
    simpa [prefixWord, tailWord_8364740, baseEnd_8364740] using wordTrace_append hprefix tailTrace_8364740
  have hstable : (prefixWord ++ tailWord_8364740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364740).length < 2 ^ (prefixWord ++ tailWord_8364740).sum := by decide
  have hdescent : baseEnd_8364740 < baseStart_8364740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364803 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 4]
def baseStart_8364803 : Nat := 118140960795 + 8364803 * 2 ^ 59
def prefixEnd_8364803 : Nat := 4983230072969 + 3 ^ 40 * 8364803 * 2
def baseEnd_8364803 : Nat := 4295164519170941403493477

theorem tailTrace_8364803 : CollatzResearch.WordTrace tailWord_8364803 prefixEnd_8364803 4295164519170941403493477 := by
  unfold tailWord_8364803
  simp only [CollatzResearch.WordTrace]
  refine ⟨305089429514754800461283063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203392953009836533640855375 305089429514754800461283063)
  ·
    refine ⟨457634144272132200691924595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305089429514754800461283063 457634144272132200691924595)
    ·
      refine ⟨686451216408198301037886893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457634144272132200691924595 686451216408198301037886893)
      ·
        refine ⟨257419206153074362889207585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686451216408198301037886893 257419206153074362889207585)
        ·
          refine ⟨193064404614805772166905689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257419206153074362889207585 193064404614805772166905689)
          ·
            refine ⟨144798303461104329125179267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193064404614805772166905689 144798303461104329125179267)
            ·
              refine ⟨217197455191656493687768901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144798303461104329125179267 217197455191656493687768901)
              ·
                refine ⟨40724522848435592566456669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217197455191656493687768901 40724522848435592566456669)
                ·
                  refine ⟨15271696068163347212421251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40724522848435592566456669 15271696068163347212421251)
                  ·
                    refine ⟨22907544102245020818631877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15271696068163347212421251 22907544102245020818631877)
                    ·
                      refine ⟨4295164519170941403493477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22907544102245020818631877 4295164519170941403493477)
                      ·
                        rfl

theorem cell23_8364803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_8364803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364803 prefixEnd_8364803 := by exact prefixLift 8364803
  have htrace : WordTrace (prefixWord ++ tailWord_8364803) baseStart_8364803 baseEnd_8364803 := by
    simpa [prefixWord, tailWord_8364803, baseEnd_8364803] using wordTrace_append hprefix tailTrace_8364803
  have hstable : (prefixWord ++ tailWord_8364803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364803).length < 2 ^ (prefixWord ++ tailWord_8364803).sum := by decide
  have hdescent : baseEnd_8364803 < baseStart_8364803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364837 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 1, 1, 4]
def baseStart_8364837 : Nat := 118140960795 + 8364837 * 2 ^ 59
def prefixEnd_8364837 : Nat := 4983230072969 + 3 ^ 40 * 8364837 * 2
def baseEnd_8364837 : Nat := 4295181977513194270468321

theorem tailTrace_8364837 : CollatzResearch.WordTrace tailWord_8364837 prefixEnd_8364837 4295181977513194270468321 := by
  unfold tailWord_8364837
  simp only [CollatzResearch.WordTrace]
  refine ⟨305090669596631624268020765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203393779731087749512013843 305090669596631624268020765)
  ·
    refine ⟨114409001098736859100507787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305090669596631624268020765 114409001098736859100507787)
    ·
      refine ⟨171613501648105288650761681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114409001098736859100507787 171613501648105288650761681)
      ·
        refine ⟨128710126236078966488071261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171613501648105288650761681 128710126236078966488071261)
        ·
          refine ⟨48266297338529612433026723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128710126236078966488071261 48266297338529612433026723)
          ·
            refine ⟨72399446007794418649540085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48266297338529612433026723 72399446007794418649540085)
            ·
              refine ⟨6787448063230726748394383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72399446007794418649540085 6787448063230726748394383)
              ·
                refine ⟨10181172094846090122591575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787448063230726748394383 10181172094846090122591575)
                ·
                  refine ⟨15271758142269135183887363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10181172094846090122591575 15271758142269135183887363)
                  ·
                    refine ⟨22907637213403702775831045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15271758142269135183887363 22907637213403702775831045)
                    ·
                      refine ⟨4295181977513194270468321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22907637213403702775831045 4295181977513194270468321)
                      ·
                        rfl

theorem cell23_8364837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_8364837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364837 prefixEnd_8364837 := by exact prefixLift 8364837
  have htrace : WordTrace (prefixWord ++ tailWord_8364837) baseStart_8364837 baseEnd_8364837 := by
    simpa [prefixWord, tailWord_8364837, baseEnd_8364837] using wordTrace_append hprefix tailTrace_8364837
  have hstable : (prefixWord ++ tailWord_8364837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364837).length < 2 ^ (prefixWord ++ tailWord_8364837).sum := by decide
  have hdescent : baseEnd_8364837 < baseStart_8364837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364904 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_8364904 : Nat := 118140960795 + 8364904 * 2 ^ 59
def prefixEnd_8364904 : Nat := 4983230072969 + 3 ^ 40 * 8364904 * 2
def baseEnd_8364904 : Nat := 4295216380717045508330513

theorem tailTrace_8364904 : CollatzResearch.WordTrace tailWord_8364904 prefixEnd_8364904 4295216380717045508330513 := by
  unfold tailWord_8364904
  simp only [CollatzResearch.WordTrace]
  refine ⟨152546556643694447355354883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203395408858259263140473177 152546556643694447355354883)
  ·
    refine ⟨228819834965541671033032325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152546556643694447355354883 228819834965541671033032325)
    ·
      refine ⟨42903719056039063318693561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228819834965541671033032325 42903719056039063318693561)
      ·
        refine ⟨32177789292029297489020171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42903719056039063318693561 32177789292029297489020171)
        ·
          refine ⟨48266683938043946233530257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32177789292029297489020171 48266683938043946233530257)
          ·
            refine ⟨36200012953532959675147693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48266683938043946233530257 36200012953532959675147693)
            ·
              refine ⟨13575004857574859878180385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36200012953532959675147693 13575004857574859878180385)
              ·
                refine ⟨10181253643181144908635289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13575004857574859878180385 10181253643181144908635289)
                ·
                  refine ⟨7635940232385858681476467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10181253643181144908635289 7635940232385858681476467)
                  ·
                    refine ⟨11453910348578788022214701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7635940232385858681476467 11453910348578788022214701)
                    ·
                      refine ⟨4295216380717045508330513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11453910348578788022214701 4295216380717045508330513)
                      ·
                        rfl

theorem cell23_8364904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_8364904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364904 prefixEnd_8364904 := by exact prefixLift 8364904
  have htrace : WordTrace (prefixWord ++ tailWord_8364904) baseStart_8364904 baseEnd_8364904 := by
    simpa [prefixWord, tailWord_8364904, baseEnd_8364904] using wordTrace_append hprefix tailTrace_8364904
  have hstable : (prefixWord ++ tailWord_8364904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364904).length < 2 ^ (prefixWord ++ tailWord_8364904).sum := by decide
  have hdescent : baseEnd_8364904 < baseStart_8364904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364927 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 1, 4, 2]
def baseStart_8364927 : Nat := 118140960795 + 8364927 * 2 ^ 59
def prefixEnd_8364927 : Nat := 4983230072969 + 3 ^ 40 * 8364927 * 2
def baseEnd_8364927 : Nat := 4295228190772098918342907

theorem tailTrace_8364927 : CollatzResearch.WordTrace tailWord_8364927 prefixEnd_8364927 4295228190772098918342907 := by
  unfold tailWord_8364927
  simp only [CollatzResearch.WordTrace]
  refine ⟨305093952166305569638797035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203395968110870379759198023 305093952166305569638797035)
  ·
    refine ⟨457640928249458354458195553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305093952166305569638797035 457640928249458354458195553)
    ·
      refine ⟨343230696187093765843646665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457640928249458354458195553 343230696187093765843646665)
      ·
        refine ⟨257423022140320324382734999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343230696187093765843646665 257423022140320324382734999)
        ·
          refine ⟨386134533210480486574102499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257423022140320324382734999 386134533210480486574102499)
          ·
            refine ⟨579201799815720729861153749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386134533210480486574102499 579201799815720729861153749)
            ·
              refine ⟨13575042183180954606120791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 579201799815720729861153749 13575042183180954606120791)
              ·
                refine ⟨20362563274771431909181187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13575042183180954606120791 20362563274771431909181187)
                ·
                  refine ⟨30543844912157147863771781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20362563274771431909181187 30543844912157147863771781)
                  ·
                    refine ⟨5726970921029465224457209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30543844912157147863771781 5726970921029465224457209)
                    ·
                      refine ⟨4295228190772098918342907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5726970921029465224457209 4295228190772098918342907)
                      ·
                        rfl

theorem cell23_8364927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_8364927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364927 prefixEnd_8364927 := by exact prefixLift 8364927
  have htrace : WordTrace (prefixWord ++ tailWord_8364927) baseStart_8364927 baseEnd_8364927 := by
    simpa [prefixWord, tailWord_8364927, baseEnd_8364927] using wordTrace_append hprefix tailTrace_8364927
  have hstable : (prefixWord ++ tailWord_8364927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364927).length < 2 ^ (prefixWord ++ tailWord_8364927).sum := by decide
  have hdescent : baseEnd_8364927 < baseStart_8364927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364960 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 3]
def baseStart_8364960 : Nat := 118140960795 + 8364960 * 2 ^ 59
def prefixEnd_8364960 : Nat := 4983230072969 + 3 ^ 40 * 8364960 * 2
def baseEnd_8364960 : Nat := 4295245135633697289230255

theorem tailTrace_8364960 : CollatzResearch.WordTrace tailWord_8364960 prefixEnd_8364960 4295245135633697289230255 := by
  unfold tailWord_8364960
  simp only [CollatzResearch.WordTrace]
  refine ⟨152547577887593008137374167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203396770516790677516498889 152547577887593008137374167)
  ·
    refine ⟨228821366831389512206061251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152547577887593008137374167 228821366831389512206061251)
    ·
      refine ⟨343232050247084268309091877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228821366831389512206061251 343232050247084268309091877)
      ·
        refine ⟨64356009421328300307954727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343232050247084268309091877 64356009421328300307954727)
        ·
          refine ⟨96534014131992450461932091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64356009421328300307954727 96534014131992450461932091)
          ·
            refine ⟨144801021197988675692898137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96534014131992450461932091 144801021197988675692898137)
            ·
              refine ⟨108600765898491506769673603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144801021197988675692898137 108600765898491506769673603)
              ·
                refine ⟨162901148847737260154510405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108600765898491506769673603 162901148847737260154510405)
                ·
                  refine ⟨30543965408950736278970701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162901148847737260154510405 30543965408950736278970701)
                  ·
                    refine ⟨11453987028356526104614013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30543965408950736278970701 11453987028356526104614013)
                    ·
                      refine ⟨4295245135633697289230255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11453987028356526104614013 4295245135633697289230255)
                      ·
                        rfl

theorem cell23_8364960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_8364960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364960 prefixEnd_8364960 := by exact prefixLift 8364960
  have htrace : WordTrace (prefixWord ++ tailWord_8364960) baseStart_8364960 baseEnd_8364960 := by
    simpa [prefixWord, tailWord_8364960, baseEnd_8364960] using wordTrace_append hprefix tailTrace_8364960
  have hstable : (prefixWord ++ tailWord_8364960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364960).length < 2 ^ (prefixWord ++ tailWord_8364960).sum := by decide
  have hdescent : baseEnd_8364960 < baseStart_8364960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364982 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_8364982 : Nat := 118140960795 + 8364982 * 2 ^ 59
def prefixEnd_8364982 : Nat := 4983230072969 + 3 ^ 40 * 8364982 * 2
def baseEnd_8364982 : Nat := 4295256432208096203155155

theorem tailTrace_8364982 : CollatzResearch.WordTrace tailWord_8364982 prefixEnd_8364982 4295256432208096203155155 := by
  unfold tailWord_8364982
  simp only [CollatzResearch.WordTrace]
  refine ⟨19068497386319144627003075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203397305454070876021366133 19068497386319144627003075)
  ·
    refine ⟨28602746079478716940504613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19068497386319144627003075 28602746079478716940504613)
    ·
      refine ⟨5363014889902259426344615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28602746079478716940504613 5363014889902259426344615)
      ·
        refine ⟨8044522334853389139516923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5363014889902259426344615 8044522334853389139516923)
        ·
          refine ⟨12066783502280083709275385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044522334853389139516923 12066783502280083709275385)
          ·
            refine ⟨9050087626710062781956539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12066783502280083709275385 9050087626710062781956539)
            ·
              refine ⟨13575131440065094172934809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9050087626710062781956539 13575131440065094172934809)
              ·
                refine ⟨10181348580048820629701107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13575131440065094172934809 10181348580048820629701107)
                ·
                  refine ⟨15272022870073230944551661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10181348580048820629701107 15272022870073230944551661)
                  ·
                    refine ⟨5727008576277461604206873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15272022870073230944551661 5727008576277461604206873)
                    ·
                      refine ⟨4295256432208096203155155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727008576277461604206873 4295256432208096203155155)
                      ·
                        rfl

theorem cell23_8364982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_8364982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364982 prefixEnd_8364982 := by exact prefixLift 8364982
  have htrace : WordTrace (prefixWord ++ tailWord_8364982) baseStart_8364982 baseEnd_8364982 := by
    simpa [prefixWord, tailWord_8364982, baseEnd_8364982] using wordTrace_append hprefix tailTrace_8364982
  have hstable : (prefixWord ++ tailWord_8364982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364982).length < 2 ^ (prefixWord ++ tailWord_8364982).sum := by decide
  have hdescent : baseEnd_8364982 < baseStart_8364982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8364990 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_8364990 : Nat := 118140960795 + 8364990 * 2 ^ 59
def prefixEnd_8364990 : Nat := 4983230072969 + 3 ^ 40 * 8364990 * 2
def baseEnd_8364990 : Nat := 4295260540053332171855117

theorem tailTrace_8364990 : CollatzResearch.WordTrace tailWord_8364990 prefixEnd_8364990 4295260540053332171855117 := by
  unfold tailWord_8364990
  simp only [CollatzResearch.WordTrace]
  refine ⟨38137031245634666424792553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203397499976718220932226949 38137031245634666424792553)
  ·
    refine ⟨28602773434225999818594415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38137031245634666424792553 28602773434225999818594415)
    ·
      refine ⟨42904160151338999727891623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28602773434225999818594415 42904160151338999727891623)
      ·
        refine ⟨64356240227008499591837435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42904160151338999727891623 64356240227008499591837435)
        ·
          refine ⟨96534360340512749387756153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64356240227008499591837435 96534360340512749387756153)
          ·
            refine ⟨72400770255384562040817115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96534360340512749387756153 72400770255384562040817115)
            ·
              refine ⟨108601155383076843061225673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72400770255384562040817115 108601155383076843061225673)
              ·
                refine ⟨81450866537307632295919255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108601155383076843061225673 81450866537307632295919255)
                ·
                  refine ⟨122176299805961448443878883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81450866537307632295919255 122176299805961448443878883)
                  ·
                    refine ⟨183264449708942172665818325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122176299805961448443878883 183264449708942172665818325)
                    ·
                      refine ⟨4295260540053332171855117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183264449708942172665818325 4295260540053332171855117)
                      ·
                        rfl

theorem cell23_8364990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_8364990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8364990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8364990 prefixEnd_8364990 := by exact prefixLift 8364990
  have htrace : WordTrace (prefixWord ++ tailWord_8364990) baseStart_8364990 baseEnd_8364990 := by
    simpa [prefixWord, tailWord_8364990, baseEnd_8364990] using wordTrace_append hprefix tailTrace_8364990
  have hstable : (prefixWord ++ tailWord_8364990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8364990).length < 2 ^ (prefixWord ++ tailWord_8364990).sum := by decide
  have hdescent : baseEnd_8364990 < baseStart_8364990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8364990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365014 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_8365014 : Nat := 118140960795 + 8365014 * 2 ^ 59
def prefixEnd_8365014 : Nat := 4983230072969 + 3 ^ 40 * 8365014 * 2
def baseEnd_8365014 : Nat := 1431757621196346692651669

theorem tailTrace_8365014 : CollatzResearch.WordTrace tailWord_8365014 prefixEnd_8365014 1431757621196346692651669 := by
  unfold tailWord_8365014
  simp only [CollatzResearch.WordTrace]
  refine ⟨19068570332311898968575881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203398083544660255664809397 19068570332311898968575881)
  ·
    refine ⟨14301427749233924226431911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19068570332311898968575881 14301427749233924226431911)
    ·
      refine ⟨21452141623850886339647867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14301427749233924226431911 21452141623850886339647867)
      ·
        refine ⟨32178212435776329509471801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21452141623850886339647867 32178212435776329509471801)
        ·
          refine ⟨24133659326832247132103851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32178212435776329509471801 24133659326832247132103851)
          ·
            refine ⟨36200488990248370698155777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24133659326832247132103851 36200488990248370698155777)
            ·
              refine ⟨27150366742686278023616833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36200488990248370698155777 27150366742686278023616833)
              ·
                refine ⟨20362775057014708517712625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27150366742686278023616833 20362775057014708517712625)
                ·
                  refine ⟨15272081292761031388284469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20362775057014708517712625 15272081292761031388284469)
                  ·
                    refine ⟨1431757621196346692651669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15272081292761031388284469 1431757621196346692651669)
                    ·
                      rfl

theorem cell23_8365014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_8365014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365014 prefixEnd_8365014 := by exact prefixLift 8365014
  have htrace : WordTrace (prefixWord ++ tailWord_8365014) baseStart_8365014 baseEnd_8365014 := by
    simpa [prefixWord, tailWord_8365014, baseEnd_8365014] using wordTrace_append hprefix tailTrace_8365014
  have hstable : (prefixWord ++ tailWord_8365014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365014).length < 2 ^ (prefixWord ++ tailWord_8365014).sum := by decide
  have hdescent : baseEnd_8365014 < baseStart_8365014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365017 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_8365017 : Nat := 118140960795 + 8365017 * 2 ^ 59
def prefixEnd_8365017 : Nat := 4983230072969 + 3 ^ 40 * 8365017 * 2
def baseEnd_8365017 : Nat := 4295274404031003566217493

theorem tailTrace_8365017 : CollatzResearch.WordTrace tailWord_8365017 prefixEnd_8365017 4295274404031003566217493 := by
  unfold tailWord_8365017
  simp only [CollatzResearch.WordTrace]
  refine ⟨305097234735979515009573305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203398156490653010006382203 305097234735979515009573305)
  ·
    refine ⟨228822926051984636257179979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305097234735979515009573305 228822926051984636257179979)
    ·
      refine ⟨343234389077976954385769969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228822926051984636257179979 343234389077976954385769969)
      ·
        refine ⟨257425791808482715789327477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343234389077976954385769969 257425791808482715789327477)
        ·
          refine ⟨24133667982045254605249451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257425791808482715789327477 24133667982045254605249451)
          ·
            refine ⟨36200501973067881907874177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24133667982045254605249451 36200501973067881907874177)
            ·
              refine ⟨27150376479800911430905633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36200501973067881907874177 27150376479800911430905633)
              ·
                refine ⟨20362782359850683573179225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27150376479800911430905633 20362782359850683573179225)
                ·
                  refine ⟨15272086769888012679884419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20362782359850683573179225 15272086769888012679884419)
                  ·
                    refine ⟨22908130154832019019826629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15272086769888012679884419 22908130154832019019826629)
                    ·
                      refine ⟨4295274404031003566217493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22908130154832019019826629 4295274404031003566217493)
                      ·
                        rfl

theorem cell23_8365017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_8365017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365017 prefixEnd_8365017 := by exact prefixLift 8365017
  have htrace : WordTrace (prefixWord ++ tailWord_8365017) baseStart_8365017 baseEnd_8365017 := by
    simpa [prefixWord, tailWord_8365017, baseEnd_8365017] using wordTrace_append hprefix tailTrace_8365017
  have hstable : (prefixWord ++ tailWord_8365017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365017).length < 2 ^ (prefixWord ++ tailWord_8365017).sum := by decide
  have hdescent : baseEnd_8365017 < baseStart_8365017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365027 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 3, 4]
def baseStart_8365027 : Nat := 118140960795 + 8365027 * 2 ^ 59
def prefixEnd_8365027 : Nat := 4983230072969 + 3 ^ 40 * 8365027 * 2
def baseEnd_8365027 : Nat := 1431759846279182842364149

theorem tailTrace_8365027 : CollatzResearch.WordTrace tailWord_8365027 prefixEnd_8365027 1431759846279182842364149 := by
  unfold tailWord_8365027
  simp only [CollatzResearch.WordTrace]
  refine ⟨305097599465943286717437335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203398399643962191144958223 305097599465943286717437335)
  ·
    refine ⟨457646399198914930076156003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305097599465943286717437335 457646399198914930076156003)
    ·
      refine ⟨686469598798372395114234005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457646399198914930076156003 686469598798372395114234005)
      ·
        refine ⟨32178262443673706020979719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 686469598798372395114234005 32178262443673706020979719)
        ·
          refine ⟨48267393665510559031469579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32178262443673706020979719 48267393665510559031469579)
          ·
            refine ⟨72401090498265838547204369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48267393665510559031469579 72401090498265838547204369)
            ·
              refine ⟨54300817873699378910403277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72401090498265838547204369 54300817873699378910403277)
              ·
                refine ⟨20362806702637267091401229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54300817873699378910403277 20362806702637267091401229)
                ·
                  refine ⟨7636052513488975159275461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20362806702637267091401229 7636052513488975159275461)
                  ·
                    refine ⟨1431759846279182842364149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636052513488975159275461 1431759846279182842364149)
                    ·
                      rfl

theorem cell23_8365027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 4].length) (baseStart_8365027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365027 prefixEnd_8365027 := by exact prefixLift 8365027
  have htrace : WordTrace (prefixWord ++ tailWord_8365027) baseStart_8365027 baseEnd_8365027 := by
    simpa [prefixWord, tailWord_8365027, baseEnd_8365027] using wordTrace_append hprefix tailTrace_8365027
  have hstable : (prefixWord ++ tailWord_8365027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365027).length < 2 ^ (prefixWord ++ tailWord_8365027).sum := by decide
  have hdescent : baseEnd_8365027 < baseStart_8365027 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8365034 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_8365034 : Nat := 118140960795 + 8365034 * 2 ^ 59
def prefixEnd_8365034 : Nat := 4983230072969 + 3 ^ 40 * 8365034 * 2
def baseEnd_8365034 : Nat := 4295283133202129999704915

theorem tailTrace_8365034 : CollatzResearch.WordTrace tailWord_8365034 prefixEnd_8365034 4295283133202129999704915 := by
  unfold tailWord_8365034
  simp only [CollatzResearch.WordTrace]
  refine ⟨76274463694229481728235539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203398569851278617941961437 76274463694229481728235539)
  ·
    refine ⟨114411695541344222592353309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76274463694229481728235539 114411695541344222592353309)
    ·
      refine ⟨42904385828004083472132491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114411695541344222592353309 42904385828004083472132491)
      ·
        refine ⟨64356578742006125208198737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42904385828004083472132491 64356578742006125208198737)
        ·
          refine ⟨48267434056504593906149053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64356578742006125208198737 48267434056504593906149053)
          ·
            refine ⟨18100287771189222714805895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48267434056504593906149053 18100287771189222714805895)
            ·
              refine ⟨27150431656783834072208843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18100287771189222714805895 27150431656783834072208843)
              ·
                refine ⟨40725647485175751108313265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27150431656783834072208843 40725647485175751108313265)
                ·
                  refine ⟨30544235613881813331234949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40725647485175751108313265 30544235613881813331234949)
                  ·
                    refine ⟨5727044177602839999606553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30544235613881813331234949 5727044177602839999606553)
                    ·
                      refine ⟨4295283133202129999704915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5727044177602839999606553 4295283133202129999704915)
                      ·
                        rfl

theorem cell23_8365034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_8365034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8365034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8365034 prefixEnd_8365034 := by exact prefixLift 8365034
  have htrace : WordTrace (prefixWord ++ tailWord_8365034) baseStart_8365034 baseEnd_8365034 := by
    simpa [prefixWord, tailWord_8365034, baseEnd_8365034] using wordTrace_append hprefix tailTrace_8365034
  have hstable : (prefixWord ++ tailWord_8365034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8365034).length < 2 ^ (prefixWord ++ tailWord_8365034).sum := by decide
  have hdescent : baseEnd_8365034 < baseStart_8365034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8365034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
