import V185TrunkScan23Chunk0827

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4898386 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_4898386 : Nat := 118140960795 + 4898386 * 2 ^ 59
def prefixEnd_4898386 : Nat := 4983230072969 + 3 ^ 40 * 4898386 * 2
def baseEnd_4898386 : Nat := 838408816418192425315913

theorem tailTrace_4898386 : CollatzResearch.WordTrace tailWord_4898386 prefixEnd_4898386 838408816418192425315913 := by
  unfold tailWord_4898386
  simp only [CollatzResearch.WordTrace]
  refine ⟨44664703707997893642638753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119105876554661049713703341 44664703707997893642638753)
  ·
    refine ⟨33498527780998420231979065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44664703707997893642638753 33498527780998420231979065)
    ·
      refine ⟨25123895835748815173984299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33498527780998420231979065 25123895835748815173984299)
      ·
        refine ⟨37685843753623222760976449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25123895835748815173984299 37685843753623222760976449)
        ·
          refine ⟨28264382815217417070732337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37685843753623222760976449 28264382815217417070732337)
          ·
            refine ⟨21198287111413062803049253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28264382815217417070732337 21198287111413062803049253)
            ·
              refine ⟨3974678833389949275571735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21198287111413062803049253 3974678833389949275571735)
              ·
                refine ⟨5962018250084923913357603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974678833389949275571735 5962018250084923913357603)
                ·
                  refine ⟨8943027375127385870036405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5962018250084923913357603 8943027375127385870036405)
                  ·
                    refine ⟨838408816418192425315913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8943027375127385870036405 838408816418192425315913)
                    ·
                      rfl

theorem cell23_4898386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_4898386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898386 prefixEnd_4898386 := by exact prefixLift 4898386
  have htrace : WordTrace (prefixWord ++ tailWord_4898386) baseStart_4898386 baseEnd_4898386 := by
    simpa [prefixWord, tailWord_4898386, baseEnd_4898386] using wordTrace_append hprefix tailTrace_4898386
  have hstable : (prefixWord ++ tailWord_4898386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898386).length < 2 ^ (prefixWord ++ tailWord_4898386).sum := by decide
  have hdescent : baseEnd_4898386 < baseStart_4898386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898390 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_4898390 : Nat := 118140960795 + 4898390 * 2 ^ 59
def prefixEnd_4898390 : Nat := 4983230072969 + 3 ^ 40 * 4898390 * 2
def baseEnd_4898390 : Nat := 279469833686355028921969

theorem tailTrace_4898390 : CollatzResearch.WordTrace tailWord_4898390 prefixEnd_4898390 279469833686355028921969 := by
  unfold tailWord_4898390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11166185045248567703356289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119105973815984722169133749 11166185045248567703356289)
  ·
    refine ⟨8374638783936425777517217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11166185045248567703356289 8374638783936425777517217)
    ·
      refine ⟨6280979087952319333137913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8374638783936425777517217 6280979087952319333137913)
      ·
        refine ⟨4710734315964239499853435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6280979087952319333137913 4710734315964239499853435)
        ·
          refine ⟨7066101473946359249780153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710734315964239499853435 7066101473946359249780153)
          ·
            refine ⟨5299576105459769437335115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7066101473946359249780153 5299576105459769437335115)
            ·
              refine ⟨7949364158189654156002673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5299576105459769437335115 7949364158189654156002673)
              ·
                refine ⟨5962023118642240617002005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7949364158189654156002673 5962023118642240617002005)
                ·
                  refine ⟨279469833686355028921969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5962023118642240617002005 279469833686355028921969)
                  ·
                    rfl

theorem cell23_4898390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_4898390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898390 prefixEnd_4898390 := by exact prefixLift 4898390
  have htrace : WordTrace (prefixWord ++ tailWord_4898390) baseStart_4898390 baseEnd_4898390 := by
    simpa [prefixWord, tailWord_4898390, baseEnd_4898390] using wordTrace_append hprefix tailTrace_4898390
  have hstable : (prefixWord ++ tailWord_4898390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898390).length < 2 ^ (prefixWord ++ tailWord_4898390).sum := by decide
  have hdescent : baseEnd_4898390 < baseStart_4898390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898392 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_4898392 : Nat := 118140960795 + 4898392 * 2 ^ 59
def prefixEnd_4898392 : Nat := 4983230072969 + 3 ^ 40 * 4898392 * 2
def baseEnd_4898392 : Nat := 2515229530138504252472711

theorem tailTrace_4898392 : CollatzResearch.WordTrace tailWord_4898392 prefixEnd_4898392 2515229530138504252472711 := by
  unfold tailWord_4898392
  simp only [CollatzResearch.WordTrace]
  refine ⟨89329516834984918797636715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119106022446646558396848953 89329516834984918797636715)
  ·
    refine ⟨133994275252477378196455073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89329516834984918797636715 133994275252477378196455073)
    ·
      refine ⟨100495706439358033647341305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133994275252477378196455073 100495706439358033647341305)
      ·
        refine ⟨75371779829518525235505979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100495706439358033647341305 75371779829518525235505979)
        ·
          refine ⟨113057669744277787853258969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75371779829518525235505979 113057669744277787853258969)
          ·
            refine ⟨84793252308208340889944227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113057669744277787853258969 84793252308208340889944227)
            ·
              refine ⟨127189878462312511334916341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84793252308208340889944227 127189878462312511334916341)
              ·
                refine ⟨11924051105841797937648407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127189878462312511334916341 11924051105841797937648407)
                ·
                  refine ⟨17886076658762696906472611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11924051105841797937648407 17886076658762696906472611)
                  ·
                    refine ⟨26829114988144045359708917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17886076658762696906472611 26829114988144045359708917)
                    ·
                      refine ⟨2515229530138504252472711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26829114988144045359708917 2515229530138504252472711)
                      ·
                        rfl

theorem cell23_4898392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_4898392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898392 prefixEnd_4898392 := by exact prefixLift 4898392
  have htrace : WordTrace (prefixWord ++ tailWord_4898392) baseStart_4898392 baseEnd_4898392 := by
    simpa [prefixWord, tailWord_4898392, baseEnd_4898392] using wordTrace_append hprefix tailTrace_4898392
  have hstable : (prefixWord ++ tailWord_4898392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898392).length < 2 ^ (prefixWord ++ tailWord_4898392).sum := by decide
  have hdescent : baseEnd_4898392 < baseStart_4898392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898429 : List Nat := [1, 4, 1, 1, 4, 1, 4, 7]
def baseStart_4898429 : Nat := 118140960795 + 4898429 * 2 ^ 59
def prefixEnd_4898429 : Nat := 4983230072969 + 3 ^ 40 * 4898429 * 2
def baseEnd_4898429 : Nat := 93157352923063726211483

theorem tailTrace_4898429 : CollatzResearch.WordTrace tailWord_4898429 prefixEnd_4898429 93157352923063726211483 := by
  unfold tailWord_4898429
  simp only [CollatzResearch.WordTrace]
  refine ⟨178660383170835792914370341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119106922113890528609580227 178660383170835792914370341)
  ·
    refine ⟨33498821844531711171444439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178660383170835792914370341 33498821844531711171444439)
    ·
      refine ⟨50248232766797566757166659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33498821844531711171444439 50248232766797566757166659)
      ·
        refine ⟨75372349150196350135749989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50248232766797566757166659 75372349150196350135749989)
        ·
          refine ⟨14132315465661815650453123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75372349150196350135749989 14132315465661815650453123)
          ·
            refine ⟨21198473198492723475679685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14132315465661815650453123 21198473198492723475679685)
            ·
              refine ⟨3974713724717385651689941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21198473198492723475679685 3974713724717385651689941)
              ·
                refine ⟨93157352923063726211483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3974713724717385651689941 93157352923063726211483)
                ·
                  rfl

theorem cell23_4898429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 7].length) (baseStart_4898429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898429 prefixEnd_4898429 := by exact prefixLift 4898429
  have htrace : WordTrace (prefixWord ++ tailWord_4898429) baseStart_4898429 baseEnd_4898429 := by
    simpa [prefixWord, tailWord_4898429, baseEnd_4898429] using wordTrace_append hprefix tailTrace_4898429
  have hstable : (prefixWord ++ tailWord_4898429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898429).length < 2 ^ (prefixWord ++ tailWord_4898429).sum := by decide
  have hdescent : baseEnd_4898429 < baseStart_4898429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898456 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_4898456 : Nat := 118140960795 + 4898456 * 2 ^ 59
def prefixEnd_4898456 : Nat := 4983230072969 + 3 ^ 40 * 4898456 * 2
def baseEnd_4898456 : Nat := 2515262392900392002072417

theorem tailTrace_4898456 : CollatzResearch.WordTrace tailWord_4898456 prefixEnd_4898456 2515262392900392002072417 := by
  unfold tailWord_4898456
  simp only [CollatzResearch.WordTrace]
  refine ⟨89330683970868988262801611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119107578627825317683735481 89330683970868988262801611)
  ·
    refine ⟨133996025956303482394202417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89330683970868988262801611 133996025956303482394202417)
    ·
      refine ⟨100497019467227611795651813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133996025956303482394202417 100497019467227611795651813)
      ·
        refine ⟨18843191150105177211684715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100497019467227611795651813 18843191150105177211684715)
        ·
          refine ⟨28264786725157765817527073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18843191150105177211684715 28264786725157765817527073)
          ·
            refine ⟨21198590043868324363145305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28264786725157765817527073 21198590043868324363145305)
            ·
              refine ⟨15898942532901243272358979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21198590043868324363145305 15898942532901243272358979)
              ·
                refine ⟨23848413799351864908538469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15898942532901243272358979 23848413799351864908538469)
                ·
                  refine ⟨4471577587378474670350963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23848413799351864908538469 4471577587378474670350963)
                  ·
                    refine ⟨6707366381067712005526445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4471577587378474670350963 6707366381067712005526445)
                    ·
                      refine ⟨2515262392900392002072417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6707366381067712005526445 2515262392900392002072417)
                      ·
                        rfl

theorem cell23_4898456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_4898456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898456 prefixEnd_4898456 := by exact prefixLift 4898456
  have htrace : WordTrace (prefixWord ++ tailWord_4898456) baseStart_4898456 baseEnd_4898456 := by
    simpa [prefixWord, tailWord_4898456, baseEnd_4898456] using wordTrace_append hprefix tailTrace_4898456
  have hstable : (prefixWord ++ tailWord_4898456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898456).length < 2 ^ (prefixWord ++ tailWord_4898456).sum := by decide
  have hdescent : baseEnd_4898456 < baseStart_4898456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898496 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 1, 4, 2]
def baseStart_4898496 : Nat := 118140960795 + 4898496 * 2 ^ 59
def prefixEnd_4898496 : Nat := 4983230072969 + 3 ^ 40 * 4898496 * 2
def baseEnd_4898496 : Nat := 2515282932126571845572233

theorem tailTrace_4898496 : CollatzResearch.WordTrace tailWord_4898496 prefixEnd_4898496 2515282932126571845572233 := by
  unfold tailWord_4898496
  simp only [CollatzResearch.WordTrace]
  refine ⟨89331413430796531678529671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119108551241062042238039561 89331413430796531678529671)
  ·
    refine ⟨133997120146194797517794507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89331413430796531678529671 133997120146194797517794507)
    ·
      refine ⟨200995680219292196276691761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133997120146194797517794507 200995680219292196276691761)
      ·
        refine ⟨150746760164469147207518821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200995680219292196276691761 150746760164469147207518821)
        ·
          refine ⟨28265017530837965101409779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150746760164469147207518821 28265017530837965101409779)
          ·
            refine ⟨42397526296256947652114669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28265017530837965101409779 42397526296256947652114669)
            ·
              refine ⟨15899072361096355369543001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42397526296256947652114669 15899072361096355369543001)
              ·
                refine ⟨11924304270822266527157251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15899072361096355369543001 11924304270822266527157251)
                ·
                  refine ⟨17886456406233399790735877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11924304270822266527157251 17886456406233399790735877)
                  ·
                    refine ⟨3353710576168762460762977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17886456406233399790735877 3353710576168762460762977)
                    ·
                      refine ⟨2515282932126571845572233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353710576168762460762977 2515282932126571845572233)
                      ·
                        rfl

theorem cell23_4898496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_4898496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898496 prefixEnd_4898496 := by exact prefixLift 4898496
  have htrace : WordTrace (prefixWord ++ tailWord_4898496) baseStart_4898496 baseEnd_4898496 := by
    simpa [prefixWord, tailWord_4898496, baseEnd_4898496] using wordTrace_append hprefix tailTrace_4898496
  have hstable : (prefixWord ++ tailWord_4898496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898496).length < 2 ^ (prefixWord ++ tailWord_4898496).sum := by decide
  have hdescent : baseEnd_4898496 < baseStart_4898496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898500 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_4898500 : Nat := 118140960795 + 4898500 * 2 ^ 59
def prefixEnd_4898500 : Nat := 4983230072969 + 3 ^ 40 * 4898500 * 2
def baseEnd_4898500 : Nat := 2515284986049189829922215

theorem tailTrace_4898500 : CollatzResearch.WordTrace tailWord_4898500 prefixEnd_4898500 2515284986049189829922215 := by
  unfold tailWord_4898500
  simp only [CollatzResearch.WordTrace]
  refine ⟨89331486376789286020102477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119108648502385714693469969 89331486376789286020102477)
  ·
    refine ⟨33499307391295982257538429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89331486376789286020102477 33499307391295982257538429)
    ·
      refine ⟨12562240271735993346576911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33499307391295982257538429 12562240271735993346576911)
      ·
        refine ⟨18843360407603990019865367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12562240271735993346576911 18843360407603990019865367)
        ·
          refine ⟨28265040611405985029798051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18843360407603990019865367 28265040611405985029798051)
          ·
            refine ⟨42397560917108977544697077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28265040611405985029798051 42397560917108977544697077)
            ·
              refine ⟨3974771335978966644815351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42397560917108977544697077 3974771335978966644815351)
              ·
                refine ⟨5962157003968449967223027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974771335978966644815351 5962157003968449967223027)
                ·
                  refine ⟨8943235505952674950834541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5962157003968449967223027 8943235505952674950834541)
                  ·
                    refine ⟨3353713314732253106562953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8943235505952674950834541 3353713314732253106562953)
                    ·
                      refine ⟨2515284986049189829922215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353713314732253106562953 2515284986049189829922215)
                      ·
                        rfl

theorem cell23_4898500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_4898500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898500 prefixEnd_4898500 := by exact prefixLift 4898500
  have htrace : WordTrace (prefixWord ++ tailWord_4898500) baseStart_4898500 baseEnd_4898500 := by
    simpa [prefixWord, tailWord_4898500, baseEnd_4898500] using wordTrace_append hprefix tailTrace_4898500
  have hstable : (prefixWord ++ tailWord_4898500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898500).length < 2 ^ (prefixWord ++ tailWord_4898500).sum := by decide
  have hdescent : baseEnd_4898500 < baseStart_4898500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898513 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 2, 2, 2]
def baseStart_4898513 : Nat := 118140960795 + 4898513 * 2 ^ 59
def prefixEnd_4898513 : Nat := 4983230072969 + 3 ^ 40 * 4898513 * 2
def baseEnd_4898513 : Nat := 2515291661297698279059655

theorem tailTrace_4898513 : CollatzResearch.WordTrace tailWord_4898513 prefixEnd_4898513 2515291661297698279059655 := by
  unfold tailWord_4898513
  simp only [CollatzResearch.WordTrace]
  refine ⟨178663446902531475260428193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119108964601687650173618795 178663446902531475260428193)
  ·
    refine ⟨133997585176898606445321145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178663446902531475260428193 133997585176898606445321145)
    ·
      refine ⟨100498188882673954833990859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133997585176898606445321145 100498188882673954833990859)
      ·
        refine ⟨150747283324010932250986289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100498188882673954833990859 150747283324010932250986289)
        ·
          refine ⟨113060462493008199188239717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150747283324010932250986289 113060462493008199188239717)
          ·
            refine ⟨21198836717439037347794947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113060462493008199188239717 21198836717439037347794947)
            ·
              refine ⟨31798255076158556021692421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21198836717439037347794947 31798255076158556021692421)
              ·
                refine ⟨5962172826779729254067329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31798255076158556021692421 5962172826779729254067329)
                ·
                  refine ⟨4471629620084796940550497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5962172826779729254067329 4471629620084796940550497)
                  ·
                    refine ⟨3353722215063597705412873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4471629620084796940550497 3353722215063597705412873)
                    ·
                      refine ⟨2515291661297698279059655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353722215063597705412873 2515291661297698279059655)
                      ·
                        rfl

theorem cell23_4898513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_4898513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898513 prefixEnd_4898513 := by exact prefixLift 4898513
  have htrace : WordTrace (prefixWord ++ tailWord_4898513) baseStart_4898513 baseEnd_4898513 := by
    simpa [prefixWord, tailWord_4898513, baseEnd_4898513] using wordTrace_append hprefix tailTrace_4898513
  have hstable : (prefixWord ++ tailWord_4898513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898513).length < 2 ^ (prefixWord ++ tailWord_4898513).sum := by decide
  have hdescent : baseEnd_4898513 < baseStart_4898513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898516 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4898516 : Nat := 118140960795 + 4898516 * 2 ^ 59
def prefixEnd_4898516 : Nat := 4983230072969 + 3 ^ 40 * 4898516 * 2
def baseEnd_4898516 : Nat := 2515293201739661767322141

theorem tailTrace_4898516 : CollatzResearch.WordTrace tailWord_4898516 prefixEnd_4898516 2515293201739661767322141 := by
  unfold tailWord_4898516
  simp only [CollatzResearch.WordTrace]
  refine ⟨89331778160760303386393701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119109037547680404515191601 89331778160760303386393701)
  ·
    refine ⟨16749708405142556884948819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89331778160760303386393701 16749708405142556884948819)
    ·
      refine ⟨25124562607713835327423229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16749708405142556884948819 25124562607713835327423229)
      ·
        refine ⟨9421710977892688247783711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25124562607713835327423229 9421710977892688247783711)
        ·
          refine ⟨14132566466839032371675567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9421710977892688247783711 14132566466839032371675567)
          ·
            refine ⟨21198849700258548557513351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14132566466839032371675567 21198849700258548557513351)
            ·
              refine ⟨31798274550387822836270027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21198849700258548557513351 31798274550387822836270027)
              ·
                refine ⟨47697411825581734254405041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31798274550387822836270027 47697411825581734254405041)
                ·
                  refine ⟨35773058869186300690803781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47697411825581734254405041 35773058869186300690803781)
                  ·
                    refine ⟨6707448537972431379525709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35773058869186300690803781 6707448537972431379525709)
                    ·
                      refine ⟨2515293201739661767322141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6707448537972431379525709 2515293201739661767322141)
                      ·
                        rfl

theorem cell23_4898516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4898516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898516 prefixEnd_4898516 := by exact prefixLift 4898516
  have htrace : WordTrace (prefixWord ++ tailWord_4898516) baseStart_4898516 baseEnd_4898516 := by
    simpa [prefixWord, tailWord_4898516, baseEnd_4898516] using wordTrace_append hprefix tailTrace_4898516
  have hstable : (prefixWord ++ tailWord_4898516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898516).length < 2 ^ (prefixWord ++ tailWord_4898516).sum := by decide
  have hdescent : baseEnd_4898516 < baseStart_4898516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898569 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_4898569 : Nat := 118140960795 + 4898569 * 2 ^ 59
def prefixEnd_4898569 : Nat := 4983230072969 + 3 ^ 40 * 4898569 * 2
def baseEnd_4898569 : Nat := 2515320416214350059959397

theorem tailTrace_4898569 : CollatzResearch.WordTrace tailWord_4898569 prefixEnd_4898569 2515320416214350059959397 := by
  unfold tailWord_4898569
  simp only [CollatzResearch.WordTrace]
  refine ⟨178665489390328596824466761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119110326260219064549644507 178665489390328596824466761)
  ·
    refine ⟨133999117042746447618350071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178665489390328596824466761 133999117042746447618350071)
    ·
      refine ⟨200998675564119671427525107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133999117042746447618350071 200998675564119671427525107)
      ·
        refine ⟨301498013346179507141287661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200998675564119671427525107 301498013346179507141287661)
        ·
          refine ⟨113061755004817315177982873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301498013346179507141287661 113061755004817315177982873)
          ·
            refine ⟨84796316253612986383487155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113061755004817315177982873 84796316253612986383487155)
            ·
              refine ⟨127194474380419479575230733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84796316253612986383487155 127194474380419479575230733)
              ·
                refine ⟨47697927892657304840711525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127194474380419479575230733 47697927892657304840711525)
                ·
                  refine ⟨8943361479873244657633411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47697927892657304840711525 8943361479873244657633411)
                  ·
                    refine ⟨13415042219809866986450117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8943361479873244657633411 13415042219809866986450117)
                    ·
                      refine ⟨2515320416214350059959397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13415042219809866986450117 2515320416214350059959397)
                      ·
                        rfl

theorem cell23_4898569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_4898569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898569 prefixEnd_4898569 := by exact prefixLift 4898569
  have htrace : WordTrace (prefixWord ++ tailWord_4898569) baseStart_4898569 baseEnd_4898569 := by
    simpa [prefixWord, tailWord_4898569, baseEnd_4898569] using wordTrace_append hprefix tailTrace_4898569
  have hstable : (prefixWord ++ tailWord_4898569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898569).length < 2 ^ (prefixWord ++ tailWord_4898569).sum := by decide
  have hdescent : baseEnd_4898569 < baseStart_4898569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898609 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 8]
def baseStart_4898609 : Nat := 118140960795 + 4898609 * 2 ^ 59
def prefixEnd_4898609 : Nat := 4983230072969 + 3 ^ 40 * 4898609 * 2
def baseEnd_4898609 : Nat := 279482328382281100384357

theorem tailTrace_4898609 : CollatzResearch.WordTrace tailWord_4898609 prefixEnd_4898609 279482328382281100384357 := by
  unfold tailWord_4898609
  simp only [CollatzResearch.WordTrace]
  refine ⟨178666948310183683655922881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119111298873455789103948587 178666948310183683655922881)
  ·
    refine ⟨134000211232637762741942161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178666948310183683655922881 134000211232637762741942161)
    ·
      refine ⟨100500158424478322056456621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134000211232637762741942161 100500158424478322056456621)
      ·
        refine ⟨37687559409179370771171233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100500158424478322056456621 37687559409179370771171233)
        ·
          refine ⟨28265669556884528078378425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37687559409179370771171233 28265669556884528078378425)
          ·
            refine ⟨21199252167663396058783819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28265669556884528078378425 21199252167663396058783819)
            ·
              refine ⟨31798878251495094088175729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21199252167663396058783819 31798878251495094088175729)
              ·
                refine ⟨23849158688621320566131797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31798878251495094088175729 23849158688621320566131797)
                ·
                  refine ⟨279482328382281100384357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23849158688621320566131797 279482328382281100384357)
                  ·
                    rfl

theorem cell23_4898609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 8].length) (baseStart_4898609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898609 prefixEnd_4898609 := by exact prefixLift 4898609
  have htrace : WordTrace (prefixWord ++ tailWord_4898609) baseStart_4898609 baseEnd_4898609 := by
    simpa [prefixWord, tailWord_4898609, baseEnd_4898609] using wordTrace_append hprefix tailTrace_4898609
  have hstable : (prefixWord ++ tailWord_4898609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898609).length < 2 ^ (prefixWord ++ tailWord_4898609).sum := by decide
  have hdescent : baseEnd_4898609 < baseStart_4898609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898623 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 3]
def baseStart_4898623 : Nat := 118140960795 + 4898623 * 2 ^ 59
def prefixEnd_4898623 : Nat := 4983230072969 + 3 ^ 40 * 4898623 * 2
def baseEnd_4898623 : Nat := 2515348144169692848684149

theorem tailTrace_4898623 : CollatzResearch.WordTrace tailWord_4898623 prefixEnd_4898623 2515348144169692848684149 := by
  unfold tailWord_4898623
  simp only [CollatzResearch.WordTrace]
  refine ⟨178667458932132964046932523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119111639288088642697955015 178667458932132964046932523)
  ·
    refine ⟨268001188398199446070398785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178667458932132964046932523 268001188398199446070398785)
    ·
      refine ⟨201000891298649584552799089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268001188398199446070398785 201000891298649584552799089)
      ·
        refine ⟨150750668473987188414599317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201000891298649584552799089 150750668473987188414599317)
        ·
          refine ⟨7066437584718149456934343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150750668473987188414599317 7066437584718149456934343)
          ·
            refine ⟨10599656377077224185401515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7066437584718149456934343 10599656377077224185401515)
            ·
              refine ⟨15899484565615836278102273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10599656377077224185401515 15899484565615836278102273)
              ·
                refine ⟨11924613424211877208576705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15899484565615836278102273 11924613424211877208576705)
                ·
                  refine ⟨8943460068158907906432529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11924613424211877208576705 8943460068158907906432529)
                  ·
                    refine ⟨6707595051119180929824397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8943460068158907906432529 6707595051119180929824397)
                    ·
                      refine ⟨2515348144169692848684149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6707595051119180929824397 2515348144169692848684149)
                      ·
                        rfl

theorem cell23_4898623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_4898623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898623 prefixEnd_4898623 := by exact prefixLift 4898623
  have htrace : WordTrace (prefixWord ++ tailWord_4898623) baseStart_4898623 baseEnd_4898623 := by
    simpa [prefixWord, tailWord_4898623, baseEnd_4898623] using wordTrace_append hprefix tailTrace_4898623
  have hstable : (prefixWord ++ tailWord_4898623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898623).length < 2 ^ (prefixWord ++ tailWord_4898623).sum := by decide
  have hdescent : baseEnd_4898623 < baseStart_4898623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898656 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 3, 5]
def baseStart_4898656 : Nat := 118140960795 + 4898656 * 2 ^ 59
def prefixEnd_4898656 : Nat := 4983230072969 + 3 ^ 40 * 4898656 * 2
def baseEnd_4898656 : Nat := 838455029677097073190499

theorem tailTrace_4898656 : CollatzResearch.WordTrace tailWord_4898656 prefixEnd_4898656 838455029677097073190499 := by
  unfold tailWord_4898656
  simp only [CollatzResearch.WordTrace]
  refine ⟨89334331270506705341441911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119112441694008940455255881 89334331270506705341441911)
  ·
    refine ⟨134001496905760058012162867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89334331270506705341441911 134001496905760058012162867)
    ·
      refine ⟨201002245358640087018244301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134001496905760058012162867 201002245358640087018244301)
      ·
        refine ⟨75375842009490032631841613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201002245358640087018244301 75375842009490032631841613)
        ·
          refine ⟨28265940753558762236940605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75375842009490032631841613 28265940753558762236940605)
          ·
            refine ⟨10599727782584535838852727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28265940753558762236940605 10599727782584535838852727)
            ·
              refine ⟨15899591673876803758279091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10599727782584535838852727 15899591673876803758279091)
              ·
                refine ⟨23849387510815205637418637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15899591673876803758279091 23849387510815205637418637)
                ·
                  refine ⟨8943520316555702114031989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23849387510815205637418637 8943520316555702114031989)
                  ·
                    refine ⟨838455029677097073190499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8943520316555702114031989 838455029677097073190499)
                    ·
                      rfl

theorem cell23_4898656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_4898656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898656 prefixEnd_4898656 := by exact prefixLift 4898656
  have htrace : WordTrace (prefixWord ++ tailWord_4898656) baseStart_4898656 baseEnd_4898656 := by
    simpa [prefixWord, tailWord_4898656, baseEnd_4898656] using wordTrace_append hprefix tailTrace_4898656
  have hstable : (prefixWord ++ tailWord_4898656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898656).length < 2 ^ (prefixWord ++ tailWord_4898656).sum := by decide
  have hdescent : baseEnd_4898656 < baseStart_4898656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898673 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 1, 5]
def baseStart_4898673 : Nat := 118140960795 + 4898673 * 2 ^ 59
def prefixEnd_4898673 : Nat := 4983230072969 + 3 ^ 40 * 4898673 * 2
def baseEnd_4898673 : Nat := 838457939400805884352973

theorem tailTrace_4898673 : CollatzResearch.WordTrace tailWord_4898673 prefixEnd_4898673 838457939400805884352973 := by
  unfold tailWord_4898673
  simp only [CollatzResearch.WordTrace]
  refine ⟨178669282581951822586252673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119112855054634548390835115 178669282581951822586252673)
  ·
    refine ⟨134001961936463866939689505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178669282581951822586252673 134001961936463866939689505)
    ·
      refine ⟨100501471452347900204767129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134001961936463866939689505 100501471452347900204767129)
      ·
        refine ⟨75376103589260925153575347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100501471452347900204767129 75376103589260925153575347)
        ·
          refine ⟨113064155383891387730363021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75376103589260925153575347 113064155383891387730363021)
          ·
            refine ⟨42399058268959270398886133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113064155383891387730363021 42399058268959270398886133)
            ·
              refine ⟨3974911712714931599895575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42399058268959270398886133 3974911712714931599895575)
              ·
                refine ⟨5962367569072397399843363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974911712714931599895575 5962367569072397399843363)
                ·
                  refine ⟨8943551353608596099765045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5962367569072397399843363 8943551353608596099765045)
                  ·
                    refine ⟨838457939400805884352973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8943551353608596099765045 838457939400805884352973)
                    ·
                      rfl

theorem cell23_4898673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_4898673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898673 prefixEnd_4898673 := by exact prefixLift 4898673
  have htrace : WordTrace (prefixWord ++ tailWord_4898673) baseStart_4898673 baseEnd_4898673 := by
    simpa [prefixWord, tailWord_4898673, baseEnd_4898673] using wordTrace_append hprefix tailTrace_4898673
  have hstable : (prefixWord ++ tailWord_4898673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898673).length < 2 ^ (prefixWord ++ tailWord_4898673).sum := by decide
  have hdescent : baseEnd_4898673 < baseStart_4898673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898727 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_4898727 : Nat := 118140960795 + 4898727 * 2 ^ 59
def prefixEnd_4898727 : Nat := 4983230072969 + 3 ^ 40 * 4898727 * 2
def baseEnd_4898727 : Nat := 2515401546157760441783671

theorem tailTrace_4898727 : CollatzResearch.WordTrace tailWord_4898727 prefixEnd_4898727 2515401546157760441783671 := by
  unfold tailWord_4898727
  simp only [CollatzResearch.WordTrace]
  refine ⟨178671252123756189808718435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119114168082504126539145623 178671252123756189808718435)
  ·
    refine ⟨268006878185634284713077653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178671252123756189808718435 268006878185634284713077653)
    ·
      refine ⟨12562822414951607095925515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 268006878185634284713077653 12562822414951607095925515)
      ·
        refine ⟨18844233622427410643888273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12562822414951607095925515 18844233622427410643888273)
        ·
          refine ⟨14133175216820557982916205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18844233622427410643888273 14133175216820557982916205)
          ·
            refine ⟨5299940706307709243593577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14133175216820557982916205 5299940706307709243593577)
            ·
              refine ⟨3974955529730781932695183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5299940706307709243593577 3974955529730781932695183)
              ·
                refine ⟨5962433294596172899042775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974955529730781932695183 5962433294596172899042775)
                ·
                  refine ⟨8943649941894259348564163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5962433294596172899042775 8943649941894259348564163)
                  ·
                    refine ⟨13415474912841389022846245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8943649941894259348564163 13415474912841389022846245)
                    ·
                      refine ⟨2515401546157760441783671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13415474912841389022846245 2515401546157760441783671)
                      ·
                        rfl

theorem cell23_4898727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_4898727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898727 prefixEnd_4898727 := by exact prefixLift 4898727
  have htrace : WordTrace (prefixWord ++ tailWord_4898727) baseStart_4898727 baseEnd_4898727 := by
    simpa [prefixWord, tailWord_4898727, baseEnd_4898727] using wordTrace_append hprefix tailTrace_4898727
  have hstable : (prefixWord ++ tailWord_4898727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898727).length < 2 ^ (prefixWord ++ tailWord_4898727).sum := by decide
  have hdescent : baseEnd_4898727 < baseStart_4898727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898729 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 1, 9]
def baseStart_4898729 : Nat := 118140960795 + 4898729 * 2 ^ 59
def prefixEnd_4898729 : Nat := 4983230072969 + 3 ^ 40 * 4898729 * 2
def baseEnd_4898729 : Nat := 838467524373023144652887

theorem tailTrace_4898729 : CollatzResearch.WordTrace tailWord_4898729 prefixEnd_4898729 838467524373023144652887 := by
  unfold tailWord_4898729
  simp only [CollatzResearch.WordTrace]
  refine ⟨178671325069748944150291241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119114216713165962766860827 178671325069748944150291241)
  ·
    refine ⟨134003493802311708112718431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178671325069748944150291241 134003493802311708112718431)
    ·
      refine ⟨201005240703467562169077647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134003493802311708112718431 201005240703467562169077647)
      ·
        refine ⟨301507861055201343253616471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201005240703467562169077647 301507861055201343253616471)
        ·
          refine ⟨452261791582802014880424707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301507861055201343253616471 452261791582802014880424707)
          ·
            refine ⟨678392687374203022320637061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452261791582802014880424707 678392687374203022320637061)
            ·
              refine ⟨127198628882663066685119449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 678392687374203022320637061 127198628882663066685119449)
              ·
                refine ⟨95398971661997300013839587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127198628882663066685119449 95398971661997300013839587)
                ·
                  refine ⟨143098457492995950020759381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95398971661997300013839587 143098457492995950020759381)
                  ·
                    refine ⟨838467524373023144652887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 143098457492995950020759381 838467524373023144652887)
                    ·
                      rfl

theorem cell23_4898729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_4898729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898729 prefixEnd_4898729 := by exact prefixLift 4898729
  have htrace : WordTrace (prefixWord ++ tailWord_4898729) baseStart_4898729 baseEnd_4898729 := by
    simpa [prefixWord, tailWord_4898729, baseEnd_4898729] using wordTrace_append hprefix tailTrace_4898729
  have hstable : (prefixWord ++ tailWord_4898729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898729).length < 2 ^ (prefixWord ++ tailWord_4898729).sum := by decide
  have hdescent : baseEnd_4898729 < baseStart_4898729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898760 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_4898760 : Nat := 118140960795 + 4898760 * 2 ^ 59
def prefixEnd_4898760 : Nat := 4983230072969 + 3 ^ 40 * 4898760 * 2
def baseEnd_4898760 : Nat := 2515418491019358812671019

theorem tailTrace_4898760 : CollatzResearch.WordTrace tailWord_4898760 prefixEnd_4898760 2515418491019358812671019 := by
  unfold tailWord_4898760
  simp only [CollatzResearch.WordTrace]
  refine ⟨89336227866318318222334867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119114970488424424296446489 89336227866318318222334867)
  ·
    refine ⟨134004341799477477333502301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89336227866318318222334867 134004341799477477333502301)
    ·
      refine ⟨50251628174804054000063363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134004341799477477333502301 50251628174804054000063363)
      ·
        refine ⟨75377442262206081000095045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50251628174804054000063363 75377442262206081000095045)
        ·
          refine ⟨14133270424163640187517821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75377442262206081000095045 14133270424163640187517821)
          ·
            refine ⟨5299976409061365070319183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14133270424163640187517821 5299976409061365070319183)
            ·
              refine ⟨7949964613592047605478775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5299976409061365070319183 7949964613592047605478775)
              ·
                refine ⟨11924946920388071408218163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7949964613592047605478775 11924946920388071408218163)
                ·
                  refine ⟨17887420380582107112327245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11924946920388071408218163 17887420380582107112327245)
                  ·
                    refine ⟨6707782642718290167122717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17887420380582107112327245 6707782642718290167122717)
                    ·
                      refine ⟨2515418491019358812671019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6707782642718290167122717 2515418491019358812671019)
                      ·
                        rfl

theorem cell23_4898760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_4898760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898760 prefixEnd_4898760 := by exact prefixLift 4898760
  have htrace : WordTrace (prefixWord ++ tailWord_4898760) baseStart_4898760 baseEnd_4898760 := by
    simpa [prefixWord, tailWord_4898760, baseEnd_4898760] using wordTrace_append hprefix tailTrace_4898760
  have hstable : (prefixWord ++ tailWord_4898760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898760).length < 2 ^ (prefixWord ++ tailWord_4898760).sum := by decide
  have hdescent : baseEnd_4898760 < baseStart_4898760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898796 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_4898796 : Nat := 118140960795 + 4898796 * 2 ^ 59
def prefixEnd_4898796 : Nat := 4983230072969 + 3 ^ 40 * 4898796 * 2
def baseEnd_4898796 : Nat := 2515436976322920671820853

theorem tailTrace_4898796 : CollatzResearch.WordTrace tailWord_4898796 prefixEnd_4898796 2515436976322920671820853 := by
  unfold tailWord_4898796
  simp only [CollatzResearch.WordTrace]
  refine ⟨89336884380253107296490121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119115845840337476395320161 89336884380253107296490121)
  ·
    refine ⟨67002663285189830472367591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89336884380253107296490121 67002663285189830472367591)
    ·
      refine ⟨100503994927784745708551387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67002663285189830472367591 100503994927784745708551387)
      ·
        refine ⟨150755992391677118562827081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100503994927784745708551387 150755992391677118562827081)
        ·
          refine ⟨113066994293757838922120311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150755992391677118562827081 113066994293757838922120311)
          ·
            refine ⟨169600491440636758383180467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113066994293757838922120311 169600491440636758383180467)
            ·
              refine ⟨254400737160955137574770701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169600491440636758383180467 254400737160955137574770701)
              ·
                refine ⟨95400276435358176590539013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254400737160955137574770701 95400276435358176590539013)
                ·
                  refine ⟨17887551831629658110726065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95400276435358176590539013 17887551831629658110726065)
                  ·
                    refine ⟨13415663873722243583044549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17887551831629658110726065 13415663873722243583044549)
                    ·
                      refine ⟨2515436976322920671820853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13415663873722243583044549 2515436976322920671820853)
                      ·
                        rfl

theorem cell23_4898796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_4898796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898796 prefixEnd_4898796 := by exact prefixLift 4898796
  have htrace : WordTrace (prefixWord ++ tailWord_4898796) baseStart_4898796 baseEnd_4898796 := by
    simpa [prefixWord, tailWord_4898796, baseEnd_4898796] using wordTrace_append hprefix tailTrace_4898796
  have hstable : (prefixWord ++ tailWord_4898796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898796).length < 2 ^ (prefixWord ++ tailWord_4898796).sum := by decide
  have hdescent : baseEnd_4898796 < baseStart_4898796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898800 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 4, 2, 2]
def baseStart_4898800 : Nat := 118140960795 + 4898800 * 2 ^ 59
def prefixEnd_4898800 : Nat := 4983230072969 + 3 ^ 40 * 4898800 * 2
def baseEnd_4898800 : Nat := 2515439030245538656170835

theorem tailTrace_4898800 : CollatzResearch.WordTrace tailWord_4898800 prefixEnd_4898800 2515439030245538656170835 := by
  unfold tailWord_4898800
  simp only [CollatzResearch.WordTrace]
  refine ⟨89336957326245861638062927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119115943101661148850750569 89336957326245861638062927)
  ·
    refine ⟨134005435989368792457094391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89336957326245861638062927 134005435989368792457094391)
    ·
      refine ⟨201008153984053188685641587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134005435989368792457094391 201008153984053188685641587)
      ·
        refine ⟨301512230976079783028462381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201008153984053188685641587 301512230976079783028462381)
        ·
          refine ⟨113067086616029918635673393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301512230976079783028462381 113067086616029918635673393)
          ·
            refine ⟨84800314962022438976755045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113067086616029918635673393 84800314962022438976755045)
            ·
              refine ⟨15900059055379207308141571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84800314962022438976755045 15900059055379207308141571)
              ·
                refine ⟨23850088583068810962212357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15900059055379207308141571 23850088583068810962212357)
                ·
                  refine ⟨4471891609325402055414817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23850088583068810962212357 4471891609325402055414817)
                  ·
                    refine ⟨3353918706994051541561113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4471891609325402055414817 3353918706994051541561113)
                    ·
                      refine ⟨2515439030245538656170835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353918706994051541561113 2515439030245538656170835)
                      ·
                        rfl

theorem cell23_4898800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 2, 2].length) (baseStart_4898800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898800 prefixEnd_4898800 := by exact prefixLift 4898800
  have htrace : WordTrace (prefixWord ++ tailWord_4898800) baseStart_4898800 baseEnd_4898800 := by
    simpa [prefixWord, tailWord_4898800, baseEnd_4898800] using wordTrace_append hprefix tailTrace_4898800
  have hstable : (prefixWord ++ tailWord_4898800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898800).length < 2 ^ (prefixWord ++ tailWord_4898800).sum := by decide
  have hdescent : baseEnd_4898800 < baseStart_4898800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898817 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_4898817 : Nat := 118140960795 + 4898817 * 2 ^ 59
def prefixEnd_4898817 : Nat := 4983230072969 + 3 ^ 40 * 4898817 * 2
def baseEnd_4898817 : Nat := 2515447759416665089658257

theorem tailTrace_4898817 : CollatzResearch.WordTrace tailWord_4898817 prefixEnd_4898817 2515447759416665089658257 := by
  unfold tailWord_4898817
  simp only [CollatzResearch.WordTrace]
  refine ⟨178674534693430135179494705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119116356462286756786329803 178674534693430135179494705)
  ·
    refine ⟨134005901020072601384621029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178674534693430135179494705 134005901020072601384621029)
    ·
      refine ⟨25126106441263612759616443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134005901020072601384621029 25126106441263612759616443)
      ·
        refine ⟨37689159661895419139424665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25126106441263612759616443 37689159661895419139424665)
        ·
          refine ⟨28266869746421564354568499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37689159661895419139424665 28266869746421564354568499)
          ·
            refine ⟨42400304619632346531852749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28266869746421564354568499 42400304619632346531852749)
            ·
              refine ⟨15900114232362129949444781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42400304619632346531852749 15900114232362129949444781)
              ·
                refine ⟨5962542837135798731041793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15900114232362129949444781 5962542837135798731041793)
                ·
                  refine ⟨4471907127851849048281345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5962542837135798731041793 4471907127851849048281345)
                  ·
                    refine ⟨3353930345888886786211009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4471907127851849048281345 3353930345888886786211009)
                    ·
                      refine ⟨2515447759416665089658257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353930345888886786211009 2515447759416665089658257)
                      ·
                        rfl

theorem cell23_4898817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_4898817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898817 prefixEnd_4898817 := by exact prefixLift 4898817
  have htrace : WordTrace (prefixWord ++ tailWord_4898817) baseStart_4898817 baseEnd_4898817 := by
    simpa [prefixWord, tailWord_4898817, baseEnd_4898817] using wordTrace_append hprefix tailTrace_4898817
  have hstable : (prefixWord ++ tailWord_4898817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898817).length < 2 ^ (prefixWord ++ tailWord_4898817).sum := by decide
  have hdescent : baseEnd_4898817 < baseStart_4898817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898853 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_4898853 : Nat := 118140960795 + 4898853 * 2 ^ 59
def prefixEnd_4898853 : Nat := 4983230072969 + 3 ^ 40 * 4898853 * 2
def baseEnd_4898853 : Nat := 838488748240075649602697

theorem tailTrace_4898853 : CollatzResearch.WordTrace tailWord_4898853 prefixEnd_4898853 838488748240075649602697 := by
  unfold tailWord_4898853
  simp only [CollatzResearch.WordTrace]
  refine ⟨178675847721299713327805213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119117231814199808885203475 178675847721299713327805213)
  ·
    refine ⟨67003442895487392497926955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178675847721299713327805213 67003442895487392497926955)
    ·
      refine ⟨100505164343231088746890433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67003442895487392497926955 100505164343231088746890433)
      ·
        refine ⟨75378873257423316560167825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100505164343231088746890433 75378873257423316560167825)
        ·
          refine ⟨56534154943067487420125869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75378873257423316560167825 56534154943067487420125869)
          ·
            refine ⟨21200308103650307782547201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56534154943067487420125869 21200308103650307782547201)
            ·
              refine ⟨15900231077737730836910401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21200308103650307782547201 15900231077737730836910401)
              ·
                refine ⟨11925173308303298127682801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15900231077737730836910401 11925173308303298127682801)
                ·
                  refine ⟨8943879981227473595762101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11925173308303298127682801 8943879981227473595762101)
                  ·
                    refine ⟨838488748240075649602697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8943879981227473595762101 838488748240075649602697)
                    ·
                      rfl

theorem cell23_4898853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_4898853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898853 prefixEnd_4898853 := by exact prefixLift 4898853
  have htrace : WordTrace (prefixWord ++ tailWord_4898853) baseStart_4898853 baseEnd_4898853 := by
    simpa [prefixWord, tailWord_4898853, baseEnd_4898853] using wordTrace_append hprefix tailTrace_4898853
  have hstable : (prefixWord ++ tailWord_4898853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898853).length < 2 ^ (prefixWord ++ tailWord_4898853).sum := by decide
  have hdescent : baseEnd_4898853 < baseStart_4898853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898917 : List Nat := [1, 3, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_4898917 : Nat := 118140960795 + 4898917 * 2 ^ 59
def prefixEnd_4898917 : Nat := 4983230072969 + 3 ^ 40 * 4898917 * 2
def baseEnd_4898917 : Nat := 838499702494038232802599

theorem tailTrace_4898917 : CollatzResearch.WordTrace tailWord_4898917 prefixEnd_4898917 838499702494038232802599 := by
  unfold tailWord_4898917
  simp only [CollatzResearch.WordTrace]
  refine ⟨178678181993067852258135005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119118787995378568172090003 178678181993067852258135005)
  ·
    refine ⟨67004318247400444596800627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178678181993067852258135005 67004318247400444596800627)
    ·
      refine ⟨100506477371100666895200941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67004318247400444596800627 100506477371100666895200941)
      ·
        refine ⟨37689929014162750085700353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100506477371100666895200941 37689929014162750085700353)
        ·
          refine ⟨28267446760622062564275265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37689929014162750085700353 28267446760622062564275265)
          ·
            refine ⟨21200585070466546923206449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28267446760622062564275265 21200585070466546923206449)
            ·
              refine ⟨15900438802849910192404837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21200585070466546923206449 15900438802849910192404837)
              ·
                refine ⟨2981332275534358161075907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15900438802849910192404837 2981332275534358161075907)
                ·
                  refine ⟨4471998413301537241613861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2981332275534358161075907 4471998413301537241613861)
                  ·
                    refine ⟨838499702494038232802599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4471998413301537241613861 838499702494038232802599)
                    ·
                      rfl

theorem cell23_4898917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_4898917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898917 prefixEnd_4898917 := by exact prefixLift 4898917
  have htrace : WordTrace (prefixWord ++ tailWord_4898917) baseStart_4898917 baseEnd_4898917 := by
    simpa [prefixWord, tailWord_4898917, baseEnd_4898917] using wordTrace_append hprefix tailTrace_4898917
  have hstable : (prefixWord ++ tailWord_4898917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898917).length < 2 ^ (prefixWord ++ tailWord_4898917).sum := by decide
  have hdescent : baseEnd_4898917 < baseStart_4898917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898963 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 4]
def baseStart_4898963 : Nat := 118140960795 + 4898963 * 2 ^ 59
def prefixEnd_4898963 : Nat := 4983230072969 + 3 ^ 40 * 4898963 * 2
def baseEnd_4898963 : Nat := 2515522727592221518432585

theorem tailTrace_4898963 : CollatzResearch.WordTrace tailWord_4898963 prefixEnd_4898963 2515522727592221518432585 := by
  unfold tailWord_4898963
  simp only [CollatzResearch.WordTrace]
  refine ⟨178679859750901202114309543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119119906500600801409539695 178679859750901202114309543)
  ·
    refine ⟨268019789626351803171464315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178679859750901202114309543 268019789626351803171464315)
    ·
      refine ⟨402029684439527704757196473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268019789626351803171464315 402029684439527704757196473)
      ·
        refine ⟨301522263329645778567897355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402029684439527704757196473 301522263329645778567897355)
        ·
          refine ⟨452283394994468667851846033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301522263329645778567897355 452283394994468667851846033)
          ·
            refine ⟨339212546245851500888884525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452283394994468667851846033 339212546245851500888884525)
            ·
              refine ⟨127204704842194312833331697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339212546245851500888884525 127204704842194312833331697)
              ·
                refine ⟨95403528631645734624998773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127204704842194312833331697 95403528631645734624998773)
                ·
                  refine ⟨8944080809216787621093635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95403528631645734624998773 8944080809216787621093635)
                  ·
                    refine ⟨13416121213825181431640453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8944080809216787621093635 13416121213825181431640453)
                    ·
                      refine ⟨2515522727592221518432585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13416121213825181431640453 2515522727592221518432585)
                      ·
                        rfl

theorem cell23_4898963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_4898963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898963 prefixEnd_4898963 := by exact prefixLift 4898963
  have htrace : WordTrace (prefixWord ++ tailWord_4898963) baseStart_4898963 baseEnd_4898963 := by
    simpa [prefixWord, tailWord_4898963, baseEnd_4898963] using wordTrace_append hprefix tailTrace_4898963
  have hstable : (prefixWord ++ tailWord_4898963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898963).length < 2 ^ (prefixWord ++ tailWord_4898963).sum := by decide
  have hdescent : baseEnd_4898963 < baseStart_4898963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899000 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_4899000 : Nat := 118140960795 + 4899000 * 2 ^ 59
def prefixEnd_4899000 : Nat := 4983230072969 + 3 ^ 40 * 4899000 * 2
def baseEnd_4899000 : Nat := 2515541726376437873669915

theorem tailTrace_4899000 : CollatzResearch.WordTrace tailWord_4899000 prefixEnd_4899000 2515541726376437873669915 := by
  unfold tailWord_4899000
  simp only [CollatzResearch.WordTrace]
  refine ⟨89340604625883578716703227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119120806167844771622270969 89340604625883578716703227)
  ·
    refine ⟨134010906938825368075054841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89340604625883578716703227 134010906938825368075054841)
    ·
      refine ⟨100508180204119026056291131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134010906938825368075054841 100508180204119026056291131)
      ·
        refine ⟨150762270306178539084436697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100508180204119026056291131 150762270306178539084436697)
        ·
          refine ⟨113071702729633904313327523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150762270306178539084436697 113071702729633904313327523)
          ·
            refine ⟨169607554094450856469991285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113071702729633904313327523 169607554094450856469991285)
            ·
              refine ⟨15900708196354767794061683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169607554094450856469991285 15900708196354767794061683)
              ·
                refine ⟨23851062294532151691092525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15900708196354767794061683 23851062294532151691092525)
                ·
                  refine ⟨8944148360449556884159697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23851062294532151691092525 8944148360449556884159697)
                  ·
                    refine ⟨6708111270337167663119773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8944148360449556884159697 6708111270337167663119773)
                    ·
                      refine ⟨2515541726376437873669915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6708111270337167663119773 2515541726376437873669915)
                      ·
                        rfl

theorem cell23_4899000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_4899000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899000 prefixEnd_4899000 := by exact prefixLift 4899000
  have htrace : WordTrace (prefixWord ++ tailWord_4899000) baseStart_4899000 baseEnd_4899000 := by
    simpa [prefixWord, tailWord_4899000, baseEnd_4899000] using wordTrace_append hprefix tailTrace_4899000
  have hstable : (prefixWord ++ tailWord_4899000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899000).length < 2 ^ (prefixWord ++ tailWord_4899000).sum := by decide
  have hdescent : baseEnd_4899000 < baseStart_4899000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899020 : List Nat := [2, 2, 1, 6, 1, 11]
def baseStart_4899020 : Nat := 118140960795 + 4899020 * 2 ^ 59
def prefixEnd_4899020 : Nat := 4983230072969 + 3 ^ 40 * 4899020 * 2
def baseEnd_4899020 : Nat := 10352065827117398335061

theorem tailTrace_4899020 : CollatzResearch.WordTrace tailWord_4899020 prefixEnd_4899020 10352065827117398335061 := by
  unfold tailWord_4899020
  simp only [CollatzResearch.WordTrace]
  refine ⟨89340969355847350424567257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119121292474463133899423009 89340969355847350424567257)
  ·
    refine ⟨67005727016885512818425443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89340969355847350424567257 67005727016885512818425443)
    ·
      refine ⟨100508590525328269227638165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67005727016885512818425443 100508590525328269227638165)
      ·
        refine ⟨4711340180874762620045539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100508590525328269227638165 4711340180874762620045539)
        ·
          refine ⟨7067010271312143930068309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4711340180874762620045539 7067010271312143930068309)
          ·
            refine ⟨10352065827117398335061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7067010271312143930068309 10352065827117398335061)
            ·
              rfl

theorem cell23_4899020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 11].length) (baseStart_4899020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899020 prefixEnd_4899020 := by exact prefixLift 4899020
  have htrace : WordTrace (prefixWord ++ tailWord_4899020) baseStart_4899020 baseEnd_4899020 := by
    simpa [prefixWord, tailWord_4899020, baseEnd_4899020] using wordTrace_append hprefix tailTrace_4899020
  have hstable : (prefixWord ++ tailWord_4899020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899020).length < 2 ^ (prefixWord ++ tailWord_4899020).sum := by decide
  have hdescent : baseEnd_4899020 < baseStart_4899020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899033 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 2, 7]
def baseStart_4899033 : Nat := 118140960795 + 4899033 * 2 ^ 59
def prefixEnd_4899033 : Nat := 4983230072969 + 3 ^ 40 * 4899033 * 2
def baseEnd_4899033 : Nat := 838519557079345414852421

theorem tailTrace_4899033 : CollatzResearch.WordTrace tailWord_4899033 prefixEnd_4899033 838519557079345414852421 := by
  unfold tailWord_4899033
  simp only [CollatzResearch.WordTrace]
  refine ⟨178682412860647604069357753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119121608573765069379571835 178682412860647604069357753)
  ·
    refine ⟨134011809645485703052018315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178682412860647604069357753 134011809645485703052018315)
    ·
      refine ⟨201017714468228554578027473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134011809645485703052018315 201017714468228554578027473)
      ·
        refine ⟨150763285851171415933520605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201017714468228554578027473 150763285851171415933520605)
        ·
          refine ⟨56536232194189280975070227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150763285851171415933520605 56536232194189280975070227)
          ·
            refine ⟨84804348291283921462605341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56536232194189280975070227 84804348291283921462605341)
            ·
              refine ⟨31801630609231470548477003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84804348291283921462605341 31801630609231470548477003)
              ·
                refine ⟨47702445913847205822715505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31801630609231470548477003 47702445913847205822715505)
                ·
                  refine ⟨35776834435385404367036629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47702445913847205822715505 35776834435385404367036629)
                  ·
                    refine ⟨838519557079345414852421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35776834435385404367036629 838519557079345414852421)
                    ·
                      rfl

theorem cell23_4899033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_4899033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899033 prefixEnd_4899033 := by exact prefixLift 4899033
  have htrace : WordTrace (prefixWord ++ tailWord_4899033) baseStart_4899033 baseEnd_4899033 := by
    simpa [prefixWord, tailWord_4899033, baseEnd_4899033] using wordTrace_append hprefix tailTrace_4899033
  have hstable : (prefixWord ++ tailWord_4899033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899033).length < 2 ^ (prefixWord ++ tailWord_4899033).sum := by decide
  have hdescent : baseEnd_4899033 < baseStart_4899033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899037 : List Nat := [1, 4, 3, 2, 1, 3, 1, 8]
def baseStart_4899037 : Nat := 118140960795 + 4899037 * 2 ^ 59
def prefixEnd_4899037 : Nat := 4983230072969 + 3 ^ 40 * 4899037 * 2
def baseEnd_4899037 : Nat := 93168915746690897366935

theorem tailTrace_4899037 : CollatzResearch.WordTrace tailWord_4899037 prefixEnd_4899037 93168915746690897366935 := by
  unfold tailWord_4899037
  simp only [CollatzResearch.WordTrace]
  refine ⟨178682558752633112752503365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119121705835088741835002243 178682558752633112752503365)
  ·
    refine ⟨33502979766118708641094381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178682558752633112752503365 33502979766118708641094381)
    ·
      refine ⟨12563617412294515740410393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33502979766118708641094381 12563617412294515740410393)
      ·
        refine ⟨9422713059220886805307795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12563617412294515740410393 9422713059220886805307795)
        ·
          refine ⟨14134069588831330207961693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9422713059220886805307795 14134069588831330207961693)
          ·
            refine ⟨5300276095811748827985635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14134069588831330207961693 5300276095811748827985635)
            ·
              refine ⟨7950414143717623241978453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5300276095811748827985635 7950414143717623241978453)
              ·
                refine ⟨93168915746690897366935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7950414143717623241978453 93168915746690897366935)
                ·
                  rfl

theorem cell23_4899037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 8].length) (baseStart_4899037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899037 prefixEnd_4899037 := by exact prefixLift 4899037
  have htrace : WordTrace (prefixWord ++ tailWord_4899037) baseStart_4899037 baseEnd_4899037 := by
    simpa [prefixWord, tailWord_4899037, baseEnd_4899037] using wordTrace_append hprefix tailTrace_4899037
  have hstable : (prefixWord ++ tailWord_4899037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899037).length < 2 ^ (prefixWord ++ tailWord_4899037).sum := by decide
  have hdescent : baseEnd_4899037 < baseStart_4899037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899047 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4899047 : Nat := 118140960795 + 4899047 * 2 ^ 59
def prefixEnd_4899047 : Nat := 4983230072969 + 3 ^ 40 * 4899047 * 2
def baseEnd_4899047 : Nat := 2515565859967199189782199

theorem tailTrace_4899047 : CollatzResearch.WordTrace tailWord_4899047 prefixEnd_4899047 2515565859967199189782199 := by
  unfold tailWord_4899047
  simp only [CollatzResearch.WordTrace]
  refine ⟨178682923482596884460367395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119121948988397922973578263 178682923482596884460367395)
  ·
    refine ⟨268024385223895326690551093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178682923482596884460367395 268024385223895326690551093)
    ·
      refine ⟨25127286114740186877239165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 268024385223895326690551093 25127286114740186877239165)
      ·
        refine ⟨9422732293027570078964687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25127286114740186877239165 9422732293027570078964687)
        ·
          refine ⟨14134098439541355118447031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9422732293027570078964687 14134098439541355118447031)
          ·
            refine ⟨21201147659312032677670547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14134098439541355118447031 21201147659312032677670547)
            ·
              refine ⟨31801721488968049016505821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21201147659312032677670547 31801721488968049016505821)
              ·
                refine ⟨11925645558363018381189683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31801721488968049016505821 11925645558363018381189683)
                ·
                  refine ⟨17888468337544527571784525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11925645558363018381189683 17888468337544527571784525)
                  ·
                    refine ⟨6708175626579197839419197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17888468337544527571784525 6708175626579197839419197)
                    ·
                      refine ⟨2515565859967199189782199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6708175626579197839419197 2515565859967199189782199)
                      ·
                        rfl

theorem cell23_4899047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4899047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899047 prefixEnd_4899047 := by exact prefixLift 4899047
  have htrace : WordTrace (prefixWord ++ tailWord_4899047) baseStart_4899047 baseEnd_4899047 := by
    simpa [prefixWord, tailWord_4899047, baseEnd_4899047] using wordTrace_append hprefix tailTrace_4899047
  have hstable : (prefixWord ++ tailWord_4899047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899047).length < 2 ^ (prefixWord ++ tailWord_4899047).sum := by decide
  have hdescent : baseEnd_4899047 < baseStart_4899047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899057 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 3, 3, 2]
def baseStart_4899057 : Nat := 118140960795 + 4899057 * 2 ^ 59
def prefixEnd_4899057 : Nat := 4983230072969 + 3 ^ 40 * 4899057 * 2
def baseEnd_4899057 : Nat := 2515570994773744150657153

theorem tailTrace_4899057 : CollatzResearch.WordTrace tailWord_4899057 prefixEnd_4899057 2515570994773744150657153 := by
  unfold tailWord_4899057
  simp only [CollatzResearch.WordTrace]
  refine ⟨178683288212560656168231425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119122192141707104112154283 178683288212560656168231425)
  ·
    refine ⟨134012466159420492126173569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178683288212560656168231425 134012466159420492126173569)
    ·
      refine ⟨100509349619565369094630177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134012466159420492126173569 100509349619565369094630177)
      ·
        refine ⟨75382012214674026820972633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100509349619565369094630177 75382012214674026820972633)
        ·
          refine ⟨56536509161005520115729475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75382012214674026820972633 56536509161005520115729475)
          ·
            refine ⟨84804763741508280173594213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56536509161005520115729475 84804763741508280173594213)
            ·
              refine ⟨15900893201532802532548915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84804763741508280173594213 15900893201532802532548915)
              ·
                refine ⟨23851339802299203798823373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15900893201532802532548915 23851339802299203798823373)
                ·
                  refine ⟨8944252425862201424558765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23851339802299203798823373 8944252425862201424558765)
                  ·
                    refine ⟨3354094659698325534209537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8944252425862201424558765 3354094659698325534209537)
                    ·
                      refine ⟨2515570994773744150657153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354094659698325534209537 2515570994773744150657153)
                      ·
                        rfl

theorem cell23_4899057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_4899057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899057 prefixEnd_4899057 := by exact prefixLift 4899057
  have htrace : WordTrace (prefixWord ++ tailWord_4899057) baseStart_4899057 baseEnd_4899057 := by
    simpa [prefixWord, tailWord_4899057, baseEnd_4899057] using wordTrace_append hprefix tailTrace_4899057
  have hstable : (prefixWord ++ tailWord_4899057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899057).length < 2 ^ (prefixWord ++ tailWord_4899057).sum := by decide
  have hdescent : baseEnd_4899057 < baseStart_4899057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899063 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 6, 6]
def baseStart_4899063 : Nat := 118140960795 + 4899063 * 2 ^ 59
def prefixEnd_4899063 : Nat := 4983230072969 + 3 ^ 40 * 4899063 * 2
def baseEnd_4899063 : Nat := 838524691885890375727375

theorem tailTrace_4899063 : CollatzResearch.WordTrace tailWord_4899063 prefixEnd_4899063 838524691885890375727375 := by
  unfold tailWord_4899063
  simp only [CollatzResearch.WordTrace]
  refine ⟨178683507050538919192949843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119122338033692612795299895 178683507050538919192949843)
  ·
    refine ⟨268025260575808378789424765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178683507050538919192949843 268025260575808378789424765)
    ·
      refine ⟨100509472715928142046034287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268025260575808378789424765 100509472715928142046034287)
      ·
        refine ⟨150764209073892213069051431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100509472715928142046034287 150764209073892213069051431)
        ·
          refine ⟨226146313610838319603577147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150764209073892213069051431 226146313610838319603577147)
          ·
            refine ⟨339219470416257479405365721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226146313610838319603577147 339219470416257479405365721)
            ·
              refine ⟨254414602812193109554024291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339219470416257479405365721 254414602812193109554024291)
              ·
                refine ⟨381621904218289664331036437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254414602812193109554024291 381621904218289664331036437)
                ·
                  refine ⟨17888526760232328015517333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 381621904218289664331036437 17888526760232328015517333)
                  ·
                    refine ⟨838524691885890375727375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17888526760232328015517333 838524691885890375727375)
                    ·
                      rfl

theorem cell23_4899063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_4899063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899063 prefixEnd_4899063 := by exact prefixLift 4899063
  have htrace : WordTrace (prefixWord ++ tailWord_4899063) baseStart_4899063 baseEnd_4899063 := by
    simpa [prefixWord, tailWord_4899063, baseEnd_4899063] using wordTrace_append hprefix tailTrace_4899063
  have hstable : (prefixWord ++ tailWord_4899063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899063).length < 2 ^ (prefixWord ++ tailWord_4899063).sum := by decide
  have hdescent : baseEnd_4899063 < baseStart_4899063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899080 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 2, 6]
def baseStart_4899080 : Nat := 118140960795 + 4899080 * 2 ^ 59
def prefixEnd_4899080 : Nat := 4983230072969 + 3 ^ 40 * 4899080 * 2
def baseEnd_4899080 : Nat := 838527601609599186889849

theorem tailTrace_4899080 : CollatzResearch.WordTrace tailWord_4899080 prefixEnd_4899080 838527601609599186889849 := by
  unfold tailWord_4899080
  simp only [CollatzResearch.WordTrace]
  refine ⟨89342063545738665548159347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119122751394318220730879129 89342063545738665548159347)
  ·
    refine ⟨134013095318607998322239021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89342063545738665548159347 134013095318607998322239021)
    ·
      refine ⟨50254910744477999370839633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134013095318607998322239021 50254910744477999370839633)
      ·
        refine ⟨37691183058358499528129725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50254910744477999370839633 37691183058358499528129725)
        ·
          refine ⟨14134193646884437323048647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37691183058358499528129725 14134193646884437323048647)
          ·
            refine ⟨21201290470326655984572971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14134193646884437323048647 21201290470326655984572971)
            ·
              refine ⟨31801935705489983976859457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21201290470326655984572971 31801935705489983976859457)
              ·
                refine ⟨23851451779117487982644593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31801935705489983976859457 23851451779117487982644593)
                ·
                  refine ⟨17888588834338115986983445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23851451779117487982644593 17888588834338115986983445)
                  ·
                    refine ⟨838527601609599186889849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17888588834338115986983445 838527601609599186889849)
                    ·
                      rfl

theorem cell23_4899080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_4899080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899080 prefixEnd_4899080 := by exact prefixLift 4899080
  have htrace : WordTrace (prefixWord ++ tailWord_4899080) baseStart_4899080 baseEnd_4899080 := by
    simpa [prefixWord, tailWord_4899080, baseEnd_4899080] using wordTrace_append hprefix tailTrace_4899080
  have hstable : (prefixWord ++ tailWord_4899080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899080).length < 2 ^ (prefixWord ++ tailWord_4899080).sum := by decide
  have hdescent : baseEnd_4899080 < baseStart_4899080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899104 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 1, 4, 2]
def baseStart_4899104 : Nat := 118140960795 + 4899104 * 2 ^ 59
def prefixEnd_4899104 : Nat := 4983230072969 + 3 ^ 40 * 4899104 * 2
def baseEnd_4899104 : Nat := 2515595128364505466769437

theorem tailTrace_4899104 : CollatzResearch.WordTrace tailWord_4899104 prefixEnd_4899104 2515595128364505466769437 := by
  unfold tailWord_4899104
  simp only [CollatzResearch.WordTrace]
  refine ⟨89342501221695191597596183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119123334962260255463461577 89342501221695191597596183)
  ·
    refine ⟨134013751832542787396394275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89342501221695191597596183 134013751832542787396394275)
    ·
      refine ⟨201020627748814181094591413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134013751832542787396394275 201020627748814181094591413)
      ·
        refine ⟨18845683851451329477617945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201020627748814181094591413 18845683851451329477617945)
        ·
          refine ⟨14134262888588497108213459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18845683851451329477617945 14134262888588497108213459)
          ·
            refine ⟨21201394332882745662320189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14134262888588497108213459 21201394332882745662320189)
            ·
              refine ⟨7950522874831029623370071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21201394332882745662320189 7950522874831029623370071)
              ·
                refine ⟨11925784312246544435055107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950522874831029623370071 11925784312246544435055107)
                ·
                  refine ⟨17888676468369816652582661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11925784312246544435055107 17888676468369816652582661)
                  ·
                    refine ⟨3354126837819340622359249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17888676468369816652582661 3354126837819340622359249)
                    ·
                      refine ⟨2515595128364505466769437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354126837819340622359249 2515595128364505466769437)
                      ·
                        rfl

theorem cell23_4899104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_4899104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899104 prefixEnd_4899104 := by exact prefixLift 4899104
  have htrace : WordTrace (prefixWord ++ tailWord_4899104) baseStart_4899104 baseEnd_4899104 := by
    simpa [prefixWord, tailWord_4899104, baseEnd_4899104] using wordTrace_append hprefix tailTrace_4899104
  have hstable : (prefixWord ++ tailWord_4899104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899104).length < 2 ^ (prefixWord ++ tailWord_4899104).sum := by decide
  have hdescent : baseEnd_4899104 < baseStart_4899104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899120 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 3]
def baseStart_4899120 : Nat := 118140960795 + 4899120 * 2 ^ 59
def prefixEnd_4899120 : Nat := 4983230072969 + 3 ^ 40 * 4899120 * 2
def baseEnd_4899120 : Nat := 2515603344054977404169363

theorem tailTrace_4899120 : CollatzResearch.WordTrace tailWord_4899120 prefixEnd_4899120 2515603344054977404169363 := by
  unfold tailWord_4899120
  simp only [CollatzResearch.WordTrace]
  refine ⟨89342793005666208963887407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119123724007554945285183209 89342793005666208963887407)
  ·
    refine ⟨134014189508499313445831111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89342793005666208963887407 134014189508499313445831111)
    ·
      refine ⟨201021284262748970168746667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134014189508499313445831111 201021284262748970168746667)
      ·
        refine ⟨301531926394123455253120001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201021284262748970168746667 301531926394123455253120001)
        ·
          refine ⟨226148944795592591439840001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301531926394123455253120001 226148944795592591439840001)
          ·
            refine ⟨169611708596694443579880001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226148944795592591439840001 169611708596694443579880001)
            ·
              refine ⟨127208781447520832684910001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169611708596694443579880001 127208781447520832684910001)
              ·
                refine ⟨95406586085640624513682501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127208781447520832684910001 95406586085640624513682501)
                ·
                  refine ⟨17888734891057617096315469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95406586085640624513682501 17888734891057617096315469)
                  ·
                    refine ⟨6708275584146606411118301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17888734891057617096315469 6708275584146606411118301)
                    ·
                      refine ⟨2515603344054977404169363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6708275584146606411118301 2515603344054977404169363)
                      ·
                        rfl

theorem cell23_4899120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_4899120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899120 prefixEnd_4899120 := by exact prefixLift 4899120
  have htrace : WordTrace (prefixWord ++ tailWord_4899120) baseStart_4899120 baseEnd_4899120 := by
    simpa [prefixWord, tailWord_4899120, baseEnd_4899120] using wordTrace_append hprefix tailTrace_4899120
  have hstable : (prefixWord ++ tailWord_4899120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899120).length < 2 ^ (prefixWord ++ tailWord_4899120).sum := by decide
  have hdescent : baseEnd_4899120 < baseStart_4899120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899160 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_4899160 : Nat := 118140960795 + 4899160 * 2 ^ 59
def prefixEnd_4899160 : Nat := 4983230072969 + 3 ^ 40 * 4899160 * 2
def baseEnd_4899160 : Nat := 2515623883281157247669179

theorem tailTrace_4899160 : CollatzResearch.WordTrace tailWord_4899160 prefixEnd_4899160 2515623883281157247669179 := by
  unfold tailWord_4899160
  simp only [CollatzResearch.WordTrace]
  refine ⟨89343522465593752379615467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119124696620791669839487289 89343522465593752379615467)
  ·
    refine ⟨134015283698390628569423201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89343522465593752379615467 134015283698390628569423201)
    ·
      refine ⟨100511462773792971427067401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134015283698390628569423201 100511462773792971427067401)
      ·
        refine ⟨75383597080344728570300551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100511462773792971427067401 75383597080344728570300551)
        ·
          refine ⟨113075395620517092855450827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75383597080344728570300551 113075395620517092855450827)
          ·
            refine ⟨169613093430775639283176241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113075395620517092855450827 169613093430775639283176241)
            ·
              refine ⟨127209820073081729462382181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169613093430775639283176241 127209820073081729462382181)
              ·
                refine ⟨23851841263702824274196659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127209820073081729462382181 23851841263702824274196659)
                ·
                  refine ⟨35777761895554236411294989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23851841263702824274196659 35777761895554236411294989)
                  ·
                    refine ⟨13416660710832838654235621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35777761895554236411294989 13416660710832838654235621)
                    ·
                      refine ⟨2515623883281157247669179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13416660710832838654235621 2515623883281157247669179)
                      ·
                        rfl

theorem cell23_4899160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_4899160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899160 prefixEnd_4899160 := by exact prefixLift 4899160
  have htrace : WordTrace (prefixWord ++ tailWord_4899160) baseStart_4899160 baseEnd_4899160 := by
    simpa [prefixWord, tailWord_4899160, baseEnd_4899160] using wordTrace_append hprefix tailTrace_4899160
  have hstable : (prefixWord ++ tailWord_4899160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899160).length < 2 ^ (prefixWord ++ tailWord_4899160).sum := by decide
  have hdescent : baseEnd_4899160 < baseStart_4899160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899177 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 4]
def baseStart_4899177 : Nat := 118140960795 + 4899177 * 2 ^ 59
def prefixEnd_4899177 : Nat := 4983230072969 + 3 ^ 40 * 4899177 * 2
def baseEnd_4899177 : Nat := 2515632612452283681156601

theorem tailTrace_4899177 : CollatzResearch.WordTrace tailWord_4899177 prefixEnd_4899177 2515632612452283681156601 := by
  unfold tailWord_4899177
  simp only [CollatzResearch.WordTrace]
  refine ⟨178687664972125916662599785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119125109981417277775066523 178687664972125916662599785)
  ·
    refine ⟨134015748729094437496949839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178687664972125916662599785 134015748729094437496949839)
    ·
      refine ⟨201023623093641656245424759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134015748729094437496949839 201023623093641656245424759)
      ·
        refine ⟨301535434640462484368137139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201023623093641656245424759 301535434640462484368137139)
        ·
          refine ⟨452303151960693726552205709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301535434640462484368137139 452303151960693726552205709)
          ·
            refine ⟨169613681985260147457077141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 452303151960693726552205709 169613681985260147457077141)
            ·
              refine ⟨7950641343059069412050491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169613681985260147457077141 7950641343059069412050491)
              ·
                refine ⟨11925962014588604118075737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950641343059069412050491 11925962014588604118075737)
                ·
                  refine ⟨8944471510941453088556803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11925962014588604118075737 8944471510941453088556803)
                  ·
                    refine ⟨13416707266412179632835205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8944471510941453088556803 13416707266412179632835205)
                    ·
                      refine ⟨2515632612452283681156601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13416707266412179632835205 2515632612452283681156601)
                      ·
                        rfl

theorem cell23_4899177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_4899177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899177 prefixEnd_4899177 := by exact prefixLift 4899177
  have htrace : WordTrace (prefixWord ++ tailWord_4899177) baseStart_4899177 baseEnd_4899177 := by
    simpa [prefixWord, tailWord_4899177, baseEnd_4899177] using wordTrace_append hprefix tailTrace_4899177
  have hstable : (prefixWord ++ tailWord_4899177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899177).length < 2 ^ (prefixWord ++ tailWord_4899177).sum := by decide
  have hdescent : baseEnd_4899177 < baseStart_4899177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899261 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_4899261 : Nat := 118140960795 + 4899261 * 2 ^ 59
def prefixEnd_4899261 : Nat := 4983230072969 + 3 ^ 40 * 4899261 * 2
def baseEnd_4899261 : Nat := 2515675744827261352506215

theorem tailTrace_4899261 : CollatzResearch.WordTrace tailWord_4899261 prefixEnd_4899261 2515675744827261352506215 := by
  unfold tailWord_4899261
  simp only [CollatzResearch.WordTrace]
  refine ⟨178690728703821599008657637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119127152469214399339105091 178690728703821599008657637)
  ·
    refine ⟨33504511631966549814123307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178690728703821599008657637 33504511631966549814123307)
    ·
      refine ⟨50256767447949824721184961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33504511631966549814123307 50256767447949824721184961)
      ·
        refine ⟨37692575585962368540888721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50256767447949824721184961 37692575585962368540888721)
        ·
          refine ⟨28269431689471776405666541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37692575585962368540888721 28269431689471776405666541)
          ·
            refine ⟨10601036883551916152124953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28269431689471776405666541 10601036883551916152124953)
            ·
              refine ⟨7950777662663937114093715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10601036883551916152124953 7950777662663937114093715)
              ·
                refine ⟨11926166493995905671140573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950777662663937114093715 11926166493995905671140573)
                ·
                  refine ⟨4472312435248464626677715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11926166493995905671140573 4472312435248464626677715)
                  ·
                    refine ⟨6708468652872696940016573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4472312435248464626677715 6708468652872696940016573)
                    ·
                      refine ⟨2515675744827261352506215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6708468652872696940016573 2515675744827261352506215)
                      ·
                        rfl

theorem cell23_4899261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_4899261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899261 prefixEnd_4899261 := by exact prefixLift 4899261
  have htrace : WordTrace (prefixWord ++ tailWord_4899261) baseStart_4899261 baseEnd_4899261 := by
    simpa [prefixWord, tailWord_4899261, baseEnd_4899261] using wordTrace_append hprefix tailTrace_4899261
  have hstable : (prefixWord ++ tailWord_4899261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899261).length < 2 ^ (prefixWord ++ tailWord_4899261).sum := by decide
  have hdescent : baseEnd_4899261 < baseStart_4899261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899297 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_4899297 : Nat := 118140960795 + 4899297 * 2 ^ 59
def prefixEnd_4899297 : Nat := 4983230072969 + 3 ^ 40 * 4899297 * 2
def baseEnd_4899297 : Nat := 2515694230130823211656049

theorem tailTrace_4899297 : CollatzResearch.WordTrace tailWord_4899297 prefixEnd_4899297 2515694230130823211656049 := by
  unfold tailWord_4899297
  simp only [CollatzResearch.WordTrace]
  refine ⟨178692041731691177156968145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119128027821127451437978763 178692041731691177156968145)
  ·
    refine ⟨134019031298768382867726109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178692041731691177156968145 134019031298768382867726109)
    ·
      refine ⟨50257136737038143575397291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134019031298768382867726109 50257136737038143575397291)
      ·
        refine ⟨75385705105557215363095937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50257136737038143575397291 75385705105557215363095937)
        ·
          refine ⟨56539278829167911522321953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75385705105557215363095937 56539278829167911522321953)
          ·
            refine ⟨42404459121875933641741465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56539278829167911522321953 42404459121875933641741465)
            ·
              refine ⟨31803344341406950231306099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42404459121875933641741465 31803344341406950231306099)
              ·
                refine ⟨47705016512110425346959149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31803344341406950231306099 47705016512110425346959149)
                ·
                  refine ⟨17889381192041409505109681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47705016512110425346959149 17889381192041409505109681)
                  ·
                    refine ⟨13417035894031057128832261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17889381192041409505109681 13417035894031057128832261)
                    ·
                      refine ⟨2515694230130823211656049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13417035894031057128832261 2515694230130823211656049)
                      ·
                        rfl

theorem cell23_4899297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_4899297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899297 prefixEnd_4899297 := by exact prefixLift 4899297
  have htrace : WordTrace (prefixWord ++ tailWord_4899297) baseStart_4899297 baseEnd_4899297 := by
    simpa [prefixWord, tailWord_4899297, baseEnd_4899297] using wordTrace_append hprefix tailTrace_4899297
  have hstable : (prefixWord ++ tailWord_4899297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899297).length < 2 ^ (prefixWord ++ tailWord_4899297).sum := by decide
  have hdescent : baseEnd_4899297 < baseStart_4899297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899304 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_4899304 : Nat := 118140960795 + 4899304 * 2 ^ 59
def prefixEnd_4899304 : Nat := 4983230072969 + 3 ^ 40 * 4899304 * 2
def baseEnd_4899304 : Nat := 2515697824495404684268517

theorem tailTrace_4899304 : CollatzResearch.WordTrace tailWord_4899304 prefixEnd_4899304 2515697824495404684268517 := by
  unfold tailWord_4899304
  simp only [CollatzResearch.WordTrace]
  refine ⟨89346148521332908676236483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119128198028443878234981977 89346148521332908676236483)
  ·
    refine ⟨134019222781999363014354725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89346148521332908676236483 134019222781999363014354725)
    ·
      refine ⟨25128604271624880565191511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134019222781999363014354725 25128604271624880565191511)
      ·
        refine ⟨37692906407437320847787267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25128604271624880565191511 37692906407437320847787267)
        ·
          refine ⟨56539359611155981271680901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37692906407437320847787267 56539359611155981271680901)
          ·
            refine ⟨10601129927091746488440169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56539359611155981271680901 10601129927091746488440169)
            ·
              refine ⟨7950847445318809866330127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10601129927091746488440169 7950847445318809866330127)
              ·
                refine ⟨11926271167978214799495191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950847445318809866330127 11926271167978214799495191)
                ·
                  refine ⟨17889406751967322199242787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11926271167978214799495191 17889406751967322199242787)
                  ·
                    refine ⟨26834110127950983298864181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17889406751967322199242787 26834110127950983298864181)
                    ·
                      refine ⟨2515697824495404684268517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26834110127950983298864181 2515697824495404684268517)
                      ·
                        rfl

theorem cell23_4899304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_4899304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899304 prefixEnd_4899304 := by exact prefixLift 4899304
  have htrace : WordTrace (prefixWord ++ tailWord_4899304) baseStart_4899304 baseEnd_4899304 := by
    simpa [prefixWord, tailWord_4899304, baseEnd_4899304] using wordTrace_append hprefix tailTrace_4899304
  have hstable : (prefixWord ++ tailWord_4899304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899304).length < 2 ^ (prefixWord ++ tailWord_4899304).sum := by decide
  have hdescent : baseEnd_4899304 < baseStart_4899304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899341 : List Nat := [1, 7, 1, 1, 1, 1, 2, 9]
def baseStart_4899341 : Nat := 118140960795 + 4899341 * 2 ^ 59
def prefixEnd_4899341 : Nat := 4983230072969 + 3 ^ 40 * 4899341 * 2
def baseEnd_4899341 : Nat := 93174697158504482944661

theorem tailTrace_4899341 : CollatzResearch.WordTrace tailWord_4899341 prefixEnd_4899341 93174697158504482944661 := by
  unfold tailWord_4899341
  simp only [CollatzResearch.WordTrace]
  refine ⟨178693646543531772671569877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119129097695687848447713251 178693646543531772671569877)
  ·
    refine ⟨4188132340864025921989919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 178693646543531772671569877 4188132340864025921989919)
    ·
      refine ⟨6282198511296038882984879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4188132340864025921989919 6282198511296038882984879)
      ·
        refine ⟨9423297766944058324477319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282198511296038882984879 9423297766944058324477319)
        ·
          refine ⟨14134946650416087486715979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9423297766944058324477319 14134946650416087486715979)
          ·
            refine ⟨21202419975624131230073969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14134946650416087486715979 21202419975624131230073969)
            ·
              refine ⟨15901814981718098422555477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21202419975624131230073969 15901814981718098422555477)
              ·
                refine ⟨93174697158504482944661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15901814981718098422555477 93174697158504482944661)
                ·
                  rfl

theorem cell23_4899341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 9].length) (baseStart_4899341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899341 prefixEnd_4899341 := by exact prefixLift 4899341
  have htrace : WordTrace (prefixWord ++ tailWord_4899341) baseStart_4899341 baseEnd_4899341 := by
    simpa [prefixWord, tailWord_4899341, baseEnd_4899341] using wordTrace_append hprefix tailTrace_4899341
  have hstable : (prefixWord ++ tailWord_4899341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899341).length < 2 ^ (prefixWord ++ tailWord_4899341).sum := by decide
  have hdescent : baseEnd_4899341 < baseStart_4899341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899368 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4899368 : Nat := 118140960795 + 4899368 * 2 ^ 59
def prefixEnd_4899368 : Nat := 4983230072969 + 3 ^ 40 * 4899368 * 2
def baseEnd_4899368 : Nat := 2515730687257292433868223

theorem tailTrace_4899368 : CollatzResearch.WordTrace tailWord_4899368 prefixEnd_4899368 2515730687257292433868223 := by
  unfold tailWord_4899368
  simp only [CollatzResearch.WordTrace]
  refine ⟨89347315657216978141401379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119129754209622637521868505 89347315657216978141401379)
  ·
    refine ⟨134020973485825467212102069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89347315657216978141401379 134020973485825467212102069)
    ·
      refine ⟨12564466264296137551134569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134020973485825467212102069 12564466264296137551134569)
      ·
        refine ⟨9423349698222103163350927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12564466264296137551134569 9423349698222103163350927)
        ·
          refine ⟨14135024547333154745026391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9423349698222103163350927 14135024547333154745026391)
          ·
            refine ⟨21202536820999732117539587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14135024547333154745026391 21202536820999732117539587)
            ·
              refine ⟨31803805231499598176309381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21202536820999732117539587 31803805231499598176309381)
              ·
                refine ⟨5963213480906174658058009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31803805231499598176309381 5963213480906174658058009)
                ·
                  refine ⟨4472410110679630993543507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5963213480906174658058009 4472410110679630993543507)
                  ·
                    refine ⟨6708615166019446490315261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4472410110679630993543507 6708615166019446490315261)
                    ·
                      refine ⟨2515730687257292433868223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6708615166019446490315261 2515730687257292433868223)
                      ·
                        rfl

theorem cell23_4899368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4899368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899368 prefixEnd_4899368 := by exact prefixLift 4899368
  have htrace : WordTrace (prefixWord ++ tailWord_4899368) baseStart_4899368 baseEnd_4899368 := by
    simpa [prefixWord, tailWord_4899368, baseEnd_4899368] using wordTrace_append hprefix tailTrace_4899368
  have hstable : (prefixWord ++ tailWord_4899368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899368).length < 2 ^ (prefixWord ++ tailWord_4899368).sum := by decide
  have hdescent : baseEnd_4899368 < baseStart_4899368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899377 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_4899377 : Nat := 118140960795 + 4899377 * 2 ^ 59
def prefixEnd_4899377 : Nat := 4983230072969 + 3 ^ 40 * 4899377 * 2
def baseEnd_4899377 : Nat := 2515735308583182898655681

theorem tailTrace_4899377 : CollatzResearch.WordTrace tailWord_4899377 prefixEnd_4899377 2515735308583182898655681 := by
  unfold tailWord_4899377
  simp only [CollatzResearch.WordTrace]
  refine ⟨178694959571401350819880385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119129973047600900546586923 178694959571401350819880385)
  ·
    refine ⟨134021219678551013114910289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178694959571401350819880385 134021219678551013114910289)
    ·
      refine ⟨100515914758913259836182717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134021219678551013114910289 100515914758913259836182717)
      ·
        refine ⟨37693468034592472438568519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100515914758913259836182717 37693468034592472438568519)
        ·
          refine ⟨56540202051888708657852779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37693468034592472438568519 56540202051888708657852779)
          ·
            refine ⟨84810303077833062986779169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56540202051888708657852779 84810303077833062986779169)
            ·
              refine ⟨63607727308374797240084377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84810303077833062986779169 63607727308374797240084377)
              ·
                refine ⟨47705795481281097930063283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63607727308374797240084377 47705795481281097930063283)
                ·
                  refine ⟨71558693221921646895094925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47705795481281097930063283 71558693221921646895094925)
                  ·
                    refine ⟨26834509958220617585660597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71558693221921646895094925 26834509958220617585660597)
                    ·
                      refine ⟨2515735308583182898655681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26834509958220617585660597 2515735308583182898655681)
                      ·
                        rfl

theorem cell23_4899377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_4899377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899377 prefixEnd_4899377 := by exact prefixLift 4899377
  have htrace : WordTrace (prefixWord ++ tailWord_4899377) baseStart_4899377 baseEnd_4899377 := by
    simpa [prefixWord, tailWord_4899377, baseEnd_4899377] using wordTrace_append hprefix tailTrace_4899377
  have hstable : (prefixWord ++ tailWord_4899377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899377).length < 2 ^ (prefixWord ++ tailWord_4899377).sum := by decide
  have hdescent : baseEnd_4899377 < baseStart_4899377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899391 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 1, 4, 2]
def baseStart_4899391 : Nat := 118140960795 + 4899391 * 2 ^ 59
def prefixEnd_4899391 : Nat := 4983230072969 + 3 ^ 40 * 4899391 * 2
def baseEnd_4899391 : Nat := 2515742497312345843880617

theorem tailTrace_4899391 : CollatzResearch.WordTrace tailWord_4899391 prefixEnd_4899391 2515742497312345843880617 := by
  unfold tailWord_4899391
  simp only [CollatzResearch.WordTrace]
  refine ⟨178695470193350631210890027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119130313462233754140593351 178695470193350631210890027)
  ·
    refine ⟨268043205290025946816335041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178695470193350631210890027 268043205290025946816335041)
    ·
      refine ⟨201032403967519460112251281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268043205290025946816335041 201032403967519460112251281)
      ·
        refine ⟨150774302975639595084188461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201032403967519460112251281 150774302975639595084188461)
        ·
          refine ⟨56540363615864848156570673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150774302975639595084188461 56540363615864848156570673)
          ·
            refine ⟨42405272711898636117428005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56540363615864848156570673 42405272711898636117428005)
            ·
              refine ⟨7950988633480994272017751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42405272711898636117428005 7950988633480994272017751)
              ·
                refine ⟨11926482950221491408026627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950988633480994272017751 11926482950221491408026627)
                ·
                  refine ⟨17889724425332237112039941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11926482950221491408026627 17889724425332237112039941)
                  ·
                    refine ⟨3354323329749794458507489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17889724425332237112039941 3354323329749794458507489)
                    ·
                      refine ⟨2515742497312345843880617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354323329749794458507489 2515742497312345843880617)
                      ·
                        rfl

theorem cell23_4899391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_4899391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899391 prefixEnd_4899391 := by exact prefixLift 4899391
  have htrace : WordTrace (prefixWord ++ tailWord_4899391) baseStart_4899391 baseEnd_4899391 := by
    simpa [prefixWord, tailWord_4899391, baseEnd_4899391] using wordTrace_append hprefix tailTrace_4899391
  have hstable : (prefixWord ++ tailWord_4899391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899391).length < 2 ^ (prefixWord ++ tailWord_4899391).sum := by decide
  have hdescent : baseEnd_4899391 < baseStart_4899391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899397 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 9]
def baseStart_4899397 : Nat := 118140960795 + 4899397 * 2 ^ 59
def prefixEnd_4899397 : Nat := 4983230072969 + 3 ^ 40 * 4899397 * 2
def baseEnd_4899397 : Nat := 279527286466252535600621

theorem tailTrace_4899397 : CollatzResearch.WordTrace tailWord_4899397 prefixEnd_4899397 279527286466252535600621 := by
  unfold tailWord_4899397
  simp only [CollatzResearch.WordTrace]
  refine ⟨178695689031328894235608445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119130459354219262823738963 178695689031328894235608445)
  ·
    refine ⟨67010883386748335338353167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178695689031328894235608445 67010883386748335338353167)
    ·
      refine ⟨100516325080122503007529751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67010883386748335338353167 100516325080122503007529751)
      ·
        refine ⟨150774487620183754511294627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100516325080122503007529751 150774487620183754511294627)
        ·
          refine ⟨226161731430275631766941941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150774487620183754511294627 226161731430275631766941941)
          ·
            refine ⟨21202662321588340478150807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 226161731430275631766941941 21202662321588340478150807)
            ·
              refine ⟨31803993482382510717226211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21202662321588340478150807 31803993482382510717226211)
              ·
                refine ⟨47705990223573766075839317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31803993482382510717226211 47705990223573766075839317)
                ·
                  refine ⟨279527286466252535600621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47705990223573766075839317 279527286466252535600621)
                  ·
                    rfl

theorem cell23_4899397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_4899397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899397 prefixEnd_4899397 := by exact prefixLift 4899397
  have htrace : WordTrace (prefixWord ++ tailWord_4899397) baseStart_4899397 baseEnd_4899397 := by
    simpa [prefixWord, tailWord_4899397, baseEnd_4899397] using wordTrace_append hprefix tailTrace_4899397
  have hstable : (prefixWord ++ tailWord_4899397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899397).length < 2 ^ (prefixWord ++ tailWord_4899397).sum := by decide
  have hdescent : baseEnd_4899397 < baseStart_4899397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899424 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 3]
def baseStart_4899424 : Nat := 118140960795 + 4899424 * 2 ^ 59
def prefixEnd_4899424 : Nat := 4983230072969 + 3 ^ 40 * 4899424 * 2
def baseEnd_4899424 : Nat := 2515759442173944214767965

theorem tailTrace_4899424 : CollatzResearch.WordTrace tailWord_4899424 prefixEnd_4899424 2515759442173944214767965 := by
  unfold tailWord_4899424
  simp only [CollatzResearch.WordTrace]
  refine ⟨89348336901115538923420663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119131115868154051897894217 89348336901115538923420663)
  ·
    refine ⟨134022505351673308385130995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89348336901115538923420663 134022505351673308385130995)
    ·
      refine ⟨201033758027509962577696493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134022505351673308385130995 201033758027509962577696493)
      ·
        refine ⟨75387659260316235966636185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201033758027509962577696493 75387659260316235966636185)
        ·
          refine ⟨56540744445237176974977139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75387659260316235966636185 56540744445237176974977139)
          ·
            refine ⟨84811116667855765462465709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56540744445237176974977139 84811116667855765462465709)
            ·
              refine ⟨31804168750445912048424641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84811116667855765462465709 31804168750445912048424641)
              ·
                refine ⟨23853126562834434036318481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31804168750445912048424641 23853126562834434036318481)
                ·
                  refine ⟨17889844922125825527238861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23853126562834434036318481 17889844922125825527238861)
                  ·
                    refine ⟨6708691845797184572714573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17889844922125825527238861 6708691845797184572714573)
                    ·
                      refine ⟨2515759442173944214767965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6708691845797184572714573 2515759442173944214767965)
                      ·
                        rfl

theorem cell23_4899424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_4899424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899424 prefixEnd_4899424 := by exact prefixLift 4899424
  have htrace : WordTrace (prefixWord ++ tailWord_4899424) baseStart_4899424 baseEnd_4899424 := by
    simpa [prefixWord, tailWord_4899424, baseEnd_4899424] using wordTrace_append hprefix tailTrace_4899424
  have hstable : (prefixWord ++ tailWord_4899424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899424).length < 2 ^ (prefixWord ++ tailWord_4899424).sum := by decide
  have hdescent : baseEnd_4899424 < baseStart_4899424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899425 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_4899425 : Nat := 118140960795 + 4899425 * 2 ^ 59
def prefixEnd_4899425 : Nat := 4983230072969 + 3 ^ 40 * 4899425 * 2
def baseEnd_4899425 : Nat := 2515759955654598710855461

theorem tailTrace_4899425 : CollatzResearch.WordTrace tailWord_4899425 prefixEnd_4899425 2515759955654598710855461 := by
  unfold tailWord_4899425
  simp only [CollatzResearch.WordTrace]
  refine ⟨178696710275227455017627729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119131140183484970011751819 178696710275227455017627729)
  ·
    refine ⟨134022532706420591263220797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178696710275227455017627729 134022532706420591263220797)
    ·
      refine ⟨50258449764907721723707799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134022532706420591263220797 50258449764907721723707799)
      ·
        refine ⟨75387674647361582585561699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50258449764907721723707799 75387674647361582585561699)
        ·
          refine ⟨113081511971042373878342549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75387674647361582585561699 113081511971042373878342549)
          ·
            refine ⟨5300695873642611275547307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113081511971042373878342549 5300695873642611275547307)
            ·
              refine ⟨7951043810463916913320961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5300695873642611275547307 7951043810463916913320961)
              ·
                refine ⟨5963282857847937684990721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7951043810463916913320961 5963282857847937684990721)
                ·
                  refine ⟨4472462143385953263743041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5963282857847937684990721 4472462143385953263743041)
                  ·
                    refine ⟨3354346607539464947807281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4472462143385953263743041 3354346607539464947807281)
                    ·
                      refine ⟨2515759955654598710855461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354346607539464947807281 2515759955654598710855461)
                      ·
                        rfl

theorem cell23_4899425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_4899425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899425 prefixEnd_4899425 := by exact prefixLift 4899425
  have htrace : WordTrace (prefixWord ++ tailWord_4899425) baseStart_4899425 baseEnd_4899425 := by
    simpa [prefixWord, tailWord_4899425, baseEnd_4899425] using wordTrace_append hprefix tailTrace_4899425
  have hstable : (prefixWord ++ tailWord_4899425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899425).length < 2 ^ (prefixWord ++ tailWord_4899425).sum := by decide
  have hdescent : baseEnd_4899425 < baseStart_4899425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899442 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_4899442 : Nat := 118140960795 + 4899442 * 2 ^ 59
def prefixEnd_4899442 : Nat := 4983230072969 + 3 ^ 40 * 4899442 * 2
def baseEnd_4899442 : Nat := 2515768684825725144342883

theorem tailTrace_4899442 : CollatzResearch.WordTrace tailWord_4899442 prefixEnd_4899442 2515768684825725144342883 := by
  unfold tailWord_4899442
  simp only [CollatzResearch.WordTrace]
  refine ⟨44674332579041466730249145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119131553544110577947331053 44674332579041466730249145)
  ·
    refine ⟨33505749434281100047686859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44674332579041466730249145 33505749434281100047686859)
    ·
      refine ⟨50258624151421650071530289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33505749434281100047686859 50258624151421650071530289)
      ·
        refine ⟨37693968113566237553647717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50258624151421650071530289 37693968113566237553647717)
        ·
          refine ⟨7067619021293669541308947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37693968113566237553647717 7067619021293669541308947)
          ·
            refine ⟨10601428531940504311963421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7067619021293669541308947 10601428531940504311963421)
            ·
              refine ⟨3975535699477689116986283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10601428531940504311963421 3975535699477689116986283)
              ·
                refine ⟨5963303549216533675479425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975535699477689116986283 5963303549216533675479425)
                ·
                  refine ⟨4472477661912400256609569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5963303549216533675479425 4472477661912400256609569)
                  ·
                    refine ⟨3354358246434300192457177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4472477661912400256609569 3354358246434300192457177)
                    ·
                      refine ⟨2515768684825725144342883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354358246434300192457177 2515768684825725144342883)
                      ·
                        rfl

theorem cell23_4899442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_4899442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899442 prefixEnd_4899442 := by exact prefixLift 4899442
  have htrace : WordTrace (prefixWord ++ tailWord_4899442) baseStart_4899442 baseEnd_4899442 := by
    simpa [prefixWord, tailWord_4899442, baseEnd_4899442] using wordTrace_append hprefix tailTrace_4899442
  have hstable : (prefixWord ++ tailWord_4899442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899442).length < 2 ^ (prefixWord ++ tailWord_4899442).sum := by decide
  have hdescent : baseEnd_4899442 < baseStart_4899442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899518 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_4899518 : Nat := 118140960795 + 4899518 * 2 ^ 59
def prefixEnd_4899518 : Nat := 4983230072969 + 3 ^ 40 * 4899518 * 2
def baseEnd_4899518 : Nat := 2515807709355466846992533

theorem tailTrace_4899518 : CollatzResearch.WordTrace tailWord_4899518 prefixEnd_4899518 2515807709355466846992533 := by
  unfold tailWord_4899518
  simp only [CollatzResearch.WordTrace]
  refine ⟨22337512782986316487595401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119133401509260354600508805 22337512782986316487595401)
  ·
    refine ⟨16753134587239737365696551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22337512782986316487595401 16753134587239737365696551)
    ·
      refine ⟨25129701880859606048544827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16753134587239737365696551 25129701880859606048544827)
      ·
        refine ⟨37694552821289409072817241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25129701880859606048544827 37694552821289409072817241)
        ·
          refine ⟨28270914615967056804612931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37694552821289409072817241 28270914615967056804612931)
          ·
            refine ⟨42406371923950585206919397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28270914615967056804612931 42406371923950585206919397)
            ·
              refine ⟨7951194735740734726297387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42406371923950585206919397 7951194735740734726297387)
              ·
                refine ⟨11926792103611102089446081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7951194735740734726297387 11926792103611102089446081)
                ·
                  refine ⟨8945094077708326567084561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11926792103611102089446081 8945094077708326567084561)
                  ·
                    refine ⟨6708820558281244925313421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8945094077708326567084561 6708820558281244925313421)
                    ·
                      refine ⟨2515807709355466846992533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6708820558281244925313421 2515807709355466846992533)
                      ·
                        rfl

theorem cell23_4899518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_4899518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899518 prefixEnd_4899518 := by exact prefixLift 4899518
  have htrace : WordTrace (prefixWord ++ tailWord_4899518) baseStart_4899518 baseEnd_4899518 := by
    simpa [prefixWord, tailWord_4899518, baseEnd_4899518] using wordTrace_append hprefix tailTrace_4899518
  have hstable : (prefixWord ++ tailWord_4899518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899518).length < 2 ^ (prefixWord ++ tailWord_4899518).sum := by decide
  have hdescent : baseEnd_4899518 < baseStart_4899518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899538 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 6]
def baseStart_4899538 : Nat := 118140960795 + 4899538 * 2 ^ 59
def prefixEnd_4899538 : Nat := 4983230072969 + 3 ^ 40 * 4899538 * 2
def baseEnd_4899538 : Nat := 279535330996506307638049

theorem tailTrace_4899538 : CollatzResearch.WordTrace tailWord_4899538 prefixEnd_4899538 279535330996506307638049 := by
  unfold tailWord_4899538
  simp only [CollatzResearch.WordTrace]
  refine ⟨44675207930954518829122817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119133887815878716877660845 44675207930954518829122817)
  ·
    refine ⟨33506405948215889121842113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44675207930954518829122817 33506405948215889121842113)
    ·
      refine ⟨25129804461161916841381585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33506405948215889121842113 25129804461161916841381585)
      ·
        refine ⟨18847353345871437631036189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25129804461161916841381585 18847353345871437631036189)
        ·
          refine ⟨7067757504701789111638571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18847353345871437631036189 7067757504701789111638571)
          ·
            refine ⟨10601636257052683667457857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7067757504701789111638571 10601636257052683667457857)
            ·
              refine ⟨7951227192789512750593393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10601636257052683667457857 7951227192789512750593393)
              ·
                refine ⟨5963420394592134562945045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7951227192789512750593393 5963420394592134562945045)
                ·
                  refine ⟨279535330996506307638049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5963420394592134562945045 279535330996506307638049)
                  ·
                    rfl

theorem cell23_4899538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_4899538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899538 prefixEnd_4899538 := by exact prefixLift 4899538
  have htrace : WordTrace (prefixWord ++ tailWord_4899538) baseStart_4899538 baseEnd_4899538 := by
    simpa [prefixWord, tailWord_4899538, baseEnd_4899538] using wordTrace_append hprefix tailTrace_4899538
  have hstable : (prefixWord ++ tailWord_4899538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899538).length < 2 ^ (prefixWord ++ tailWord_4899538).sum := by decide
  have hdescent : baseEnd_4899538 < baseStart_4899538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899571 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 4]
def baseStart_4899571 : Nat := 118140960795 + 4899571 * 2 ^ 59
def prefixEnd_4899571 : Nat := 4983230072969 + 3 ^ 40 * 4899571 * 2
def baseEnd_4899571 : Nat := 2515834923830155139629789

theorem tailTrace_4899571 : CollatzResearch.WordTrace tailWord_4899571 prefixEnd_4899571 2515834923830155139629789 := by
  unfold tailWord_4899571
  simp only [CollatzResearch.WordTrace]
  refine ⟨178702035332698521952442567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119134690221799014634961711 178702035332698521952442567)
  ·
    refine ⟨268053052999047782928663851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178702035332698521952442567 268053052999047782928663851)
    ·
      refine ⟨402079579498571674392995777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268053052999047782928663851 402079579498571674392995777)
      ·
        refine ⟨301559684623928755794746833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402079579498571674392995777 301559684623928755794746833)
        ·
          refine ⟨226169763467946566846060125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301559684623928755794746833 226169763467946566846060125)
          ·
            refine ⟨84813661300479962567272547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226169763467946566846060125 84813661300479962567272547)
            ·
              refine ⟨127220491950719943850908821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84813661300479962567272547 127220491950719943850908821)
              ·
                refine ⟨5963460560189997368011351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127220491950719943850908821 5963460560189997368011351)
                ·
                  refine ⟨8945190840284996052017027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5963460560189997368011351 8945190840284996052017027)
                  ·
                    refine ⟨13417786260427494078025541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8945190840284996052017027 13417786260427494078025541)
                    ·
                      refine ⟨2515834923830155139629789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13417786260427494078025541 2515834923830155139629789)
                      ·
                        rfl

theorem cell23_4899571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 4].length) (baseStart_4899571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899571 prefixEnd_4899571 := by exact prefixLift 4899571
  have htrace : WordTrace (prefixWord ++ tailWord_4899571) baseStart_4899571 baseEnd_4899571 := by
    simpa [prefixWord, tailWord_4899571, baseEnd_4899571] using wordTrace_append hprefix tailTrace_4899571
  have hstable : (prefixWord ++ tailWord_4899571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899571).length < 2 ^ (prefixWord ++ tailWord_4899571).sum := by decide
  have hdescent : baseEnd_4899571 < baseStart_4899571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899581 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_4899581 : Nat := 118140960795 + 4899581 * 2 ^ 59
def prefixEnd_4899581 : Nat := 4983230072969 + 3 ^ 40 * 4899581 * 2
def baseEnd_4899581 : Nat := 838613352878900033501581

theorem tailTrace_4899581 : CollatzResearch.WordTrace tailWord_4899581 prefixEnd_4899581 838613352878900033501581 := by
  unfold tailWord_4899581
  simp only [CollatzResearch.WordTrace]
  refine ⟨178702400062662293660306597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119134933375108195773537731 178702400062662293660306597)
  ·
    refine ⟨33506700011749180061307487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178702400062662293660306597 33506700011749180061307487)
    ·
      refine ⟨50260050017623770091961231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33506700011749180061307487 50260050017623770091961231)
      ·
        refine ⟨75390075026435655137941847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50260050017623770091961231 75390075026435655137941847)
        ·
          refine ⟨113085112539653482706912771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75390075026435655137941847 113085112539653482706912771)
          ·
            refine ⟨169627668809480224060369157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113085112539653482706912771 169627668809480224060369157)
            ·
              refine ⟨31805187901777542011319217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169627668809480224060369157 31805187901777542011319217)
              ·
                refine ⟨23853890926333156508489413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31805187901777542011319217 23853890926333156508489413)
                ·
                  refine ⟨4472604548687466845341765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23853890926333156508489413 4472604548687466845341765)
                  ·
                    refine ⟨838613352878900033501581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4472604548687466845341765 838613352878900033501581)
                    ·
                      rfl

theorem cell23_4899581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_4899581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899581 prefixEnd_4899581 := by exact prefixLift 4899581
  have htrace : WordTrace (prefixWord ++ tailWord_4899581) baseStart_4899581 baseEnd_4899581 := by
    simpa [prefixWord, tailWord_4899581, baseEnd_4899581] using wordTrace_append hprefix tailTrace_4899581
  have hstable : (prefixWord ++ tailWord_4899581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899581).length < 2 ^ (prefixWord ++ tailWord_4899581).sum := by decide
  have hdescent : baseEnd_4899581 < baseStart_4899581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899582 : List Nat := [4, 2, 2, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4899582 : Nat := 118140960795 + 4899582 * 2 ^ 59
def prefixEnd_4899582 : Nat := 4983230072969 + 3 ^ 40 * 4899582 * 2
def baseEnd_4899582 : Nat := 2515840572117354596592239

theorem tailTrace_4899582 : CollatzResearch.WordTrace tailWord_4899582 prefixEnd_4899582 2515840572117354596592239 := by
  unfold tailWord_4899582
  simp only [CollatzResearch.WordTrace]
  refine ⟨22337804566957333853886625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119134957690439113887395333 22337804566957333853886625)
  ·
    refine ⟨16753353425218000390414969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22337804566957333853886625 16753353425218000390414969)
    ·
      refine ⟨12565015068913500292811227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16753353425218000390414969 12565015068913500292811227)
      ·
        refine ⟨18847522603370250439216841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12565015068913500292811227 18847522603370250439216841)
        ·
          refine ⟨14135641952527687829412631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18847522603370250439216841 14135641952527687829412631)
          ·
            refine ⟨21203462928791531744118947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14135641952527687829412631 21203462928791531744118947)
            ·
              refine ⟨31805194393187297616178421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21203462928791531744118947 31805194393187297616178421)
              ·
                refine ⟨2981736974361309151516727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31805194393187297616178421 2981736974361309151516727)
                ·
                  refine ⟨4472605461541963727275091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2981736974361309151516727 4472605461541963727275091)
                  ·
                    refine ⟨6708908192312945590912637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4472605461541963727275091 6708908192312945590912637)
                    ·
                      refine ⟨2515840572117354596592239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6708908192312945590912637 2515840572117354596592239)
                      ·
                        rfl

theorem cell23_4899582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4899582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899582 prefixEnd_4899582 := by exact prefixLift 4899582
  have htrace : WordTrace (prefixWord ++ tailWord_4899582) baseStart_4899582 baseEnd_4899582 := by
    simpa [prefixWord, tailWord_4899582, baseEnd_4899582] using wordTrace_append hprefix tailTrace_4899582
  have hstable : (prefixWord ++ tailWord_4899582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899582).length < 2 ^ (prefixWord ++ tailWord_4899582).sum := by decide
  have hdescent : baseEnd_4899582 < baseStart_4899582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899588 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4899588 : Nat := 118140960795 + 4899588 * 2 ^ 59
def prefixEnd_4899588 : Nat := 4983230072969 + 3 ^ 40 * 4899588 * 2
def baseEnd_4899588 : Nat := 2515843653001281573117211

theorem tailTrace_4899588 : CollatzResearch.WordTrace tailWord_4899588 prefixEnd_4899588 2515843653001281573117211 := by
  unfold tailWord_4899588
  simp only [CollatzResearch.WordTrace]
  refine ⟨89351327686818466927905709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119135103582424622570540945 89351327686818466927905709)
  ·
    refine ⟨33506747882556925097964641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89351327686818466927905709 33506747882556925097964641)
    ·
      refine ⟨25130060911917693823473481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33506747882556925097964641 25130060911917693823473481)
      ·
        refine ⟨18847545683938270367605111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25130060911917693823473481 18847545683938270367605111)
        ·
          refine ⟨28271318525907405551407667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18847545683938270367605111 28271318525907405551407667)
          ·
            refine ⟨42406977788861108327111501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28271318525907405551407667 42406977788861108327111501)
            ·
              refine ⟨15902616670822915622666813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42406977788861108327111501 15902616670822915622666813)
              ·
                refine ⟨5963481251558593358500055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15902616670822915622666813 5963481251558593358500055)
                ·
                  refine ⟨8945221877337890037750083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5963481251558593358500055 8945221877337890037750083)
                  ·
                    refine ⟨13417832816006835056625125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8945221877337890037750083 13417832816006835056625125)
                    ·
                      refine ⟨2515843653001281573117211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13417832816006835056625125 2515843653001281573117211)
                      ·
                        rfl

theorem cell23_4899588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4899588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899588 prefixEnd_4899588 := by exact prefixLift 4899588
  have htrace : WordTrace (prefixWord ++ tailWord_4899588) baseStart_4899588 baseEnd_4899588 := by
    simpa [prefixWord, tailWord_4899588, baseEnd_4899588] using wordTrace_append hprefix tailTrace_4899588
  have hstable : (prefixWord ++ tailWord_4899588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899588).length < 2 ^ (prefixWord ++ tailWord_4899588).sum := by decide
  have hdescent : baseEnd_4899588 < baseStart_4899588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899594 : List Nat := [3, 1, 2, 2, 1, 2, 12]
def baseStart_4899594 : Nat := 118140960795 + 4899594 * 2 ^ 59
def prefixEnd_4899594 : Nat := 4983230072969 + 3 ^ 40 * 4899594 * 2
def baseEnd_4899594 : Nat := 31059836220805043822743

theorem tailTrace_4899594 : CollatzResearch.WordTrace tailWord_4899594 prefixEnd_4899594 31059836220805043822743 := by
  unfold tailWord_4899594
  simp only [CollatzResearch.WordTrace]
  refine ⟨44675718552903799220132459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119135249474410131253686557 44675718552903799220132459)
  ·
    refine ⟨67013577829355698830198689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44675718552903799220132459 67013577829355698830198689)
    ·
      refine ⟨50260183372016774122649017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67013577829355698830198689 50260183372016774122649017)
      ·
        refine ⟨37695137529012580591986763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50260183372016774122649017 37695137529012580591986763)
        ·
          refine ⟨56542706293518870887980145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37695137529012580591986763 56542706293518870887980145)
          ·
            refine ⟨42407029720139153165985109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56542706293518870887980145 42407029720139153165985109)
            ·
              refine ⟨31059836220805043822743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 42407029720139153165985109 31059836220805043822743)
              ·
                rfl

theorem cell23_4899594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 12].length) (baseStart_4899594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899594 prefixEnd_4899594 := by exact prefixLift 4899594
  have htrace : WordTrace (prefixWord ++ tailWord_4899594) baseStart_4899594 baseEnd_4899594 := by
    simpa [prefixWord, tailWord_4899594, baseEnd_4899594] using wordTrace_append hprefix tailTrace_4899594
  have hstable : (prefixWord ++ tailWord_4899594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899594).length < 2 ^ (prefixWord ++ tailWord_4899594).sum := by decide
  have hdescent : baseEnd_4899594 < baseStart_4899594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899605 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_4899605 : Nat := 118140960795 + 4899605 * 2 ^ 59
def prefixEnd_4899605 : Nat := 4983230072969 + 3 ^ 40 * 4899605 * 2
def baseEnd_4899605 : Nat := 2515852382172408006604633

theorem tailTrace_4899605 : CollatzResearch.WordTrace tailWord_4899605 prefixEnd_4899605 2515852382172408006604633 := by
  unfold tailWord_4899605
  simp only [CollatzResearch.WordTrace]
  refine ⟨178703275414575345759180269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119135516943050230506120179 178703275414575345759180269)
  ·
    refine ⟨67013728280465754659692601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178703275414575345759180269 67013728280465754659692601)
    ·
      refine ⟨50260296210349315994769451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67013728280465754659692601 50260296210349315994769451)
      ·
        refine ⟨75390444315523973992154177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50260296210349315994769451 75390444315523973992154177)
        ·
          refine ⟨56542833236642980494115633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75390444315523973992154177 56542833236642980494115633)
          ·
            refine ⟨42407124927482235370586725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56542833236642980494115633 42407124927482235370586725)
            ·
              refine ⟨7951335923902919131985011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42407124927482235370586725 7951335923902919131985011)
              ·
                refine ⟨11927003885854378697977517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7951335923902919131985011 11927003885854378697977517)
                ·
                  refine ⟨4472626457195392011741569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11927003885854378697977517 4472626457195392011741569)
                  ·
                    refine ⟨3354469842896544008806177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4472626457195392011741569 3354469842896544008806177)
                    ·
                      refine ⟨2515852382172408006604633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354469842896544008806177 2515852382172408006604633)
                      ·
                        rfl

theorem cell23_4899605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_4899605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899605 prefixEnd_4899605 := by exact prefixLift 4899605
  have htrace : WordTrace (prefixWord ++ tailWord_4899605) baseStart_4899605 baseEnd_4899605 := by
    simpa [prefixWord, tailWord_4899605, baseEnd_4899605] using wordTrace_append hprefix tailTrace_4899605
  have hstable : (prefixWord ++ tailWord_4899605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899605).length < 2 ^ (prefixWord ++ tailWord_4899605).sum := by decide
  have hdescent : baseEnd_4899605 < baseStart_4899605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899615 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 2, 4]
def baseStart_4899615 : Nat := 118140960795 + 4899615 * 2 ^ 59
def prefixEnd_4899615 : Nat := 4983230072969 + 3 ^ 40 * 4899615 * 2
def baseEnd_4899615 : Nat := 838619172326317655826529

theorem tailTrace_4899615 : CollatzResearch.WordTrace tailWord_4899615 prefixEnd_4899615 838619172326317655826529 := by
  unfold tailWord_4899615
  simp only [CollatzResearch.WordTrace]
  refine ⟨178703640144539117467044299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119135760096359411644696199 178703640144539117467044299)
  ·
    refine ⟨268055460216808676200566449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178703640144539117467044299 268055460216808676200566449)
    ·
      refine ⟨201041595162606507150424837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268055460216808676200566449 201041595162606507150424837)
      ·
        refine ⟨37695299092988720090704657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201041595162606507150424837 37695299092988720090704657)
        ·
          refine ⟨28271474319741540068028493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37695299092988720090704657 28271474319741540068028493)
          ·
            refine ⟨10601802869903077525510685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28271474319741540068028493 10601802869903077525510685)
            ·
              refine ⟨3975676076213654072066507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10601802869903077525510685 3975676076213654072066507)
              ·
                refine ⟨5963514114320481108099761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975676076213654072066507 5963514114320481108099761)
                ·
                  refine ⟨4472635585740360831074821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5963514114320481108099761 4472635585740360831074821)
                  ·
                    refine ⟨838619172326317655826529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4472635585740360831074821 838619172326317655826529)
                    ·
                      rfl

theorem cell23_4899615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 4].length) (baseStart_4899615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899615 prefixEnd_4899615 := by exact prefixLift 4899615
  have htrace : WordTrace (prefixWord ++ tailWord_4899615) baseStart_4899615 baseEnd_4899615 := by
    simpa [prefixWord, tailWord_4899615, baseEnd_4899615] using wordTrace_append hprefix tailTrace_4899615
  have hstable : (prefixWord ++ tailWord_4899615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899615).length < 2 ^ (prefixWord ++ tailWord_4899615).sum := by decide
  have hdescent : baseEnd_4899615 < baseStart_4899615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899618 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_4899618 : Nat := 118140960795 + 4899618 * 2 ^ 59
def prefixEnd_4899618 : Nat := 4983230072969 + 3 ^ 40 * 4899618 * 2
def baseEnd_4899618 : Nat := 2515859057420916455742073

theorem tailTrace_4899618 : CollatzResearch.WordTrace tailWord_4899618 prefixEnd_4899618 2515859057420916455742073 := by
  unfold tailWord_4899618
  simp only [CollatzResearch.WordTrace]
  refine ⟨44675937390882062244850877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119135833042352165986269005 44675937390882062244850877)
  ·
    refine ⟨16753476521580773341819079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44675937390882062244850877 16753476521580773341819079)
    ·
      refine ⟨25130214782371160012728619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16753476521580773341819079 25130214782371160012728619)
      ·
        refine ⟨37695322173556740019092929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25130214782371160012728619 37695322173556740019092929)
        ·
          refine ⟨28271491630167555014319697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37695322173556740019092929 28271491630167555014319697)
          ·
            refine ⟨21203618722625666260739773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28271491630167555014319697 21203618722625666260739773)
            ·
              refine ⟨7951357020984624847777415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21203618722625666260739773 7951357020984624847777415)
              ·
                refine ⟨11927035531476937271666123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7951357020984624847777415 11927035531476937271666123)
                ·
                  refine ⟨17890553297215405907499185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11927035531476937271666123 17890553297215405907499185)
                  ·
                    refine ⟨13417914972911554430624389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17890553297215405907499185 13417914972911554430624389)
                    ·
                      refine ⟨2515859057420916455742073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13417914972911554430624389 2515859057420916455742073)
                      ·
                        rfl

theorem cell23_4899618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_4899618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899618 prefixEnd_4899618 := by exact prefixLift 4899618
  have htrace : WordTrace (prefixWord ++ tailWord_4899618) baseStart_4899618 baseEnd_4899618 := by
    simpa [prefixWord, tailWord_4899618, baseEnd_4899618] using wordTrace_append hprefix tailTrace_4899618
  have hstable : (prefixWord ++ tailWord_4899618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899618).length < 2 ^ (prefixWord ++ tailWord_4899618).sum := by decide
  have hdescent : baseEnd_4899618 < baseStart_4899618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899681 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_4899681 : Nat := 118140960795 + 4899681 * 2 ^ 59
def prefixEnd_4899681 : Nat := 4983230072969 + 3 ^ 40 * 4899681 * 2
def baseEnd_4899681 : Nat := 2515891406702149709254283

theorem tailTrace_4899681 : CollatzResearch.WordTrace tailWord_4899681 prefixEnd_4899681 2515891406702149709254283 := by
  unfold tailWord_4899681
  simp only [CollatzResearch.WordTrace]
  refine ⟨178706047362300010738946897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119137364908200007159297931 178706047362300010738946897)
  ·
    refine ⟨134029535521725008054210173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178706047362300010738946897 134029535521725008054210173)
    ·
      refine ⟨50261075820646878020328815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134029535521725008054210173 50261075820646878020328815)
      ·
        refine ⟨75391613730970317030493223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50261075820646878020328815 75391613730970317030493223)
        ·
          refine ⟨113087420596455475545739835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75391613730970317030493223 113087420596455475545739835)
          ·
            refine ⟨169631130894683213318609753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113087420596455475545739835 169631130894683213318609753)
            ·
              refine ⟨127223348171012409988957315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169631130894683213318609753 127223348171012409988957315)
              ·
                refine ⟨190835022256518614983435973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127223348171012409988957315 190835022256518614983435973)
                ·
                  refine ⟨35781566673097240309394245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190835022256518614983435973 35781566673097240309394245)
                  ·
                    refine ⟨6709043751205732558011421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35781566673097240309394245 6709043751205732558011421)
                    ·
                      refine ⟨2515891406702149709254283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6709043751205732558011421 2515891406702149709254283)
                      ·
                        rfl

theorem cell23_4899681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_4899681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899681 prefixEnd_4899681 := by exact prefixLift 4899681
  have htrace : WordTrace (prefixWord ++ tailWord_4899681) baseStart_4899681 baseEnd_4899681 := by
    simpa [prefixWord, tailWord_4899681, baseEnd_4899681] using wordTrace_append hprefix tailTrace_4899681
  have hstable : (prefixWord ++ tailWord_4899681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899681).length < 2 ^ (prefixWord ++ tailWord_4899681).sum := by decide
  have hdescent : baseEnd_4899681 < baseStart_4899681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899682 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_4899682 : Nat := 118140960795 + 4899682 * 2 ^ 59
def prefixEnd_4899682 : Nat := 4983230072969 + 3 ^ 40 * 4899682 * 2
def baseEnd_4899682 : Nat := 2515891920182804205341779

theorem tailTrace_4899682 : CollatzResearch.WordTrace tailWord_4899682 prefixEnd_4899682 2515891920182804205341779 := by
  unfold tailWord_4899682
  simp only [CollatzResearch.WordTrace]
  refine ⟨44676520958824096977433325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119137389223530925273155533 44676520958824096977433325)
  ·
    refine ⟨16753695359559036366537497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44676520958824096977433325 16753695359559036366537497)
    ·
      refine ⟨12565271519669277274903123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16753695359559036366537497 12565271519669277274903123)
      ·
        refine ⟨18847907279503915912354685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12565271519669277274903123 18847907279503915912354685)
        ·
          refine ⟨7067965229813968467133007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18847907279503915912354685 7067965229813968467133007)
          ·
            refine ⟨10601947844720952700699511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7067965229813968467133007 10601947844720952700699511)
            ·
              refine ⟨15902921767081429051049267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10601947844720952700699511 15902921767081429051049267)
              ·
                refine ⟨23854382650622143576573901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15902921767081429051049267 23854382650622143576573901)
                ·
                  refine ⟨8945393493983303841215213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23854382650622143576573901 8945393493983303841215213)
                  ·
                    refine ⟨3354522560243738940455705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8945393493983303841215213 3354522560243738940455705)
                    ·
                      refine ⟨2515891920182804205341779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354522560243738940455705 2515891920182804205341779)
                      ·
                        rfl

theorem cell23_4899682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_4899682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899682 prefixEnd_4899682 := by exact prefixLift 4899682
  have htrace : WordTrace (prefixWord ++ tailWord_4899682) baseStart_4899682 baseEnd_4899682 := by
    simpa [prefixWord, tailWord_4899682, baseEnd_4899682] using wordTrace_append hprefix tailTrace_4899682
  have hstable : (prefixWord ++ tailWord_4899682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899682).length < 2 ^ (prefixWord ++ tailWord_4899682).sum := by decide
  have hdescent : baseEnd_4899682 < baseStart_4899682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899788 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_4899788 : Nat := 118140960795 + 4899788 * 2 ^ 59
def prefixEnd_4899788 : Nat := 4983230072969 + 3 ^ 40 * 4899788 * 2
def baseEnd_4899788 : Nat := 2515946349132180790616291

theorem tailTrace_4899788 : CollatzResearch.WordTrace tailWord_4899788 prefixEnd_4899788 2515946349132180790616291 := by
  unfold tailWord_4899788
  simp only [CollatzResearch.WordTrace]
  refine ⟨89354974986456184006546009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119139966648608245342061345 89354974986456184006546009)
  ·
    refine ⟨67016231239842138004909507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89354974986456184006546009 67016231239842138004909507)
    ·
      refine ⟨100524346859763207007364261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67016231239842138004909507 100524346859763207007364261)
      ·
        refine ⟨18848315036205601313880799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100524346859763207007364261 18848315036205601313880799)
        ·
          refine ⟨28272472554308401970821199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18848315036205601313880799 28272472554308401970821199)
          ·
            refine ⟨42408708831462602956231799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28272472554308401970821199 42408708831462602956231799)
            ·
              refine ⟨63613063247193904434347699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42408708831462602956231799 63613063247193904434347699)
              ·
                refine ⟨95419594870790856651521549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63613063247193904434347699 95419594870790856651521549)
                ·
                  refine ⟨35782348076546571244320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95419594870790856651521549 35782348076546571244320581)
                  ·
                    refine ⟨6709190264352482108310109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35782348076546571244320581 6709190264352482108310109)
                    ·
                      refine ⟨2515946349132180790616291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6709190264352482108310109 2515946349132180790616291)
                      ·
                        rfl

theorem cell23_4899788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_4899788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899788 prefixEnd_4899788 := by exact prefixLift 4899788
  have htrace : WordTrace (prefixWord ++ tailWord_4899788) baseStart_4899788 baseEnd_4899788 := by
    simpa [prefixWord, tailWord_4899788, baseEnd_4899788] using wordTrace_append hprefix tailTrace_4899788
  have hstable : (prefixWord ++ tailWord_4899788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899788).length < 2 ^ (prefixWord ++ tailWord_4899788).sum := by decide
  have hdescent : baseEnd_4899788 < baseStart_4899788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899805 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4899805 : Nat := 118140960795 + 4899805 * 2 ^ 59
def prefixEnd_4899805 : Nat := 4983230072969 + 3 ^ 40 * 4899805 * 2
def baseEnd_4899805 : Nat := 2515955078303307224103713

theorem tailTrace_4899805 : CollatzResearch.WordTrace tailWord_4899805 prefixEnd_4899805 2515955078303307224103713 := by
  unfold tailWord_4899805
  simp only [CollatzResearch.WordTrace]
  refine ⟨178710570013850779916460869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119140380009233853277640579 178710570013850779916460869)
  ·
    refine ⟨33508231877597021234336413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178710570013850779916460869 33508231877597021234336413)
    ·
      refine ⟨12565586954098882962876155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33508231877597021234336413 12565586954098882962876155)
      ·
        refine ⟨18848380431148324444314233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12565586954098882962876155 18848380431148324444314233)
        ·
          refine ⟨14136285323361243333235675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18848380431148324444314233 14136285323361243333235675)
          ·
            refine ⟨21204427985041864999853513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14136285323361243333235675 21204427985041864999853513)
            ·
              refine ⟨15903320988781398749890135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21204427985041864999853513 15903320988781398749890135)
              ·
                refine ⟨23854981483172098124835203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15903320988781398749890135 23854981483172098124835203)
                ·
                  refine ⟨35782472224758147187252805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23854981483172098124835203 35782472224758147187252805)
                  ·
                    refine ⟨6709213542142152597609901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35782472224758147187252805 6709213542142152597609901)
                    ·
                      refine ⟨2515955078303307224103713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6709213542142152597609901 2515955078303307224103713)
                      ·
                        rfl

theorem cell23_4899805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4899805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899805 prefixEnd_4899805 := by exact prefixLift 4899805
  have htrace : WordTrace (prefixWord ++ tailWord_4899805) baseStart_4899805 baseEnd_4899805 := by
    simpa [prefixWord, tailWord_4899805, baseEnd_4899805] using wordTrace_append hprefix tailTrace_4899805
  have hstable : (prefixWord ++ tailWord_4899805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899805).length < 2 ^ (prefixWord ++ tailWord_4899805).sum := by decide
  have hdescent : baseEnd_4899805 < baseStart_4899805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899822 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_4899822 : Nat := 118140960795 + 4899822 * 2 ^ 59
def prefixEnd_4899822 : Nat := 4983230072969 + 3 ^ 40 * 4899822 * 2
def baseEnd_4899822 : Nat := 2515963807474433657591135

theorem tailTrace_4899822 : CollatzResearch.WordTrace tailWord_4899822 prefixEnd_4899822 2515963807474433657591135 := by
  unfold tailWord_4899822
  simp only [CollatzResearch.WordTrace]
  refine ⟨22338898756848648977478715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119140793369859461213219813 22338898756848648977478715)
  ·
    refine ⟨33508348135272973466218073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22338898756848648977478715 33508348135272973466218073)
    ·
      refine ⟨25131261101454730099663555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33508348135272973466218073 25131261101454730099663555)
      ·
        refine ⟨37696891652182095149495333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25131261101454730099663555 37696891652182095149495333)
        ·
          refine ⟨7068167184784142840530375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37696891652182095149495333 7068167184784142840530375)
          ·
            refine ⟨10602250777176214260795563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068167184784142840530375 10602250777176214260795563)
            ·
              refine ⟨15903376165764321391193345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10602250777176214260795563 15903376165764321391193345)
              ·
                refine ⟨11927532124323241043395009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15903376165764321391193345 11927532124323241043395009)
                ·
                  refine ⟨8945649093242430782546257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11927532124323241043395009 8945649093242430782546257)
                  ·
                    refine ⟨6709236819931823086909693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8945649093242430782546257 6709236819931823086909693)
                    ·
                      refine ⟨2515963807474433657591135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6709236819931823086909693 2515963807474433657591135)
                      ·
                        rfl

theorem cell23_4899822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_4899822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899822 prefixEnd_4899822 := by exact prefixLift 4899822
  have htrace : WordTrace (prefixWord ++ tailWord_4899822) baseStart_4899822 baseEnd_4899822 := by
    simpa [prefixWord, tailWord_4899822, baseEnd_4899822] using wordTrace_append hprefix tailTrace_4899822
  have hstable : (prefixWord ++ tailWord_4899822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899822).length < 2 ^ (prefixWord ++ tailWord_4899822).sum := by decide
  have hdescent : baseEnd_4899822 < baseStart_4899822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899845 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 4, 3, 2]
def baseStart_4899845 : Nat := 118140960795 + 4899845 * 2 ^ 59
def prefixEnd_4899845 : Nat := 4983230072969 + 3 ^ 40 * 4899845 * 2
def baseEnd_4899845 : Nat := 2515975617529487067603529

theorem tailTrace_4899845 : CollatzResearch.WordTrace tailWord_4899845 prefixEnd_4899845 2515975617529487067603529 := by
  unfold tailWord_4899845
  simp only [CollatzResearch.WordTrace]
  refine ⟨178712028933705866747916989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119141352622470577831944659 178712028933705866747916989)
  ·
    refine ⟨67017010850139700030468871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178712028933705866747916989 67017010850139700030468871)
    ·
      refine ⟨100525516275209550045703307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67017010850139700030468871 100525516275209550045703307)
      ·
        refine ⟨150788274412814325068554961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100525516275209550045703307 150788274412814325068554961)
        ·
          refine ⟨113091205809610743801416221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150788274412814325068554961 113091205809610743801416221)
          ·
            refine ⟨42409202178604028925531083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113091205809610743801416221 42409202178604028925531083)
            ·
              refine ⟨63613803267906043388296625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42409202178604028925531083 63613803267906043388296625)
              ·
                refine ⟨47710352450929532541222469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63613803267906043388296625 47710352450929532541222469)
                ·
                  refine ⟨8945691084549287351479213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47710352450929532541222469 8945691084549287351479213)
                  ·
                    refine ⟨3354634156705982756804705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8945691084549287351479213 3354634156705982756804705)
                    ·
                      refine ⟨2515975617529487067603529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354634156705982756804705 2515975617529487067603529)
                      ·
                        rfl

theorem cell23_4899845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_4899845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899845 prefixEnd_4899845 := by exact prefixLift 4899845
  have htrace : WordTrace (prefixWord ++ tailWord_4899845) baseStart_4899845 baseEnd_4899845 := by
    simpa [prefixWord, tailWord_4899845, baseEnd_4899845] using wordTrace_append hprefix tailTrace_4899845
  have hstable : (prefixWord ++ tailWord_4899845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899845).length < 2 ^ (prefixWord ++ tailWord_4899845).sum := by decide
  have hdescent : baseEnd_4899845 < baseStart_4899845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899879 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4899879 : Nat := 118140960795 + 4899879 * 2 ^ 59
def prefixEnd_4899879 : Nat := 4983230072969 + 3 ^ 40 * 4899879 * 2
def baseEnd_4899879 : Nat := 2515993075871739934578373

theorem tailTrace_4899879 : CollatzResearch.WordTrace tailWord_4899879 prefixEnd_4899879 2515993075871739934578373 := by
  unfold tailWord_4899879
  simp only [CollatzResearch.WordTrace]
  refine ⟨178713269015582690554654691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119142179343721793703103127 178713269015582690554654691)
  ·
    refine ⟨268069903523374035831982037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178713269015582690554654691 268069903523374035831982037)
    ·
      refine ⟨6282888363829078964812079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 268069903523374035831982037 6282888363829078964812079)
      ·
        refine ⟨9424332545743618447218119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282888363829078964812079 9424332545743618447218119)
        ·
          refine ⟨14136498818615427670827179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9424332545743618447218119 14136498818615427670827179)
          ·
            refine ⟨21204748227923141506240769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14136498818615427670827179 21204748227923141506240769)
            ·
              refine ⟨15903561170942356129680577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21204748227923141506240769 15903561170942356129680577)
              ·
                refine ⟨11927670878206767097260433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15903561170942356129680577 11927670878206767097260433)
                ·
                  refine ⟨8945753158655075322945325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11927670878206767097260433 8945753158655075322945325)
                  ·
                    refine ⟨3354657434495653246104497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8945753158655075322945325 3354657434495653246104497)
                    ·
                      refine ⟨2515993075871739934578373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354657434495653246104497 2515993075871739934578373)
                      ·
                        rfl

theorem cell23_4899879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4899879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899879 prefixEnd_4899879 := by exact prefixLift 4899879
  have htrace : WordTrace (prefixWord ++ tailWord_4899879) baseStart_4899879 baseEnd_4899879 := by
    simpa [prefixWord, tailWord_4899879, baseEnd_4899879] using wordTrace_append hprefix tailTrace_4899879
  have hstable : (prefixWord ++ tailWord_4899879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899879).length < 2 ^ (prefixWord ++ tailWord_4899879).sum := by decide
  have hdescent : baseEnd_4899879 < baseStart_4899879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899888 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_4899888 : Nat := 118140960795 + 4899888 * 2 ^ 59
def prefixEnd_4899888 : Nat := 4983230072969 + 3 ^ 40 * 4899888 * 2
def baseEnd_4899888 : Nat := 2515997697197630399365831

theorem tailTrace_4899888 : CollatzResearch.WordTrace tailWord_4899888 prefixEnd_4899888 2515997697197630399365831 := by
  unfold tailWord_4899888
  simp only [CollatzResearch.WordTrace]
  refine ⟨89356798636275042545866159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119142398181700056727821545 89356798636275042545866159)
  ·
    refine ⟨134035197954412563818799239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89356798636275042545866159 134035197954412563818799239)
    ·
      refine ⟨201052796931618845728198859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134035197954412563818799239 201052796931618845728198859)
      ·
        refine ⟨301579195397428268592298289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201052796931618845728198859 301579195397428268592298289)
        ·
          refine ⟨226184396548071201444223717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301579195397428268592298289 226184396548071201444223717)
          ·
            refine ⟨42409574352763350270791947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226184396548071201444223717 42409574352763350270791947)
            ·
              refine ⟨63614361529145025406187921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42409574352763350270791947 63614361529145025406187921)
              ·
                refine ⟨47710771146858769054640941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63614361529145025406187921 47710771146858769054640941)
                ·
                  refine ⟨17891539180072038395490353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47710771146858769054640941 17891539180072038395490353)
                  ·
                    refine ⟨13418654385054028796617765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17891539180072038395490353 13418654385054028796617765)
                    ·
                      refine ⟨2515997697197630399365831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13418654385054028796617765 2515997697197630399365831)
                      ·
                        rfl

theorem cell23_4899888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_4899888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899888 prefixEnd_4899888 := by exact prefixLift 4899888
  have htrace : WordTrace (prefixWord ++ tailWord_4899888) baseStart_4899888 baseEnd_4899888 := by
    simpa [prefixWord, tailWord_4899888, baseEnd_4899888] using wordTrace_append hprefix tailTrace_4899888
  have hstable : (prefixWord ++ tailWord_4899888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899888).length < 2 ^ (prefixWord ++ tailWord_4899888).sum := by decide
  have hdescent : baseEnd_4899888 < baseStart_4899888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899892 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4899892 : Nat := 118140960795 + 4899892 * 2 ^ 59
def prefixEnd_4899892 : Nat := 4983230072969 + 3 ^ 40 * 4899892 * 2
def baseEnd_4899892 : Nat := 2515999751120248383715813

theorem tailTrace_4899892 : CollatzResearch.WordTrace tailWord_4899892 prefixEnd_4899892 2515999751120248383715813 := by
  unfold tailWord_4899892
  simp only [CollatzResearch.WordTrace]
  refine ⟨89356871582267796887438965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119142495443023729183251953 89356871582267796887438965)
  ·
    refine ⟨8377206710837605958197403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89356871582267796887438965 8377206710837605958197403)
    ·
      refine ⟨12565810066256408937296105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8377206710837605958197403 12565810066256408937296105)
      ·
        refine ⟨9424357549692306702972079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12565810066256408937296105 9424357549692306702972079)
        ·
          refine ⟨14136536324538460054458119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9424357549692306702972079 14136536324538460054458119)
          ·
            refine ⟨21204804486807690081687179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14136536324538460054458119 21204804486807690081687179)
            ·
              refine ⟨31807206730211535122530769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21204804486807690081687179 31807206730211535122530769)
              ·
                refine ⟨23855405047658651341898077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31807206730211535122530769 23855405047658651341898077)
                ·
                  refine ⟨8945776892871994253211779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23855405047658651341898077 8945776892871994253211779)
                  ·
                    refine ⟨13418665339307991379817669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8945776892871994253211779 13418665339307991379817669)
                    ·
                      refine ⟨2515999751120248383715813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13418665339307991379817669 2515999751120248383715813)
                      ·
                        rfl

theorem cell23_4899892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4899892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899892 prefixEnd_4899892 := by exact prefixLift 4899892
  have htrace : WordTrace (prefixWord ++ tailWord_4899892) baseStart_4899892 baseEnd_4899892 := by
    simpa [prefixWord, tailWord_4899892, baseEnd_4899892] using wordTrace_append hprefix tailTrace_4899892
  have hstable : (prefixWord ++ tailWord_4899892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899892).length < 2 ^ (prefixWord ++ tailWord_4899892).sum := by decide
  have hdescent : baseEnd_4899892 < baseStart_4899892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899898 : List Nat := [3, 1, 1, 1, 3, 1, 5, 8]
def baseStart_4899898 : Nat := 118140960795 + 4899898 * 2 ^ 59
def prefixEnd_4899898 : Nat := 4983230072969 + 3 ^ 40 * 4899898 * 2
def baseEnd_4899898 : Nat := 93185290074228717045955

theorem tailTrace_4899898 : CollatzResearch.WordTrace tailWord_4899898 prefixEnd_4899898 93185290074228717045955 := by
  unfold tailWord_4899898
  simp only [CollatzResearch.WordTrace]
  refine ⟨44678490500628464199899087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119142641335009237866397565 44678490500628464199899087)
  ·
    refine ⟨67017735750942696299848631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44678490500628464199899087 67017735750942696299848631)
    ·
      refine ⟨100526603626414044449772947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67017735750942696299848631 100526603626414044449772947)
      ·
        refine ⟨150789905439621066674659421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100526603626414044449772947 150789905439621066674659421)
        ·
          refine ⟨56546214539857900002997283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150789905439621066674659421 56546214539857900002997283)
          ·
            refine ⟨84819321809786850004495925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56546214539857900002997283 84819321809786850004495925)
            ·
              refine ⟨7951811419667517187921493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84819321809786850004495925 7951811419667517187921493)
              ·
                refine ⟨93185290074228717045955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7951811419667517187921493 93185290074228717045955)
                ·
                  rfl

theorem cell23_4899898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 8].length) (baseStart_4899898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899898 prefixEnd_4899898 := by exact prefixLift 4899898
  have htrace : WordTrace (prefixWord ++ tailWord_4899898) baseStart_4899898 baseEnd_4899898 := by
    simpa [prefixWord, tailWord_4899898, baseEnd_4899898] using wordTrace_append hprefix tailTrace_4899898
  have hstable : (prefixWord ++ tailWord_4899898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899898).length < 2 ^ (prefixWord ++ tailWord_4899898).sum := by decide
  have hdescent : baseEnd_4899898 < baseStart_4899898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899902 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_4899902 : Nat := 118140960795 + 4899902 * 2 ^ 59
def prefixEnd_4899902 : Nat := 4983230072969 + 3 ^ 40 * 4899902 * 2
def baseEnd_4899902 : Nat := 838668295308931114863589

theorem tailTrace_4899902 : CollatzResearch.WordTrace tailWord_4899902 prefixEnd_4899902 838668295308931114863589 := by
  unfold tailWord_4899902
  simp only [CollatzResearch.WordTrace]
  refine ⟨22339263486812420685342745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119142738596332910321827973 22339263486812420685342745)
  ·
    refine ⟨16754447615109315514007059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22339263486812420685342745 16754447615109315514007059)
    ·
      refine ⟨25131671422663973271010589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16754447615109315514007059 25131671422663973271010589)
      ·
        refine ⟨9424376783498989976628971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25131671422663973271010589 9424376783498989976628971)
        ·
          refine ⟨14136565175248484964943457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9424376783498989976628971 14136565175248484964943457)
          ·
            refine ⟨10602423881436363723707593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14136565175248484964943457 10602423881436363723707593)
            ·
              refine ⟨7951817911077272792780695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10602423881436363723707593 7951817911077272792780695)
              ·
                refine ⟨11927726866615909189171043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7951817911077272792780695 11927726866615909189171043)
                ·
                  refine ⟨17891590299923863783756565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11927726866615909189171043 17891590299923863783756565)
                  ·
                    refine ⟨838668295308931114863589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17891590299923863783756565 838668295308931114863589)
                    ·
                      rfl

theorem cell23_4899902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_4899902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899902 prefixEnd_4899902 := by exact prefixLift 4899902
  have htrace : WordTrace (prefixWord ++ tailWord_4899902) baseStart_4899902 baseEnd_4899902 := by
    simpa [prefixWord, tailWord_4899902, baseEnd_4899902] using wordTrace_append hprefix tailTrace_4899902
  have hstable : (prefixWord ++ tailWord_4899902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899902).length < 2 ^ (prefixWord ++ tailWord_4899902).sum := by decide
  have hdescent : baseEnd_4899902 < baseStart_4899902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899925 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_4899925 : Nat := 118140960795 + 4899925 * 2 ^ 59
def prefixEnd_4899925 : Nat := 4983230072969 + 3 ^ 40 * 4899925 * 2
def baseEnd_4899925 : Nat := 2516016695981846754603161

theorem tailTrace_4899925 : CollatzResearch.WordTrace tailWord_4899925 prefixEnd_4899925 2516016695981846754603161 := by
  unfold tailWord_4899925
  simp only [CollatzResearch.WordTrace]
  refine ⟨178714946773416040410829229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119143297848944026940552819 178714946773416040410829229)
  ·
    refine ⟨67018105040031015154060961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178714946773416040410829229 67018105040031015154060961)
    ·
      refine ⟨50263578780023261365545721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67018105040031015154060961 50263578780023261365545721)
      ·
        refine ⟨37697684085017446024159291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50263578780023261365545721 37697684085017446024159291)
        ·
          refine ⟨56546526127526169036238937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37697684085017446024159291 56546526127526169036238937)
          ·
            refine ⟨42409894595644626777179203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56546526127526169036238937 42409894595644626777179203)
            ·
              refine ⟨63614841893466940165768805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42409894595644626777179203 63614841893466940165768805)
              ·
                refine ⟨11927782855025051281081651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63614841893466940165768805 11927782855025051281081651)
                ·
                  refine ⟨17891674282537576921622477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11927782855025051281081651 17891674282537576921622477)
                  ·
                    refine ⟨6709377855951591345608429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17891674282537576921622477 6709377855951591345608429)
                    ·
                      refine ⟨2516016695981846754603161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6709377855951591345608429 2516016695981846754603161)
                      ·
                        rfl

theorem cell23_4899925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_4899925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899925 prefixEnd_4899925 := by exact prefixLift 4899925
  have htrace : WordTrace (prefixWord ++ tailWord_4899925) baseStart_4899925 baseEnd_4899925 := by
    simpa [prefixWord, tailWord_4899925, baseEnd_4899925] using wordTrace_append hprefix tailTrace_4899925
  have hstable : (prefixWord ++ tailWord_4899925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899925).length < 2 ^ (prefixWord ++ tailWord_4899925).sum := by decide
  have hdescent : baseEnd_4899925 < baseStart_4899925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899926 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_4899926 : Nat := 118140960795 + 4899926 * 2 ^ 59
def prefixEnd_4899926 : Nat := 4983230072969 + 3 ^ 40 * 4899926 * 2
def baseEnd_4899926 : Nat := 2516017209462501250690657

theorem tailTrace_4899926 : CollatzResearch.WordTrace tailWord_4899926 prefixEnd_4899926 2516017209462501250690657 := by
  unfold tailWord_4899926
  simp only [CollatzResearch.WordTrace]
  refine ⟨11169686452900776098850977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119143322164274945054410421 11169686452900776098850977)
  ·
    refine ⟨8377264839675582074138233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11169686452900776098850977 8377264839675582074138233)
    ·
      refine ⟨6282948629756686555603675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8377264839675582074138233 6282948629756686555603675)
      ·
        refine ⟨9424422944635029833405513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282948629756686555603675 9424422944635029833405513)
        ·
          refine ⟨7068317208476272375054135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9424422944635029833405513 7068317208476272375054135)
          ·
            refine ⟨10602475812714408562581203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068317208476272375054135 10602475812714408562581203)
            ·
              refine ⟨15903713719071612843871805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10602475812714408562581203 15903713719071612843871805)
              ·
                refine ⟨5963892644651854816451927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15903713719071612843871805 5963892644651854816451927)
                ·
                  refine ⟨8945838966977782224677891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5963892644651854816451927 8945838966977782224677891)
                  ·
                    refine ⟨13418758450466673337016837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8945838966977782224677891 13418758450466673337016837)
                    ·
                      refine ⟨2516017209462501250690657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13418758450466673337016837 2516017209462501250690657)
                      ·
                        rfl

theorem cell23_4899926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_4899926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899926 prefixEnd_4899926 := by exact prefixLift 4899926
  have htrace : WordTrace (prefixWord ++ tailWord_4899926) baseStart_4899926 baseEnd_4899926 := by
    simpa [prefixWord, tailWord_4899926, baseEnd_4899926] using wordTrace_append hprefix tailTrace_4899926
  have hstable : (prefixWord ++ tailWord_4899926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899926).length < 2 ^ (prefixWord ++ tailWord_4899926).sum := by decide
  have hdescent : baseEnd_4899926 < baseStart_4899926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899959 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 2, 1, 3]
def baseStart_4899959 : Nat := 118140960795 + 4899959 * 2 ^ 59
def prefixEnd_4899959 : Nat := 4983230072969 + 3 ^ 40 * 4899959 * 2
def baseEnd_4899959 : Nat := 2516034154324099621578005

theorem tailTrace_4899959 : CollatzResearch.WordTrace tailWord_4899959 prefixEnd_4899959 2516034154324099621578005 := by
  unfold tailWord_4899959
  simp only [CollatzResearch.WordTrace]
  refine ⟨178716186855292864217566931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119144124570195242811711287 178716186855292864217566931)
  ·
    refine ⟨268074280282939296326350397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178716186855292864217566931 268074280282939296326350397)
    ·
      refine ⟨100527855106102236122381399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268074280282939296326350397 100527855106102236122381399)
      ·
        refine ⟨150791782659153354183572099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100527855106102236122381399 150791782659153354183572099)
        ·
          refine ⟨226187673988730031275358149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150791782659153354183572099 226187673988730031275358149)
          ·
            refine ⟨42410188872886880864129653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226187673988730031275358149 42410188872886880864129653)
            ·
              refine ⟨3975955206833145081012155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42410188872886880864129653 3975955206833145081012155)
              ·
                refine ⟨5963932810249717621518233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975955206833145081012155 5963932810249717621518233)
                ·
                  refine ⟨4472949607687288216138675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5963932810249717621518233 4472949607687288216138675)
                  ·
                    refine ⟨6709424411530932324208013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4472949607687288216138675 6709424411530932324208013)
                    ·
                      refine ⟨2516034154324099621578005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6709424411530932324208013 2516034154324099621578005)
                      ·
                        rfl

theorem cell23_4899959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_4899959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899959 prefixEnd_4899959 := by exact prefixLift 4899959
  have htrace : WordTrace (prefixWord ++ tailWord_4899959) baseStart_4899959 baseEnd_4899959 := by
    simpa [prefixWord, tailWord_4899959, baseEnd_4899959] using wordTrace_append hprefix tailTrace_4899959
  have hstable : (prefixWord ++ tailWord_4899959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899959).length < 2 ^ (prefixWord ++ tailWord_4899959).sum := by decide
  have hdescent : baseEnd_4899959 < baseStart_4899959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4899969 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_4899969 : Nat := 118140960795 + 4899969 * 2 ^ 59
def prefixEnd_4899969 : Nat := 4983230072969 + 3 ^ 40 * 4899969 * 2
def baseEnd_4899969 : Nat := 2516039289130644582452959

theorem tailTrace_4899969 : CollatzResearch.WordTrace tailWord_4899969 prefixEnd_4899969 2516039289130644582452959 := by
  unfold tailWord_4899969
  simp only [CollatzResearch.WordTrace]
  refine ⟨178716551585256635925430961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119144367723504423950287307 178716551585256635925430961)
  ·
    refine ⟨134037413688942476944073221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178716551585256635925430961 134037413688942476944073221)
    ·
      refine ⟨25132015066676714427013729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134037413688942476944073221 25132015066676714427013729)
      ·
        refine ⟨18849011300007535820260297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25132015066676714427013729 18849011300007535820260297)
        ·
          refine ⟨14136758475005651865195223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18849011300007535820260297 14136758475005651865195223)
          ·
            refine ⟨21205137712508477797792835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14136758475005651865195223 21205137712508477797792835)
            ·
              refine ⟨31807706568762716696689253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21205137712508477797792835 31807706568762716696689253)
              ·
                refine ⟨5963944981643009380629235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31807706568762716696689253 5963944981643009380629235)
                ·
                  refine ⟨8945917472464514070943853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5963944981643009380629235 8945917472464514070943853)
                  ·
                    refine ⟨3354719052174192776603945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8945917472464514070943853 3354719052174192776603945)
                    ·
                      refine ⟨2516039289130644582452959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354719052174192776603945 2516039289130644582452959)
                      ·
                        rfl

theorem cell23_4899969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_4899969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4899969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4899969 prefixEnd_4899969 := by exact prefixLift 4899969
  have htrace : WordTrace (prefixWord ++ tailWord_4899969) baseStart_4899969 baseEnd_4899969 := by
    simpa [prefixWord, tailWord_4899969, baseEnd_4899969] using wordTrace_append hprefix tailTrace_4899969
  have hstable : (prefixWord ++ tailWord_4899969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4899969).length < 2 ^ (prefixWord ++ tailWord_4899969).sum := by decide
  have hdescent : baseEnd_4899969 < baseStart_4899969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4899969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900005 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 7]
def baseStart_4900005 : Nat := 118140960795 + 4900005 * 2 ^ 59
def prefixEnd_4900005 : Nat := 4983230072969 + 3 ^ 40 * 4900005 * 2
def baseEnd_4900005 : Nat := 279561974937134049066977

theorem tailTrace_4900005 : CollatzResearch.WordTrace tailWord_4900005 prefixEnd_4900005 279561974937134049066977 := by
  unfold tailWord_4900005
  simp only [CollatzResearch.WordTrace]
  refine ⟨178717864613126214073741469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119145243075417476049160979 178717864613126214073741469)
  ·
    refine ⟨67019199229922330277653051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178717864613126214073741469 67019199229922330277653051)
    ·
      refine ⟨100528798844883495416479577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67019199229922330277653051 100528798844883495416479577)
      ·
        refine ⟨75396599133662621562359683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100528798844883495416479577 75396599133662621562359683)
        ·
          refine ⟨113094898700493932343539525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75396599133662621562359683 113094898700493932343539525)
          ·
            refine ⟨21205293506342612314413661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113094898700493932343539525 21205293506342612314413661)
            ·
              refine ⟨7951985064878479617905123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21205293506342612314413661 7951985064878479617905123)
              ·
                refine ⟨11927977597317719426857685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7951985064878479617905123 11927977597317719426857685)
                ·
                  refine ⟨279561974937134049066977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11927977597317719426857685 279561974937134049066977)
                  ·
                    rfl

theorem cell23_4900005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_4900005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900005 prefixEnd_4900005 := by exact prefixLift 4900005
  have htrace : WordTrace (prefixWord ++ tailWord_4900005) baseStart_4900005 baseEnd_4900005 := by
    simpa [prefixWord, tailWord_4900005, baseEnd_4900005] using wordTrace_append hprefix tailTrace_4900005
  have hstable : (prefixWord ++ tailWord_4900005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900005).length < 2 ^ (prefixWord ++ tailWord_4900005).sum := by decide
  have hdescent : baseEnd_4900005 < baseStart_4900005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900015 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 3]
def baseStart_4900015 : Nat := 118140960795 + 4900015 * 2 ^ 59
def prefixEnd_4900015 : Nat := 4983230072969 + 3 ^ 40 * 4900015 * 2
def baseEnd_4900015 : Nat := 2516062909240751402477747

theorem tailTrace_4900015 : CollatzResearch.WordTrace tailWord_4900015 prefixEnd_4900015 2516062909240751402477747 := by
  unfold tailWord_4900015
  simp only [CollatzResearch.WordTrace]
  refine ⟨178718229343089985781605499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119145486228726657187736999 178718229343089985781605499)
  ·
    refine ⟨268077344014634978672408249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178718229343089985781605499 268077344014634978672408249)
    ·
      refine ⟨201058008010976234004306187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268077344014634978672408249 201058008010976234004306187)
      ·
        refine ⟨301587012016464351006459281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201058008010976234004306187 301587012016464351006459281)
        ·
          refine ⟨226190259012348263254844461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301587012016464351006459281 226190259012348263254844461)
          ·
            refine ⟨84821347129630598720566673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226190259012348263254844461 84821347129630598720566673)
            ·
              refine ⟨63616010347222949040425005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84821347129630598720566673 63616010347222949040425005)
              ·
                refine ⟨23856003880208605890159377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63616010347222949040425005 23856003880208605890159377)
                ·
                  refine ⟨17892002910156454417619533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23856003880208605890159377 17892002910156454417619533)
                  ·
                    refine ⟨6709501091308670406607325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17892002910156454417619533 6709501091308670406607325)
                    ·
                      refine ⟨2516062909240751402477747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6709501091308670406607325 2516062909240751402477747)
                      ·
                        rfl

theorem cell23_4900015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_4900015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900015 prefixEnd_4900015 := by exact prefixLift 4900015
  have htrace : WordTrace (prefixWord ++ tailWord_4900015) baseStart_4900015 baseEnd_4900015 := by
    simpa [prefixWord, tailWord_4900015, baseEnd_4900015] using wordTrace_append hprefix tailTrace_4900015
  have hstable : (prefixWord ++ tailWord_4900015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900015).length < 2 ^ (prefixWord ++ tailWord_4900015).sum := by decide
  have hdescent : baseEnd_4900015 < baseStart_4900015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900056 : List Nat := [2, 1, 2, 2, 5, 2, 2, 2, 5]
def baseStart_4900056 : Nat := 118140960795 + 4900056 * 2 ^ 59
def prefixEnd_4900056 : Nat := 4983230072969 + 3 ^ 40 * 4900056 * 2
def baseEnd_4900056 : Nat := 279564884660842860229451

theorem tailTrace_4900056 : CollatzResearch.WordTrace tailWord_4900056 prefixEnd_4900056 279564884660842860229451 := by
  unfold tailWord_4900056
  simp only [CollatzResearch.WordTrace]
  refine ⟨89359862367970724891924011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119146483157294299855898681 89359862367970724891924011)
  ·
    refine ⟨134039793551956087337886017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89359862367970724891924011 134039793551956087337886017)
    ·
      refine ⟨100529845163967065503414513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134039793551956087337886017 100529845163967065503414513)
      ·
        refine ⟨75397383872975299127560885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100529845163967065503414513 75397383872975299127560885)
        ·
          refine ⟨7068504738091434293208833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75397383872975299127560885 7068504738091434293208833)
          ·
            refine ⟨5301378553568575719906625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7068504738091434293208833 5301378553568575719906625)
            ·
              refine ⟨3976033915176431789929969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5301378553568575719906625 3976033915176431789929969)
              ·
                refine ⟨2982025436382323842447477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3976033915176431789929969 2982025436382323842447477)
                ·
                  refine ⟨279564884660842860229451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2982025436382323842447477 279564884660842860229451)
                  ·
                    rfl

theorem cell23_4900056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 5].length) (baseStart_4900056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900056 prefixEnd_4900056 := by exact prefixLift 4900056
  have htrace : WordTrace (prefixWord ++ tailWord_4900056) baseStart_4900056 baseEnd_4900056 := by
    simpa [prefixWord, tailWord_4900056, baseEnd_4900056] using wordTrace_append hprefix tailTrace_4900056
  have hstable : (prefixWord ++ tailWord_4900056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900056).length < 2 ^ (prefixWord ++ tailWord_4900056).sum := by decide
  have hdescent : baseEnd_4900056 < baseStart_4900056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900099 : List Nat := [1, 1, 1, 3, 2, 4, 1, 5, 1, 4]
def baseStart_4900099 : Nat := 118140960795 + 4900099 * 2 ^ 59
def prefixEnd_4900099 : Nat := 4983230072969 + 3 ^ 40 * 4900099 * 2
def baseEnd_4900099 : Nat := 838702013871909691275787

theorem tailTrace_4900099 : CollatzResearch.WordTrace tailWord_4900099 prefixEnd_4900099 838702013871909691275787 := by
  unfold tailWord_4900099
  simp only [CollatzResearch.WordTrace]
  refine ⟨178721293074785668127663351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119147528716523778751775567 178721293074785668127663351)
  ·
    refine ⟨268081939612178502191495027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178721293074785668127663351 268081939612178502191495027)
    ·
      refine ⟨402122909418267753287242541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268081939612178502191495027 402122909418267753287242541)
      ·
        refine ⟨150796091031850407482715953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 402122909418267753287242541 150796091031850407482715953)
        ·
          refine ⟨113097068273887805612036965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150796091031850407482715953 113097068273887805612036965)
          ·
            refine ⟨21205700301353963552256931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113097068273887805612036965 21205700301353963552256931)
            ·
              refine ⟨31808550452030945328385397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21205700301353963552256931 31808550452030945328385397)
              ·
                refine ⟨2982051604877901124536131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31808550452030945328385397 2982051604877901124536131)
                ·
                  refine ⟨4473077407316851686804197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982051604877901124536131 4473077407316851686804197)
                  ·
                    refine ⟨838702013871909691275787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473077407316851686804197 838702013871909691275787)
                    ·
                      rfl

theorem cell23_4900099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 4].length) (baseStart_4900099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900099 prefixEnd_4900099 := by exact prefixLift 4900099
  have htrace : WordTrace (prefixWord ++ tailWord_4900099) baseStart_4900099 baseEnd_4900099 := by
    simpa [prefixWord, tailWord_4900099, baseEnd_4900099] using wordTrace_append hprefix tailTrace_4900099
  have hstable : (prefixWord ++ tailWord_4900099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900099).length < 2 ^ (prefixWord ++ tailWord_4900099).sum := by decide
  have hdescent : baseEnd_4900099 < baseStart_4900099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900149 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_4900149 : Nat := 118140960795 + 4900149 * 2 ^ 59
def prefixEnd_4900149 : Nat := 4983230072969 + 3 ^ 40 * 4900149 * 2
def baseEnd_4900149 : Nat := 2516131715648453878202131

theorem tailTrace_4900149 : CollatzResearch.WordTrace tailWord_4900149 prefixEnd_4900149 2516131715648453878202131 := by
  unfold tailWord_4900149
  simp only [CollatzResearch.WordTrace]
  refine ⟨178723116724604526666983501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119148744483069684444655667 178723116724604526666983501)
  ·
    refine ⟨67021168771726697500118813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178723116724604526666983501 67021168771726697500118813)
    ·
      refine ⟨25132938289397511562544555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67021168771726697500118813 25132938289397511562544555)
      ·
        refine ⟨37699407434096267343816833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25132938289397511562544555 37699407434096267343816833)
        ·
          refine ⟨28274555575572200507862625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37699407434096267343816833 28274555575572200507862625)
          ·
            refine ⟨21205916681679150380896969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28274555575572200507862625 21205916681679150380896969)
            ·
              refine ⟨15904437511259362785672727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21205916681679150380896969 15904437511259362785672727)
              ·
                refine ⟨23856656266889044178509091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15904437511259362785672727 23856656266889044178509091)
                ·
                  refine ⟨35784984400333566267763637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23856656266889044178509091 35784984400333566267763637)
                  ·
                    refine ⟨3354842287531271837602841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35784984400333566267763637 3354842287531271837602841)
                    ·
                      refine ⟨2516131715648453878202131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354842287531271837602841 2516131715648453878202131)
                      ·
                        rfl

theorem cell23_4900149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_4900149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900149 prefixEnd_4900149 := by exact prefixLift 4900149
  have htrace : WordTrace (prefixWord ++ tailWord_4900149) baseStart_4900149 baseEnd_4900149 := by
    simpa [prefixWord, tailWord_4900149, baseEnd_4900149] using wordTrace_append hprefix tailTrace_4900149
  have hstable : (prefixWord ++ tailWord_4900149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900149).length < 2 ^ (prefixWord ++ tailWord_4900149).sum := by decide
  have hdescent : baseEnd_4900149 < baseStart_4900149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900185 : List Nat := [1, 2, 1, 2, 2, 2, 3, 10]
def baseStart_4900185 : Nat := 118140960795 + 4900185 * 2 ^ 59
def prefixEnd_4900185 : Nat := 4983230072969 + 3 ^ 40 * 4900185 * 2
def baseEnd_4900185 : Nat := 93190748183407990272295

theorem tailTrace_4900185 : CollatzResearch.WordTrace tailWord_4900185 prefixEnd_4900185 93190748183407990272295 := by
  unfold tailWord_4900185
  simp only [CollatzResearch.WordTrace]
  refine ⟨178724429752474104815294009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119149619834982736543529339 178724429752474104815294009)
  ·
    refine ⟨134043322314355578611470507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178724429752474104815294009 134043322314355578611470507)
    ·
      refine ⟨201064983471533367917205761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134043322314355578611470507 201064983471533367917205761)
      ·
        refine ⟨150798737603650025937904321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201064983471533367917205761 150798737603650025937904321)
        ·
          refine ⟨113099053202737519453428241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150798737603650025937904321 113099053202737519453428241)
          ·
            refine ⟨84824289902053139590071181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113099053202737519453428241 84824289902053139590071181)
            ·
              refine ⟨31809108713269927346276693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84824289902053139590071181 31809108713269927346276693)
              ·
                refine ⟨93190748183407990272295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31809108713269927346276693 93190748183407990272295)
                ·
                  rfl

theorem cell23_4900185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 10].length) (baseStart_4900185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900185 prefixEnd_4900185 := by exact prefixLift 4900185
  have htrace : WordTrace (prefixWord ++ tailWord_4900185) baseStart_4900185 baseEnd_4900185 := by
    simpa [prefixWord, tailWord_4900185, baseEnd_4900185] using wordTrace_append hprefix tailTrace_4900185
  have hstable : (prefixWord ++ tailWord_4900185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900185).length < 2 ^ (prefixWord ++ tailWord_4900185).sum := by decide
  have hdescent : baseEnd_4900185 < baseStart_4900185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900192 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_4900192 : Nat := 118140960795 + 4900192 * 2 ^ 59
def prefixEnd_4900192 : Nat := 4983230072969 + 3 ^ 40 * 4900192 * 2
def baseEnd_4900192 : Nat := 2516153795316597209964433

theorem tailTrace_4900192 : CollatzResearch.WordTrace tailWord_4900192 prefixEnd_4900192 2516153795316597209964433 := by
  unfold tailWord_4900192
  simp only [CollatzResearch.WordTrace]
  refine ⟨89362342531724372505399415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119149790042299163340532553 89362342531724372505399415)
  ·
    refine ⟨134043513797586558758099123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89362342531724372505399415 134043513797586558758099123)
    ·
      refine ⟨201065270696379838137148685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134043513797586558758099123 201065270696379838137148685)
      ·
        refine ⟨75399476511142439301430757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201065270696379838137148685 75399476511142439301430757)
        ·
          refine ⟨14137401845839207369018267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75399476511142439301430757 14137401845839207369018267)
          ·
            refine ⟨21206102768758811053527401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14137401845839207369018267 21206102768758811053527401)
            ·
              refine ⟨15904577076569108290145551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21206102768758811053527401 15904577076569108290145551)
              ·
                refine ⟨23856865614853662435218327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15904577076569108290145551 23856865614853662435218327)
                ·
                  refine ⟨35785298422280493652827491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23856865614853662435218327 35785298422280493652827491)
                  ·
                    refine ⟨53677947633420740479241237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35785298422280493652827491 53677947633420740479241237)
                    ·
                      refine ⟨2516153795316597209964433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53677947633420740479241237 2516153795316597209964433)
                      ·
                        rfl

theorem cell23_4900192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_4900192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900192 prefixEnd_4900192 := by exact prefixLift 4900192
  have htrace : WordTrace (prefixWord ++ tailWord_4900192) baseStart_4900192 baseEnd_4900192 := by
    simpa [prefixWord, tailWord_4900192, baseEnd_4900192] using wordTrace_append hprefix tailTrace_4900192
  have hstable : (prefixWord ++ tailWord_4900192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900192).length < 2 ^ (prefixWord ++ tailWord_4900192).sum := by decide
  have hdescent : baseEnd_4900192 < baseStart_4900192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900196 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_4900196 : Nat := 118140960795 + 4900196 * 2 ^ 59
def prefixEnd_4900196 : Nat := 4983230072969 + 3 ^ 40 * 4900196 * 2
def baseEnd_4900196 : Nat := 2516155849239215194314415

theorem tailTrace_4900196 : CollatzResearch.WordTrace tailWord_4900196 prefixEnd_4900196 2516155849239215194314415 := by
  unfold tailWord_4900196
  simp only [CollatzResearch.WordTrace]
  refine ⟨89362415477717126846972221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119149887303622835795962961 89362415477717126846972221)
  ·
    refine ⟨33510905804143922567614583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89362415477717126846972221 33510905804143922567614583)
    ·
      refine ⟨50266358706215883851421875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33510905804143922567614583 50266358706215883851421875)
      ·
        refine ⟨75399538059323825777132813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50266358706215883851421875 75399538059323825777132813)
        ·
          refine ⟨28274826772246434666424805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75399538059323825777132813 28274826772246434666424805)
          ·
            refine ⟨5301530019796206499954651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28274826772246434666424805 5301530019796206499954651)
            ·
              refine ⟨7952295029694309749931977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5301530019796206499954651 7952295029694309749931977)
              ·
                refine ⟨5964221272270732312448983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7952295029694309749931977 5964221272270732312448983)
                ·
                  refine ⟨8946331908406098468673475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5964221272270732312448983 8946331908406098468673475)
                  ·
                    refine ⟨13419497862609147703010213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8946331908406098468673475 13419497862609147703010213)
                    ·
                      refine ⟨2516155849239215194314415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13419497862609147703010213 2516155849239215194314415)
                      ·
                        rfl

theorem cell23_4900196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_4900196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900196 prefixEnd_4900196 := by exact prefixLift 4900196
  have htrace : WordTrace (prefixWord ++ tailWord_4900196) baseStart_4900196 baseEnd_4900196 := by
    simpa [prefixWord, tailWord_4900196, baseEnd_4900196] using wordTrace_append hprefix tailTrace_4900196
  have hstable : (prefixWord ++ tailWord_4900196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900196).length < 2 ^ (prefixWord ++ tailWord_4900196).sum := by decide
  have hdescent : baseEnd_4900196 < baseStart_4900196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900206 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_4900206 : Nat := 118140960795 + 4900206 * 2 ^ 59
def prefixEnd_4900206 : Nat := 4983230072969 + 3 ^ 40 * 4900206 * 2
def baseEnd_4900206 : Nat := 838720328015253385063123

theorem tailTrace_4900206 : CollatzResearch.WordTrace tailWord_4900206 prefixEnd_4900206 838720328015253385063123 := by
  unfold tailWord_4900206
  simp only [CollatzResearch.WordTrace]
  refine ⟨22340649460674753175226059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119150130456932016934538981 22340649460674753175226059)
  ·
    refine ⟨33510974191012129762839089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22340649460674753175226059 33510974191012129762839089)
    ·
      refine ⟨25133230643259097322129317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33510974191012129762839089 25133230643259097322129317)
      ·
        refine ⟨4712480745611080747899247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25133230643259097322129317 4712480745611080747899247)
        ·
          refine ⟨7068721118416621121848871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4712480745611080747899247 7068721118416621121848871)
          ·
            refine ⟨10603081677624931682773307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068721118416621121848871 10603081677624931682773307)
            ·
              refine ⟨15904622516437397524159961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10603081677624931682773307 15904622516437397524159961)
              ·
                refine ⟨11928466887328048143119971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15904622516437397524159961 11928466887328048143119971)
                ·
                  refine ⟨17892700330992072214679957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11928466887328048143119971 17892700330992072214679957)
                  ·
                    refine ⟨838720328015253385063123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17892700330992072214679957 838720328015253385063123)
                    ·
                      rfl

theorem cell23_4900206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_4900206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900206 prefixEnd_4900206 := by exact prefixLift 4900206
  have htrace : WordTrace (prefixWord ++ tailWord_4900206) baseStart_4900206 baseEnd_4900206 := by
    simpa [prefixWord, tailWord_4900206, baseEnd_4900206] using wordTrace_append hprefix tailTrace_4900206
  have hstable : (prefixWord ++ tailWord_4900206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900206).length < 2 ^ (prefixWord ++ tailWord_4900206).sum := by decide
  have hdescent : baseEnd_4900206 < baseStart_4900206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900213 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_4900213 : Nat := 118140960795 + 4900213 * 2 ^ 59
def prefixEnd_4900213 : Nat := 4983230072969 + 3 ^ 40 * 4900213 * 2
def baseEnd_4900213 : Nat := 2516164578410341627801837

theorem tailTrace_4900213 : CollatzResearch.WordTrace tailWord_4900213 prefixEnd_4900213 2516164578410341627801837 := by
  unfold tailWord_4900213
  simp only [CollatzResearch.WordTrace]
  refine ⟨178725450996372665597313293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119150300664248443731542195 178725450996372665597313293)
  ·
    refine ⟨67022044123639749598992485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178725450996372665597313293 67022044123639749598992485)
    ·
      refine ⟨12566633273182453049811091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67022044123639749598992485 12566633273182453049811091)
      ·
        refine ⟨18849949909773679574716637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12566633273182453049811091 18849949909773679574716637)
        ·
          refine ⟨7068731216165129840518739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18849949909773679574716637 7068731216165129840518739)
          ·
            refine ⟨10603096824247694760778109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068731216165129840518739 10603096824247694760778109)
            ·
              refine ⟨3976161309092885535291791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10603096824247694760778109 3976161309092885535291791)
              ·
                refine ⟨5964241963639328302937687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976161309092885535291791 5964241963639328302937687)
                ·
                  refine ⟨8946362945458992454406531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5964241963639328302937687 8946362945458992454406531)
                  ·
                    refine ⟨13419544418188488681609797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8946362945458992454406531 13419544418188488681609797)
                    ·
                      refine ⟨2516164578410341627801837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13419544418188488681609797 2516164578410341627801837)
                      ·
                        rfl

theorem cell23_4900213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_4900213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900213 prefixEnd_4900213 := by exact prefixLift 4900213
  have htrace : WordTrace (prefixWord ++ tailWord_4900213) baseStart_4900213 baseEnd_4900213 := by
    simpa [prefixWord, tailWord_4900213, baseEnd_4900213] using wordTrace_append hprefix tailTrace_4900213
  have hstable : (prefixWord ++ tailWord_4900213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900213).length < 2 ^ (prefixWord ++ tailWord_4900213).sum := by decide
  have hdescent : baseEnd_4900213 < baseStart_4900213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900229 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_4900229 : Nat := 118140960795 + 4900229 * 2 ^ 59
def prefixEnd_4900229 : Nat := 4983230072969 + 3 ^ 40 * 4900229 * 2
def baseEnd_4900229 : Nat := 2516172794100813565201763

theorem tailTrace_4900229 : CollatzResearch.WordTrace tailWord_4900229 prefixEnd_4900229 2516172794100813565201763 := by
  unfold tailWord_4900229
  simp only [CollatzResearch.WordTrace]
  refine ⟨178726034564314700329895741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119150689709543133553263827 178726034564314700329895741)
  ·
    refine ⟨67022262961618012623710903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178726034564314700329895741 67022262961618012623710903)
    ·
      refine ⟨100533394442427018935566355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67022262961618012623710903 100533394442427018935566355)
      ·
        refine ⟨150800091663640528403349533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100533394442427018935566355 150800091663640528403349533)
        ·
          refine ⟨56550034373865198151256075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150800091663640528403349533 56550034373865198151256075)
          ·
            refine ⟨84825051560797797226884113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56550034373865198151256075 84825051560797797226884113)
            ·
              refine ⟨63618788670598347920163085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84825051560797797226884113 63618788670598347920163085)
              ·
                refine ⟨23857045751474380470061157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63618788670598347920163085 23857045751474380470061157)
                ·
                  refine ⟨4473196078401446338136467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23857045751474380470061157 4473196078401446338136467)
                  ·
                    refine ⟨6709794117602169507204701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4473196078401446338136467 6709794117602169507204701)
                    ·
                      refine ⟨2516172794100813565201763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6709794117602169507204701 2516172794100813565201763)
                      ·
                        rfl

theorem cell23_4900229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_4900229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900229 prefixEnd_4900229 := by exact prefixLift 4900229
  have htrace : WordTrace (prefixWord ++ tailWord_4900229) baseStart_4900229 baseEnd_4900229 := by
    simpa [prefixWord, tailWord_4900229, baseEnd_4900229] using wordTrace_append hprefix tailTrace_4900229
  have hstable : (prefixWord ++ tailWord_4900229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900229).length < 2 ^ (prefixWord ++ tailWord_4900229).sum := by decide
  have hdescent : baseEnd_4900229 < baseStart_4900229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900232 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 2, 7]
def baseStart_4900232 : Nat := 118140960795 + 4900232 * 2 ^ 59
def prefixEnd_4900232 : Nat := 4983230072969 + 3 ^ 40 * 4900232 * 2
def baseEnd_4900232 : Nat := 838724778180925684488083

theorem tailTrace_4900232 : CollatzResearch.WordTrace tailWord_4900232 prefixEnd_4900232 838724778180925684488083 := by
  unfold tailWord_4900232
  simp only [CollatzResearch.WordTrace]
  refine ⟨89363071991651915921127475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119150762655535887894836633 89363071991651915921127475)
  ·
    refine ⟨134044607987477873881691213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89363071991651915921127475 134044607987477873881691213)
    ·
      refine ⟨50266727995304202705634205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134044607987477873881691213 50266727995304202705634205)
      ·
        refine ⟨18850022998239076014612827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50266727995304202705634205 18850022998239076014612827)
        ·
          refine ⟨28275034497358614021919241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18850022998239076014612827 28275034497358614021919241)
          ·
            refine ⟨21206275873018960516439431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28275034497358614021919241 21206275873018960516439431)
            ·
              refine ⟨31809413809528440774659147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21206275873018960516439431 31809413809528440774659147)
              ·
                refine ⟨47714120714292661161988721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31809413809528440774659147 47714120714292661161988721)
                ·
                  refine ⟨35785590535719495871491541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47714120714292661161988721 35785590535719495871491541)
                  ·
                    refine ⟨838724778180925684488083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35785590535719495871491541 838724778180925684488083)
                    ·
                      rfl

theorem cell23_4900232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_4900232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900232 prefixEnd_4900232 := by exact prefixLift 4900232
  have htrace : WordTrace (prefixWord ++ tailWord_4900232) baseStart_4900232 baseEnd_4900232 := by
    simpa [prefixWord, tailWord_4900232, baseEnd_4900232] using wordTrace_append hprefix tailTrace_4900232
  have hstable : (prefixWord ++ tailWord_4900232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900232).length < 2 ^ (prefixWord ++ tailWord_4900232).sum := by decide
  have hdescent : baseEnd_4900232 < baseStart_4900232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900256 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 1, 3, 2]
def baseStart_4900256 : Nat := 118140960795 + 4900256 * 2 ^ 59
def prefixEnd_4900256 : Nat := 4983230072969 + 3 ^ 40 * 4900256 * 2
def baseEnd_4900256 : Nat := 2516186658078484959564139

theorem tailTrace_4900256 : CollatzResearch.WordTrace tailWord_4900256 prefixEnd_4900256 2516186658078484959564139 := by
  unfold tailWord_4900256
  simp only [CollatzResearch.WordTrace]
  refine ⟨89363509667608441970564311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119151346223477922627419081 89363509667608441970564311)
  ·
    refine ⟨134045264501412662955846467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89363509667608441970564311 134045264501412662955846467)
    ·
      refine ⟨201067896752118994433769701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134045264501412662955846467 201067896752118994433769701)
      ·
        refine ⟨37700230641022311456331819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201067896752118994433769701 37700230641022311456331819)
        ·
          refine ⟨56550345961533467184497729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37700230641022311456331819 56550345961533467184497729)
          ·
            refine ⟨42412759471150100388373297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56550345961533467184497729 42412759471150100388373297)
            ·
              refine ⟨31809569603362575291279973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42412759471150100388373297 31809569603362575291279973)
              ·
                refine ⟨5964294300630482867114995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31809569603362575291279973 5964294300630482867114995)
                ·
                  refine ⟨8946441450945724300672493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5964294300630482867114995 8946441450945724300672493)
                  ·
                    refine ⟨3354915544104646612752185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8946441450945724300672493 3354915544104646612752185)
                    ·
                      refine ⟨2516186658078484959564139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354915544104646612752185 2516186658078484959564139)
                      ·
                        rfl

theorem cell23_4900256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_4900256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900256 prefixEnd_4900256 := by exact prefixLift 4900256
  have htrace : WordTrace (prefixWord ++ tailWord_4900256) baseStart_4900256 baseEnd_4900256 := by
    simpa [prefixWord, tailWord_4900256, baseEnd_4900256] using wordTrace_append hprefix tailTrace_4900256
  have hstable : (prefixWord ++ tailWord_4900256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900256).length < 2 ^ (prefixWord ++ tailWord_4900256).sum := by decide
  have hdescent : baseEnd_4900256 < baseStart_4900256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900272 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 3]
def baseStart_4900272 : Nat := 118140960795 + 4900272 * 2 ^ 59
def prefixEnd_4900272 : Nat := 4983230072969 + 3 ^ 40 * 4900272 * 2
def baseEnd_4900272 : Nat := 2516194873768956896964065

theorem tailTrace_4900272 : CollatzResearch.WordTrace tailWord_4900272 prefixEnd_4900272 2516194873768956896964065 := by
  unfold tailWord_4900272
  simp only [CollatzResearch.WordTrace]
  refine ⟨89363801451579459336855535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119151735268772612449140713 89363801451579459336855535)
  ·
    refine ⟨134045702177369189005283303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89363801451579459336855535 134045702177369189005283303)
    ·
      refine ⟨201068553266053783507924955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134045702177369189005283303 201068553266053783507924955)
      ·
        refine ⟨301602829899080675261887433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201068553266053783507924955 301602829899080675261887433)
        ·
          refine ⟨226202122424310506446415575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301602829899080675261887433 226202122424310506446415575)
          ·
            refine ⟨339303183636465759669623363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226202122424310506446415575 339303183636465759669623363)
            ·
              refine ⟨508954775454698639504435045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339303183636465759669623363 508954775454698639504435045)
              ·
                refine ⟨95429020397755994907081571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 508954775454698639504435045 95429020397755994907081571)
                ·
                  refine ⟨143143530596633992360622357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95429020397755994907081571 143143530596633992360622357)
                  ·
                    refine ⟨6709852996717218391904173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 143143530596633992360622357 6709852996717218391904173)
                    ·
                      refine ⟨2516194873768956896964065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6709852996717218391904173 2516194873768956896964065)
                      ·
                        rfl

theorem cell23_4900272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_4900272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900272 prefixEnd_4900272 := by exact prefixLift 4900272
  have htrace : WordTrace (prefixWord ++ tailWord_4900272) baseStart_4900272 baseEnd_4900272 := by
    simpa [prefixWord, tailWord_4900272, baseEnd_4900272] using wordTrace_append hprefix tailTrace_4900272
  have hstable : (prefixWord ++ tailWord_4900272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900272).length < 2 ^ (prefixWord ++ tailWord_4900272).sum := by decide
  have hdescent : baseEnd_4900272 < baseStart_4900272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900349 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_4900349 : Nat := 118140960795 + 4900349 * 2 ^ 59
def prefixEnd_4900349 : Nat := 4983230072969 + 3 ^ 40 * 4900349 * 2
def baseEnd_4900349 : Nat := 2516234411779353095701211

theorem tailTrace_4900349 : CollatzResearch.WordTrace tailWord_4900349 prefixEnd_4900349 2516234411779353095701211 := by
  unfold tailWord_4900349
  simp only [CollatzResearch.WordTrace]
  refine ⟨178730411323879960824264101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119153607549253307216176067 178730411323879960824264101)
  ·
    refine ⟨33511952123227492654549519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178730411323879960824264101 33511952123227492654549519)
    ·
      refine ⟨50267928184841238981824279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33511952123227492654549519 50267928184841238981824279)
      ·
        refine ⟨75401892277261858472736419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50267928184841238981824279 75401892277261858472736419)
        ·
          refine ⟨113102838415892787709104629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75401892277261858472736419 113102838415892787709104629)
          ·
            refine ⟨10603391101489948847728559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113102838415892787709104629 10603391101489948847728559)
            ·
              refine ⟨15905086652234923271592839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10603391101489948847728559 15905086652234923271592839)
              ·
                refine ⟨23857629978352384907389259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15905086652234923271592839 23857629978352384907389259)
                ·
                  refine ⟨35786444967528577361083889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23857629978352384907389259 35786444967528577361083889)
                  ·
                    refine ⟨26839833725646433020812917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35786444967528577361083889 26839833725646433020812917)
                    ·
                      refine ⟨2516234411779353095701211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26839833725646433020812917 2516234411779353095701211)
                      ·
                        rfl

theorem cell23_4900349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_4900349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900349 prefixEnd_4900349 := by exact prefixLift 4900349
  have htrace : WordTrace (prefixWord ++ tailWord_4900349) baseStart_4900349 baseEnd_4900349 := by
    simpa [prefixWord, tailWord_4900349, baseEnd_4900349] using wordTrace_append hprefix tailTrace_4900349
  have hstable : (prefixWord ++ tailWord_4900349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900349).length < 2 ^ (prefixWord ++ tailWord_4900349).sum := by decide
  have hdescent : baseEnd_4900349 < baseStart_4900349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900354 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_4900354 : Nat := 118140960795 + 4900354 * 2 ^ 59
def prefixEnd_4900354 : Nat := 4983230072969 + 3 ^ 40 * 4900354 * 2
def baseEnd_4900354 : Nat := 2516236979182625576138689

theorem tailTrace_4900354 : CollatzResearch.WordTrace tailWord_4900354 prefixEnd_4900354 2516236979182625576138689 := by
  unfold tailWord_4900354
  simp only [CollatzResearch.WordTrace]
  refine ⟨44682648422215461669549029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119153729125907897785464077 44682648422215461669549029)
  ·
    refine ⟨8377996579165399063040443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44682648422215461669549029 8377996579165399063040443)
    ·
      refine ⟨12566994868748098594560665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8377996579165399063040443 12566994868748098594560665)
      ·
        refine ⟨9425246151561073945920499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12566994868748098594560665 9425246151561073945920499)
        ·
          refine ⟨14137869227341610918880749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9425246151561073945920499 14137869227341610918880749)
          ·
            refine ⟨5301700960253104094580281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14137869227341610918880749 5301700960253104094580281)
            ·
              refine ⟨3976275720189828070935211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5301700960253104094580281 3976275720189828070935211)
              ·
                refine ⟨5964413580284742106402817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976275720189828070935211 5964413580284742106402817)
                ·
                  refine ⟨4473310185213556579802113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5964413580284742106402817 4473310185213556579802113)
                  ·
                    refine ⟨3354982638910167434851585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4473310185213556579802113 3354982638910167434851585)
                    ·
                      refine ⟨2516236979182625576138689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3354982638910167434851585 2516236979182625576138689)
                      ·
                        rfl

theorem cell23_4900354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_4900354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900354 prefixEnd_4900354 := by exact prefixLift 4900354
  have htrace : WordTrace (prefixWord ++ tailWord_4900354) baseStart_4900354 baseEnd_4900354 := by
    simpa [prefixWord, tailWord_4900354, baseEnd_4900354] using wordTrace_append hprefix tailTrace_4900354
  have hstable : (prefixWord ++ tailWord_4900354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900354).length < 2 ^ (prefixWord ++ tailWord_4900354).sum := by decide
  have hdescent : baseEnd_4900354 < baseStart_4900354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900369 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 5, 4]
def baseStart_4900369 : Nat := 118140960795 + 4900369 * 2 ^ 59
def prefixEnd_4900369 : Nat := 4983230072969 + 3 ^ 40 * 4900369 * 2
def baseEnd_4900369 : Nat := 838748227130814339150373

theorem tailTrace_4900369 : CollatzResearch.WordTrace tailWord_4900369 prefixEnd_4900369 838748227130814339150373 := by
  unfold tailWord_4900369
  simp only [CollatzResearch.WordTrace]
  refine ⟨178731140783807504239992161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119154093855871669493328107 178731140783807504239992161)
  ·
    refine ⟨134048355587855628179994121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178731140783807504239992161 134048355587855628179994121)
    ·
      refine ⟨100536266690891721134995591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134048355587855628179994121 100536266690891721134995591)
      ·
        refine ⟨150804400036337581702493387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100536266690891721134995591 150804400036337581702493387)
        ·
          refine ⟨226206600054506372553740081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150804400036337581702493387 226206600054506372553740081)
          ·
            refine ⟨169654950040879779415305061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226206600054506372553740081 169654950040879779415305061)
            ·
              refine ⟨31810303132664958640369699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169654950040879779415305061 31810303132664958640369699)
              ·
                refine ⟨47715454698997437960554549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31810303132664958640369699 47715454698997437960554549)
                ·
                  refine ⟨4473323878031009808801989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47715454698997437960554549 4473323878031009808801989)
                  ·
                    refine ⟨838748227130814339150373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473323878031009808801989 838748227130814339150373)
                    ·
                      rfl

theorem cell23_4900369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_4900369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900369 prefixEnd_4900369 := by exact prefixLift 4900369
  have htrace : WordTrace (prefixWord ++ tailWord_4900369) baseStart_4900369 baseEnd_4900369 := by
    simpa [prefixWord, tailWord_4900369, baseEnd_4900369] using wordTrace_append hprefix tailTrace_4900369
  have hstable : (prefixWord ++ tailWord_4900369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900369).length < 2 ^ (prefixWord ++ tailWord_4900369).sum := by decide
  have hdescent : baseEnd_4900369 < baseStart_4900369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900403 : List Nat := [1, 1, 1, 2, 4, 4, 1, 4, 1, 4]
def baseStart_4900403 : Nat := 118140960795 + 4900403 * 2 ^ 59
def prefixEnd_4900403 : Nat := 4983230072969 + 3 ^ 40 * 4900403 * 2
def baseEnd_4900403 : Nat := 838754046578231961475321

theorem tailTrace_4900403 : CollatzResearch.WordTrace tailWord_4900403 prefixEnd_4900403 838754046578231961475321 := by
  unfold tailWord_4900403
  simp only [CollatzResearch.WordTrace]
  refine ⟨178732380865684328046729863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119154920577122885364486575 178732380865684328046729863)
  ·
    refine ⟨268098571298526492070094795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178732380865684328046729863 268098571298526492070094795)
    ·
      refine ⟨402147856947789738105142193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268098571298526492070094795 402147856947789738105142193)
      ·
        refine ⟨301610892710842303578856645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402147856947789738105142193 301610892710842303578856645)
        ·
          refine ⟨56552042383282931921035621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 301610892710842303578856645 56552042383282931921035621)
          ·
            refine ⟨10603507946865549735194179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56552042383282931921035621 10603507946865549735194179)
            ·
              refine ⟨15905261920298324602791269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10603507946865549735194179 15905261920298324602791269)
              ·
                refine ⟨2982236610055935863023363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15905261920298324602791269 2982236610055935863023363)
                ·
                  refine ⟨4473354915083903794535045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982236610055935863023363 4473354915083903794535045)
                  ·
                    refine ⟨838754046578231961475321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473354915083903794535045 838754046578231961475321)
                    ·
                      rfl

theorem cell23_4900403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 4].length) (baseStart_4900403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900403 prefixEnd_4900403 := by exact prefixLift 4900403
  have htrace : WordTrace (prefixWord ++ tailWord_4900403) baseStart_4900403 baseEnd_4900403 := by
    simpa [prefixWord, tailWord_4900403, baseEnd_4900403] using wordTrace_append hprefix tailTrace_4900403
  have hstable : (prefixWord ++ tailWord_4900403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900403).length < 2 ^ (prefixWord ++ tailWord_4900403).sum := by decide
  have hdescent : baseEnd_4900403 < baseStart_4900403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900503 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_4900503 : Nat := 118140960795 + 4900503 * 2 ^ 59
def prefixEnd_4900503 : Nat := 4983230072969 + 3 ^ 40 * 4900503 * 2
def baseEnd_4900503 : Nat := 2516313487800145493175503

theorem tailTrace_4900503 : CollatzResearch.WordTrace tailWord_4900503 prefixEnd_4900503 2516313487800145493175503 := by
  unfold tailWord_4900503
  simp only [CollatzResearch.WordTrace]
  refine ⟨178736028165322045125370163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119157352110214696750246775 178736028165322045125370163)
  ·
    refine ⟨268104042247983067688055245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178736028165322045125370163 268104042247983067688055245)
    ·
      refine ⟨100539015842993650383020717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268104042247983067688055245 100539015842993650383020717)
      ·
        refine ⟨37702130941122618893632769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100539015842993650383020717 37702130941122618893632769)
        ·
          refine ⟨28276598205841964170224577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37702130941122618893632769 28276598205841964170224577)
          ·
            refine ⟨21207448654381473127668433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28276598205841964170224577 21207448654381473127668433)
            ·
              refine ⟨15905586490786104845751325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21207448654381473127668433 15905586490786104845751325)
              ·
                refine ⟨5964594934044789317156747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15905586490786104845751325 5964594934044789317156747)
                ·
                  refine ⟨8946892401067183975735121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5964594934044789317156747 8946892401067183975735121)
                  ·
                    refine ⟨6710169300800387981801341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8946892401067183975735121 6710169300800387981801341)
                    ·
                      refine ⟨2516313487800145493175503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6710169300800387981801341 2516313487800145493175503)
                      ·
                        rfl

theorem cell23_4900503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_4900503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900503 prefixEnd_4900503 := by exact prefixLift 4900503
  have htrace : WordTrace (prefixWord ++ tailWord_4900503) baseStart_4900503 baseEnd_4900503 := by
    simpa [prefixWord, tailWord_4900503, baseEnd_4900503] using wordTrace_append hprefix tailTrace_4900503
  have hstable : (prefixWord ++ tailWord_4900503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900503).length < 2 ^ (prefixWord ++ tailWord_4900503).sum := by decide
  have hdescent : baseEnd_4900503 < baseStart_4900503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900543 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 3, 3, 2]
def baseStart_4900543 : Nat := 118140960795 + 4900543 * 2 ^ 59
def prefixEnd_4900543 : Nat := 4983230072969 + 3 ^ 40 * 4900543 * 2
def baseEnd_4900543 : Nat := 2516334027026325336675319

theorem tailTrace_4900543 : CollatzResearch.WordTrace tailWord_4900543 prefixEnd_4900543 2516334027026325336675319 := by
  unfold tailWord_4900543
  simp only [CollatzResearch.WordTrace]
  refine ⟨178737487085177131956826283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119158324723451421304550855 178737487085177131956826283)
  ·
    refine ⟨268106230627765697935239425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178737487085177131956826283 268106230627765697935239425)
    ·
      refine ⟨201079672970824273451429569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268106230627765697935239425 201079672970824273451429569)
      ·
        refine ⟨150809754728118205088572177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201079672970824273451429569 150809754728118205088572177)
        ·
          refine ⟨113107316046088653816429133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150809754728118205088572177 113107316046088653816429133)
          ·
            refine ⟨42415243517283245181160925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113107316046088653816429133 42415243517283245181160925)
            ·
              refine ⟨15905716318981216942935347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42415243517283245181160925 15905716318981216942935347)
              ·
                refine ⟨23858574478471825414403021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15905716318981216942935347 23858574478471825414403021)
                ·
                  refine ⟨8946965429426934530401133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23858574478471825414403021 8946965429426934530401133)
                  ·
                    refine ⟨3355112036035100448900425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8946965429426934530401133 3355112036035100448900425)
                    ·
                      refine ⟨2516334027026325336675319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355112036035100448900425 2516334027026325336675319)
                      ·
                        rfl

theorem cell23_4900543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_4900543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900543 prefixEnd_4900543 := by exact prefixLift 4900543
  have htrace : WordTrace (prefixWord ++ tailWord_4900543) baseStart_4900543 baseEnd_4900543 := by
    simpa [prefixWord, tailWord_4900543, baseEnd_4900543] using wordTrace_append hprefix tailTrace_4900543
  have hstable : (prefixWord ++ tailWord_4900543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900543).length < 2 ^ (prefixWord ++ tailWord_4900543).sum := by decide
  have hdescent : baseEnd_4900543 < baseStart_4900543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900549 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_4900549 : Nat := 118140960795 + 4900549 * 2 ^ 59
def prefixEnd_4900549 : Nat := 4983230072969 + 3 ^ 40 * 4900549 * 2
def baseEnd_4900549 : Nat := 838779035970084104400097

theorem tailTrace_4900549 : CollatzResearch.WordTrace tailWord_4900549 prefixEnd_4900549 838779035970084104400097 := by
  unfold tailWord_4900549
  simp only [CollatzResearch.WordTrace]
  refine ⟨178737705923155394981544701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119158470615436929987696467 178737705923155394981544701)
  ·
    refine ⟨67026639721183273118079263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178737705923155394981544701 67026639721183273118079263)
    ·
      refine ⟨100539959581774909677118895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67026639721183273118079263 100539959581774909677118895)
      ·
        refine ⟨150809939372662364515678343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100539959581774909677118895 150809939372662364515678343)
        ·
          refine ⟨226214909058993546773517515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150809939372662364515678343 226214909058993546773517515)
          ·
            refine ⟨339322363588490320160276273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226214909058993546773517515 339322363588490320160276273)
            ·
              refine ⟨254491772691367740120207205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339322363588490320160276273 254491772691367740120207205)
              ·
                refine ⟨47717207379631451272538851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254491772691367740120207205 47717207379631451272538851)
                ·
                  refine ⟨71575811069447176908808277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47717207379631451272538851 71575811069447176908808277)
                  ·
                    refine ⟨838779035970084104400097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71575811069447176908808277 838779035970084104400097)
                    ·
                      rfl

theorem cell23_4900549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_4900549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900549 prefixEnd_4900549 := by exact prefixLift 4900549
  have htrace : WordTrace (prefixWord ++ tailWord_4900549) baseStart_4900549 baseEnd_4900549 := by
    simpa [prefixWord, tailWord_4900549, baseEnd_4900549] using wordTrace_append hprefix tailTrace_4900549
  have hstable : (prefixWord ++ tailWord_4900549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900549).length < 2 ^ (prefixWord ++ tailWord_4900549).sum := by decide
  have hdescent : baseEnd_4900549 < baseStart_4900549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900576 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 3]
def baseStart_4900576 : Nat := 118140960795 + 4900576 * 2 ^ 59
def prefixEnd_4900576 : Nat := 4983230072969 + 3 ^ 40 * 4900576 * 2
def baseEnd_4900576 : Nat := 2516350971887923707562667

theorem tailTrace_4900576 : CollatzResearch.WordTrace tailWord_4900576 prefixEnd_4900576 2516350971887923707562667 := by
  unfold tailWord_4900576
  simp only [CollatzResearch.WordTrace]
  refine ⟨89369345347028789296388791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119159127129371719061851721 89369345347028789296388791)
  ·
    refine ⟨134054018020543183944583187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89369345347028789296388791 134054018020543183944583187)
    ·
      refine ⟨201081027030814775916874781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134054018020543183944583187 201081027030814775916874781)
      ·
        refine ⟨75405385136555540968828043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201081027030814775916874781 75405385136555540968828043)
        ·
          refine ⟨113108077704833311453242065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75405385136555540968828043 113108077704833311453242065)
          ·
            refine ⟨84831058278624983589931549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113108077704833311453242065 84831058278624983589931549)
            ·
              refine ⟨31811646854484368846224331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84831058278624983589931549 31811646854484368846224331)
              ·
                refine ⟨47717470281726553269336497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31811646854484368846224331 47717470281726553269336497)
                ·
                  refine ⟨35788102711294914952002373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47717470281726553269336497 35788102711294914952002373)
                  ·
                    refine ⟨6710269258367796553500445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35788102711294914952002373 6710269258367796553500445)
                    ·
                      refine ⟨2516350971887923707562667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6710269258367796553500445 2516350971887923707562667)
                      ·
                        rfl

theorem cell23_4900576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_4900576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900576 prefixEnd_4900576 := by exact prefixLift 4900576
  have htrace : WordTrace (prefixWord ++ tailWord_4900576) baseStart_4900576 baseEnd_4900576 := by
    simpa [prefixWord, tailWord_4900576, baseEnd_4900576] using wordTrace_append hprefix tailTrace_4900576
  have hstable : (prefixWord ++ tailWord_4900576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900576).length < 2 ^ (prefixWord ++ tailWord_4900576).sum := by decide
  have hdescent : baseEnd_4900576 < baseStart_4900576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900586 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_4900586 : Nat := 118140960795 + 4900586 * 2 ^ 59
def prefixEnd_4900586 : Nat := 4983230072969 + 3 ^ 40 * 4900586 * 2
def baseEnd_4900586 : Nat := 2516356106694468668437621

theorem tailTrace_4900586 : CollatzResearch.WordTrace tailWord_4900586 prefixEnd_4900586 2516356106694468668437621 := by
  unfold tailWord_4900586
  simp only [CollatzResearch.WordTrace]
  refine ⟨44684763856005337575160403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119159370282680900200427741 44684763856005337575160403)
  ·
    refine ⟨67027145784008006362740605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44684763856005337575160403 67027145784008006362740605)
    ·
      refine ⟨25135179669003002386027727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67027145784008006362740605 25135179669003002386027727)
      ·
        refine ⟨37702769503504503579041591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25135179669003002386027727 37702769503504503579041591)
        ·
          refine ⟨56554154255256755368562387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37702769503504503579041591 56554154255256755368562387)
          ·
            refine ⟨84831231382885133052843581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56554154255256755368562387 84831231382885133052843581)
            ·
              refine ⟨31811711768581924894816343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84831231382885133052843581 31811711768581924894816343)
              ·
                refine ⟨47717567652872887342224515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31811711768581924894816343 47717567652872887342224515)
                ·
                  refine ⟨71576351479309331013336773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47717567652872887342224515 71576351479309331013336773)
                  ·
                    refine ⟨13420565902370499565000645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71576351479309331013336773 13420565902370499565000645)
                    ·
                      refine ⟨2516356106694468668437621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13420565902370499565000645 2516356106694468668437621)
                      ·
                        rfl

theorem cell23_4900586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_4900586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900586 prefixEnd_4900586 := by exact prefixLift 4900586
  have htrace : WordTrace (prefixWord ++ tailWord_4900586) baseStart_4900586 baseEnd_4900586 := by
    simpa [prefixWord, tailWord_4900586, baseEnd_4900586] using wordTrace_append hprefix tailTrace_4900586
  have hstable : (prefixWord ++ tailWord_4900586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900586).length < 2 ^ (prefixWord ++ tailWord_4900586).sum := by decide
  have hdescent : baseEnd_4900586 < baseStart_4900586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900590 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_4900590 : Nat := 118140960795 + 4900590 * 2 ^ 59
def prefixEnd_4900590 : Nat := 4983230072969 + 3 ^ 40 * 4900590 * 2
def baseEnd_4900590 : Nat := 2516358160617086652787603

theorem tailTrace_4900590 : CollatzResearch.WordTrace tailWord_4900590 prefixEnd_4900590 2516358160617086652787603 := by
  unfold tailWord_4900590
  simp only [CollatzResearch.WordTrace]
  refine ⟨22342400164500857372973403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119159467544004572655858149 22342400164500857372973403)
  ·
    refine ⟨33513600246751286059460105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22342400164500857372973403 33513600246751286059460105)
    ·
      refine ⟨25135200185063464544595079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33513600246751286059460105 25135200185063464544595079)
      ·
        refine ⟨37702800277595196816892619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25135200185063464544595079 37702800277595196816892619)
        ·
          refine ⟨56554200416392795225338929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37702800277595196816892619 56554200416392795225338929)
          ·
            refine ⟨42415650312294596419004197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56554200416392795225338929 42415650312294596419004197)
            ·
              refine ⟨7952934433555236828563287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42415650312294596419004197 7952934433555236828563287)
              ·
                refine ⟨11929401650332855242844931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7952934433555236828563287 11929401650332855242844931)
                ·
                  refine ⟨17894102475499282864267397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11929401650332855242844931 17894102475499282864267397)
                  ·
                    refine ⟨3355144214156115537050137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17894102475499282864267397 3355144214156115537050137)
                    ·
                      refine ⟨2516358160617086652787603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355144214156115537050137 2516358160617086652787603)
                      ·
                        rfl

theorem cell23_4900590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_4900590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900590 prefixEnd_4900590 := by exact prefixLift 4900590
  have htrace : WordTrace (prefixWord ++ tailWord_4900590) baseStart_4900590 baseEnd_4900590 := by
    simpa [prefixWord, tailWord_4900590, baseEnd_4900590] using wordTrace_append hprefix tailTrace_4900590
  have hstable : (prefixWord ++ tailWord_4900590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900590).length < 2 ^ (prefixWord ++ tailWord_4900590).sum := by decide
  have hdescent : baseEnd_4900590 < baseStart_4900590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900636 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4900636 : Nat := 118140960795 + 4900636 * 2 ^ 59
def prefixEnd_4900636 : Nat := 4983230072969 + 3 ^ 40 * 4900636 * 2
def baseEnd_4900636 : Nat := 2516381780727193472812391

theorem tailTrace_4900636 : CollatzResearch.WordTrace tailWord_4900636 prefixEnd_4900636 2516381780727193472812391 := by
  unfold tailWord_4900636
  simp only [CollatzResearch.WordTrace]
  refine ⟨89370439536920104419980881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119160586049226805893307841 89370439536920104419980881)
  ·
    refine ⟨67027829652690078314985661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89370439536920104419980881 67027829652690078314985661)
    ·
      refine ⟨25135436119758779368119623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67027829652690078314985661 25135436119758779368119623)
      ·
        refine ⟨37703154179638169052179435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25135436119758779368119623 37703154179638169052179435)
        ·
          refine ⟨56554731269457253578269153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37703154179638169052179435 56554731269457253578269153)
          ·
            refine ⟨42416048452092940183701865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56554731269457253578269153 42416048452092940183701865)
            ·
              refine ⟨31812036339069705137776399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42416048452092940183701865 31812036339069705137776399)
              ·
                refine ⟨47718054508604557706664599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31812036339069705137776399 47718054508604557706664599)
                ·
                  refine ⟨71577081762906836559996899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47718054508604557706664599 71577081762906836559996899)
                  ·
                    refine ⟨107365622644360254839995349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71577081762906836559996899 107365622644360254839995349)
                    ·
                      refine ⟨2516381780727193472812391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107365622644360254839995349 2516381780727193472812391)
                      ·
                        rfl

theorem cell23_4900636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4900636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900636 prefixEnd_4900636 := by exact prefixLift 4900636
  have htrace : WordTrace (prefixWord ++ tailWord_4900636) baseStart_4900636 baseEnd_4900636 := by
    simpa [prefixWord, tailWord_4900636, baseEnd_4900636] using wordTrace_append hprefix tailTrace_4900636
  have hstable : (prefixWord ++ tailWord_4900636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900636).length < 2 ^ (prefixWord ++ tailWord_4900636).sum := by decide
  have hdescent : baseEnd_4900636 < baseStart_4900636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900663 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 4, 4, 2]
def baseStart_4900663 : Nat := 118140960795 + 4900663 * 2 ^ 59
def prefixEnd_4900663 : Nat := 4983230072969 + 3 ^ 40 * 4900663 * 2
def baseEnd_4900663 : Nat := 2516395644704864867174767

theorem tailTrace_4900663 : CollatzResearch.WordTrace tailWord_4900663 prefixEnd_4900663 2516395644704864867174767 := by
  unfold tailWord_4900663
  simp only [CollatzResearch.WordTrace]
  refine ⟨178741863844742392451194643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119161242563161594967463095 178741863844742392451194643)
  ·
    refine ⟨268112795767113588676791965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178741863844742392451194643 268112795767113588676791965)
    ·
      refine ⟨100542298412667595753796987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268112795767113588676791965 100542298412667595753796987)
      ·
        refine ⟨150813447619001393630695481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100542298412667595753796987 150813447619001393630695481)
        ·
          refine ⟨113110085714251045223021611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150813447619001393630695481 113110085714251045223021611)
          ·
            refine ⟨169665128571376567834532417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113110085714251045223021611 169665128571376567834532417)
            ·
              refine ⟨127248846428532425875899313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169665128571376567834532417 127248846428532425875899313)
              ·
                refine ⟨95436634821399319406924485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127248846428532425875899313 95436634821399319406924485)
                ·
                  refine ⟨17894369029012372388798341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95436634821399319406924485 17894369029012372388798341)
                  ·
                    refine ⟨3355194192939819822899689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17894369029012372388798341 3355194192939819822899689)
                    ·
                      refine ⟨2516395644704864867174767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355194192939819822899689 2516395644704864867174767)
                      ·
                        rfl

theorem cell23_4900663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_4900663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900663 prefixEnd_4900663 := by exact prefixLift 4900663
  have htrace : WordTrace (prefixWord ++ tailWord_4900663) baseStart_4900663 baseEnd_4900663 := by
    simpa [prefixWord, tailWord_4900663, baseEnd_4900663] using wordTrace_append hprefix tailTrace_4900663
  have hstable : (prefixWord ++ tailWord_4900663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900663).length < 2 ^ (prefixWord ++ tailWord_4900663).sum := by decide
  have hdescent : baseEnd_4900663 < baseStart_4900663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900690 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_4900690 : Nat := 118140960795 + 4900690 * 2 ^ 59
def prefixEnd_4900690 : Nat := 4983230072969 + 3 ^ 40 * 4900690 * 2
def baseEnd_4900690 : Nat := 838803169560845420512381

theorem tailTrace_4900690 : CollatzResearch.WordTrace tailWord_4900690 prefixEnd_4900690 838803169560845420512381 := by
  unfold tailWord_4900690
  simp only [CollatzResearch.WordTrace]
  refine ⟨44685712153911144015606881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119161899077096384041618349 44685712153911144015606881)
  ·
    refine ⟨33514284115433358011705161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44685712153911144015606881 33514284115433358011705161)
    ·
      refine ⟨25135713086575018508778871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33514284115433358011705161 25135713086575018508778871)
      ·
        refine ⟨37703569629862527763168307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25135713086575018508778871 37703569629862527763168307)
        ·
          refine ⟨56555354444793791644752461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37703569629862527763168307 56555354444793791644752461)
          ·
            refine ⟨21208257916797671866782173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56555354444793791644752461 21208257916797671866782173)
            ·
              refine ⟨7953096718799126950043315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21208257916797671866782173 7953096718799126950043315)
              ·
                refine ⟨11929645078198690425064973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7953096718799126950043315 11929645078198690425064973)
                ·
                  refine ⟨4473616904324508909399365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11929645078198690425064973 4473616904324508909399365)
                  ·
                    refine ⟨838803169560845420512381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473616904324508909399365 838803169560845420512381)
                    ·
                      rfl

theorem cell23_4900690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_4900690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900690 prefixEnd_4900690 := by exact prefixLift 4900690
  have htrace : WordTrace (prefixWord ++ tailWord_4900690) baseStart_4900690 baseEnd_4900690 := by
    simpa [prefixWord, tailWord_4900690, baseEnd_4900690] using wordTrace_append hprefix tailTrace_4900690
  have hstable : (prefixWord ++ tailWord_4900690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900690).length < 2 ^ (prefixWord ++ tailWord_4900690).sum := by decide
  have hdescent : baseEnd_4900690 < baseStart_4900690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900703 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 6]
def baseStart_4900703 : Nat := 118140960795 + 4900703 * 2 ^ 59
def prefixEnd_4900703 : Nat := 4983230072969 + 3 ^ 40 * 4900703 * 2
def baseEnd_4900703 : Nat := 279601798214560523408287

theorem tailTrace_4900703 : CollatzResearch.WordTrace tailWord_4900703 prefixEnd_4900703 279601798214560523408287 := by
  unfold tailWord_4900703
  simp only [CollatzResearch.WordTrace]
  refine ⟨178743322764597479282650763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119162215176398319521767175 178743322764597479282650763)
  ·
    refine ⟨268114984146896218923976145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178743322764597479282650763 268114984146896218923976145)
    ·
      refine ⟨201086238110172164192982109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268114984146896218923976145 201086238110172164192982109)
      ·
        refine ⟨75407339291314561572368291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201086238110172164192982109 75407339291314561572368291)
        ·
          refine ⟨113111008936971842358552437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75407339291314561572368291 113111008936971842358552437)
          ·
            refine ⟨10604157087841110221114291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113111008936971842358552437 10604157087841110221114291)
            ·
              refine ⟨15906235631761665331671437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10604157087841110221114291 15906235631761665331671437)
              ·
                refine ⟨5964838361910624499376789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15906235631761665331671437 5964838361910624499376789)
                ·
                  refine ⟨279601798214560523408287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5964838361910624499376789 279601798214560523408287)
                  ·
                    rfl

theorem cell23_4900703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 6].length) (baseStart_4900703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900703 prefixEnd_4900703 := by exact prefixLift 4900703
  have htrace : WordTrace (prefixWord ++ tailWord_4900703) baseStart_4900703 baseEnd_4900703 := by
    simpa [prefixWord, tailWord_4900703, baseEnd_4900703] using wordTrace_append hprefix tailTrace_4900703
  have hstable : (prefixWord ++ tailWord_4900703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900703).length < 2 ^ (prefixWord ++ tailWord_4900703).sum := by decide
  have hdescent : baseEnd_4900703 < baseStart_4900703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900737 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 6]
def baseStart_4900737 : Nat := 118140960795 + 4900737 * 2 ^ 59
def prefixEnd_4900737 : Nat := 4983230072969 + 3 ^ 40 * 4900737 * 2
def baseEnd_4900737 : Nat := 279603738030366397516603

theorem tailTrace_4900737 : CollatzResearch.WordTrace tailWord_4900737 prefixEnd_4900737 279603738030366397516603 := by
  unfold tailWord_4900737
  simp only [CollatzResearch.WordTrace]
  refine ⟨178744562846474303089388465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119163041897649535392925643 178744562846474303089388465)
  ·
    refine ⟨134058422134855727317041349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178744562846474303089388465 134058422134855727317041349)
    ·
      refine ⟨25135954150285448871945253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134058422134855727317041349 25135954150285448871945253)
      ·
        refine ⟨4712991403178521663489735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25135954150285448871945253 4712991403178521663489735)
        ·
          refine ⟨7069487104767782495234603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4712991403178521663489735 7069487104767782495234603)
          ·
            refine ⟨10604230657151673742851905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7069487104767782495234603 10604230657151673742851905)
            ·
              refine ⟨7953172992863755307138929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10604230657151673742851905 7953172992863755307138929)
              ·
                refine ⟨5964879744647816480354197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7953172992863755307138929 5964879744647816480354197)
                ·
                  refine ⟨279603738030366397516603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5964879744647816480354197 279603738030366397516603)
                  ·
                    rfl

theorem cell23_4900737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 6].length) (baseStart_4900737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900737 prefixEnd_4900737 := by exact prefixLift 4900737
  have htrace : WordTrace (prefixWord ++ tailWord_4900737) baseStart_4900737 baseEnd_4900737 := by
    simpa [prefixWord, tailWord_4900737, baseEnd_4900737] using wordTrace_append hprefix tailTrace_4900737
  have hstable : (prefixWord ++ tailWord_4900737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900737).length < 2 ^ (prefixWord ++ tailWord_4900737).sum := by decide
  have hdescent : baseEnd_4900737 < baseStart_4900737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900753 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_4900753 : Nat := 118140960795 + 4900753 * 2 ^ 59
def prefixEnd_4900753 : Nat := 4983230072969 + 3 ^ 40 * 4900753 * 2
def baseEnd_4900753 : Nat := 2516441857963769515049353

theorem tailTrace_4900753 : CollatzResearch.WordTrace tailWord_4900753 prefixEnd_4900753 2516441857963769515049353 := by
  unfold tailWord_4900753
  simp only [CollatzResearch.WordTrace]
  refine ⟨178745146414416337821970913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119163430942944225214647275 178745146414416337821970913)
  ·
    refine ⟨134058859810812253366478185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178745146414416337821970913 134058859810812253366478185)
    ·
      refine ⟨100544144858109190024858639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134058859810812253366478185 100544144858109190024858639)
      ·
        refine ⟨150816217287163785037287959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100544144858109190024858639 150816217287163785037287959)
        ·
          refine ⟨226224325930745677555931939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150816217287163785037287959 226224325930745677555931939)
          ·
            refine ⟨339336488896118516333897909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226224325930745677555931939 339336488896118516333897909)
            ·
              refine ⟨31812795834011110906302929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 339336488896118516333897909 31812795834011110906302929)
              ·
                refine ⟨23859596875508333179727197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31812795834011110906302929 23859596875508333179727197)
                ·
                  refine ⟨8947348828315624942397699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23859596875508333179727197 8947348828315624942397699)
                  ·
                    refine ⟨13421023242473437413596549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8947348828315624942397699 13421023242473437413596549)
                    ·
                      refine ⟨2516441857963769515049353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13421023242473437413596549 2516441857963769515049353)
                      ·
                        rfl

theorem cell23_4900753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_4900753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900753 prefixEnd_4900753 := by exact prefixLift 4900753
  have htrace : WordTrace (prefixWord ++ tailWord_4900753) baseStart_4900753 baseEnd_4900753 := by
    simpa [prefixWord, tailWord_4900753, baseEnd_4900753] using wordTrace_append hprefix tailTrace_4900753
  have hstable : (prefixWord ++ tailWord_4900753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900753).length < 2 ^ (prefixWord ++ tailWord_4900753).sum := by decide
  have hdescent : baseEnd_4900753 < baseStart_4900753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900783 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_4900783 : Nat := 118140960795 + 4900783 * 2 ^ 59
def prefixEnd_4900783 : Nat := 4983230072969 + 3 ^ 40 * 4900783 * 2
def baseEnd_4900783 : Nat := 2516457262383404397674215

theorem tailTrace_4900783 : CollatzResearch.WordTrace tailWord_4900783 prefixEnd_4900783 2516457262383404397674215 := by
  unfold tailWord_4900783
  simp only [CollatzResearch.WordTrace]
  refine ⟨178746240604307652945563003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119164160402871768630375335 178746240604307652945563003)
  ·
    refine ⟨268119360906461479418344505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178746240604307652945563003 268119360906461479418344505)
    ·
      refine ⟨201089520679846109563758379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268119360906461479418344505 201089520679846109563758379)
      ·
        refine ⟨301634281019769164345637569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201089520679846109563758379 301634281019769164345637569)
        ·
          refine ⟨226225710764826873259228177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301634281019769164345637569 226225710764826873259228177)
          ·
            refine ⟨169669283073620154944421133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226225710764826873259228177 169669283073620154944421133)
            ·
              refine ⟨63625981152607558104157925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169669283073620154944421133 63625981152607558104157925)
              ·
                refine ⟨11929871466113917144529611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63625981152607558104157925 11929871466113917144529611)
                ·
                  refine ⟨17894807199170875716794417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11929871466113917144529611 17894807199170875716794417)
                  ·
                    refine ⟨13421105399378156787595813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17894807199170875716794417 13421105399378156787595813)
                    ·
                      refine ⟨2516457262383404397674215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13421105399378156787595813 2516457262383404397674215)
                      ·
                        rfl

theorem cell23_4900783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_4900783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900783 prefixEnd_4900783 := by exact prefixLift 4900783
  have htrace : WordTrace (prefixWord ++ tailWord_4900783) baseStart_4900783 baseEnd_4900783 := by
    simpa [prefixWord, tailWord_4900783, baseEnd_4900783] using wordTrace_append hprefix tailTrace_4900783
  have hstable : (prefixWord ++ tailWord_4900783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900783).length < 2 ^ (prefixWord ++ tailWord_4900783).sum := by decide
  have hdescent : baseEnd_4900783 < baseStart_4900783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900797 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_4900797 : Nat := 118140960795 + 4900797 * 2 ^ 59
def prefixEnd_4900797 : Nat := 4983230072969 + 3 ^ 40 * 4900797 * 2
def baseEnd_4900797 : Nat := 838821483704189114299717

theorem tailTrace_4900797 : CollatzResearch.WordTrace tailWord_4900797 prefixEnd_4900797 838821483704189114299717 := by
  unfold tailWord_4900797
  simp only [CollatzResearch.WordTrace]
  refine ⟨178746751226256933336572645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119164500817504622224381763 178746751226256933336572645)
  ·
    refine ⟨33515015854923175000607371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178746751226256933336572645 33515015854923175000607371)
    ·
      refine ⟨50272523782384762500911057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33515015854923175000607371 50272523782384762500911057)
      ·
        refine ⟨37704392836788571875683293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50272523782384762500911057 37704392836788571875683293)
        ·
          refine ⟨14139147313795714453381235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37704392836788571875683293 14139147313795714453381235)
          ·
            refine ⟨21208720970693571680071853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14139147313795714453381235 21208720970693571680071853)
            ·
              refine ⟨7953270364010089380026945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21208720970693571680071853 7953270364010089380026945)
              ·
                refine ⟨5964952773007567035020209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7953270364010089380026945 5964952773007567035020209)
                ·
                  refine ⟨4473714579755675276265157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5964952773007567035020209 4473714579755675276265157)
                  ·
                    refine ⟨838821483704189114299717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473714579755675276265157 838821483704189114299717)
                    ·
                      rfl

theorem cell23_4900797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_4900797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900797 prefixEnd_4900797 := by exact prefixLift 4900797
  have htrace : WordTrace (prefixWord ++ tailWord_4900797) baseStart_4900797 baseEnd_4900797 := by
    simpa [prefixWord, tailWord_4900797, baseEnd_4900797] using wordTrace_append hprefix tailTrace_4900797
  have hstable : (prefixWord ++ tailWord_4900797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900797).length < 2 ^ (prefixWord ++ tailWord_4900797).sum := by decide
  have hdescent : baseEnd_4900797 < baseStart_4900797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900833 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_4900833 : Nat := 118140960795 + 4900833 * 2 ^ 59
def prefixEnd_4900833 : Nat := 4983230072969 + 3 ^ 40 * 4900833 * 2
def baseEnd_4900833 : Nat := 2516482936416129202048985

theorem tailTrace_4900833 : CollatzResearch.WordTrace tailWord_4900833 prefixEnd_4900833 2516482936416129202048985 := by
  unfold tailWord_4900833
  simp only [CollatzResearch.WordTrace]
  refine ⟨178748064254126511484883153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119165376169417674323255435 178748064254126511484883153)
  ·
    refine ⟨134061048190594883613662365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178748064254126511484883153 134061048190594883613662365)
    ·
      refine ⟨50272893071473081355123387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134061048190594883613662365 50272893071473081355123387)
      ·
        refine ⟨75409339607209622032685081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50272893071473081355123387 75409339607209622032685081)
        ·
          refine ⟨56557004705407216524513811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75409339607209622032685081 56557004705407216524513811)
          ·
            refine ⟨84835507058110824786770717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56557004705407216524513811 84835507058110824786770717)
            ·
              refine ⟨31813315146791559295039019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84835507058110824786770717 31813315146791559295039019)
              ·
                refine ⟨47719972720187338942558529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31813315146791559295039019 47719972720187338942558529)
                ·
                  refine ⟨35789979540140504206918897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47719972720187338942558529 35789979540140504206918897)
                  ·
                    refine ⟨26842484655105378155189173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35789979540140504206918897 26842484655105378155189173)
                    ·
                      refine ⟨2516482936416129202048985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26842484655105378155189173 2516482936416129202048985)
                      ·
                        rfl

theorem cell23_4900833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_4900833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900833 prefixEnd_4900833 := by exact prefixLift 4900833
  have htrace : WordTrace (prefixWord ++ tailWord_4900833) baseStart_4900833 baseEnd_4900833 := by
    simpa [prefixWord, tailWord_4900833, baseEnd_4900833] using wordTrace_append hprefix tailTrace_4900833
  have hstable : (prefixWord ++ tailWord_4900833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900833).length < 2 ^ (prefixWord ++ tailWord_4900833).sum := by decide
  have hdescent : baseEnd_4900833 < baseStart_4900833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900847 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 1, 3, 2]
def baseStart_4900847 : Nat := 118140960795 + 4900847 * 2 ^ 59
def prefixEnd_4900847 : Nat := 4983230072969 + 3 ^ 40 * 4900847 * 2
def baseEnd_4900847 : Nat := 2516490125145292147273921

theorem tailTrace_4900847 : CollatzResearch.WordTrace tailWord_4900847 prefixEnd_4900847 2516490125145292147273921 := by
  unfold tailWord_4900847
  simp only [CollatzResearch.WordTrace]
  refine ⟨178748574876075791875892795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119165716584050527917261863 178748574876075791875892795)
  ·
    refine ⟨268122862314113687813839193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178748574876075791875892795 268122862314113687813839193)
    ·
      refine ⟨201092146735585265860379395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268122862314113687813839193 201092146735585265860379395)
      ·
        refine ⟨301638220103377898790569093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201092146735585265860379395 301638220103377898790569093)
        ·
          refine ⟨56557166269383356023231705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 301638220103377898790569093 56557166269383356023231705)
          ·
            refine ⟨42417874702037517017423779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56557166269383356023231705 42417874702037517017423779)
            ·
              refine ⟨63626812053056275526135669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42417874702037517017423779 63626812053056275526135669)
              ·
                refine ⟨5965013629974025830575219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63626812053056275526135669 5965013629974025830575219)
                ·
                  refine ⟨8947520444961038745862829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5965013629974025830575219 8947520444961038745862829)
                  ·
                    refine ⟨3355320166860389529698561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8947520444961038745862829 3355320166860389529698561)
                    ·
                      refine ⟨2516490125145292147273921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355320166860389529698561 2516490125145292147273921)
                      ·
                        rfl

theorem cell23_4900847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 3, 2].length) (baseStart_4900847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900847 prefixEnd_4900847 := by exact prefixLift 4900847
  have htrace : WordTrace (prefixWord ++ tailWord_4900847) baseStart_4900847 baseEnd_4900847 := by
    simpa [prefixWord, tailWord_4900847, baseEnd_4900847] using wordTrace_append hprefix tailTrace_4900847
  have hstable : (prefixWord ++ tailWord_4900847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900847).length < 2 ^ (prefixWord ++ tailWord_4900847).sum := by decide
  have hdescent : baseEnd_4900847 < baseStart_4900847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900871 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_4900871 : Nat := 118140960795 + 4900871 * 2 ^ 59
def prefixEnd_4900871 : Nat := 4983230072969 + 3 ^ 40 * 4900871 * 2
def baseEnd_4900871 : Nat := 2516502448681000053373811

theorem tailTrace_4900871 : CollatzResearch.WordTrace tailWord_4900871 prefixEnd_4900871 2516502448681000053373811 := by
  unfold tailWord_4900871
  simp only [CollatzResearch.WordTrace]
  refine ⟨178749450227988843974766467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119166300151992562649844311 178749450227988843974766467)
  ·
    refine ⟨268124175341983265962149701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178749450227988843974766467 268124175341983265962149701)
    ·
      refine ⟨50273282876621862367903069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268124175341983265962149701 50273282876621862367903069)
      ·
        refine ⟨18852481078733198387963651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50273282876621862367903069 18852481078733198387963651)
        ·
          refine ⟨28278721618099797581945477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18852481078733198387963651 28278721618099797581945477)
          ·
            refine ⟨5302260303393712046614777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28278721618099797581945477 5302260303393712046614777)
            ·
              refine ⟨3976695227545284034961083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5302260303393712046614777 3976695227545284034961083)
              ·
                refine ⟨5965042841317926052441625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976695227545284034961083 5965042841317926052441625)
                ·
                  refine ⟨4473782130988444539331219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5965042841317926052441625 4473782130988444539331219)
                  ·
                    refine ⟨6710673196482666808996829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4473782130988444539331219 6710673196482666808996829)
                    ·
                      refine ⟨2516502448681000053373811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6710673196482666808996829 2516502448681000053373811)
                      ·
                        rfl

theorem cell23_4900871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_4900871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900871 prefixEnd_4900871 := by exact prefixLift 4900871
  have htrace : WordTrace (prefixWord ++ tailWord_4900871) baseStart_4900871 baseEnd_4900871 := by
    simpa [prefixWord, tailWord_4900871, baseEnd_4900871] using wordTrace_append hprefix tailTrace_4900871
  have hstable : (prefixWord ++ tailWord_4900871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900871).length < 2 ^ (prefixWord ++ tailWord_4900871).sum := by decide
  have hdescent : baseEnd_4900871 < baseStart_4900871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900883 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 7]
def baseStart_4900883 : Nat := 118140960795 + 4900883 * 2 ^ 59
def prefixEnd_4900883 : Nat := 4983230072969 + 3 ^ 40 * 4900883 * 2
def baseEnd_4900883 : Nat := 279612067827650445158195

theorem tailTrace_4900883 : CollatzResearch.WordTrace tailWord_4900883 prefixEnd_4900883 279612067827650445158195 := by
  unfold tailWord_4900883
  simp only [CollatzResearch.WordTrace]
  refine ⟨178749887903945370024203303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119166591935963580016135535 178749887903945370024203303)
  ·
    refine ⟨268124831855918055036304955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178749887903945370024203303 268124831855918055036304955)
    ·
      refine ⟨402187247783877082554457433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268124831855918055036304955 402187247783877082554457433)
      ·
        refine ⟨301640435837907811915843075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402187247783877082554457433 301640435837907811915843075)
        ·
          refine ⟨452460653756861717873764613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301640435837907811915843075 452460653756861717873764613)
          ·
            refine ⟨84836372579411572101330865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 452460653756861717873764613 84836372579411572101330865)
            ·
              refine ⟨63627279434558679075998149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84836372579411572101330865 63627279434558679075998149)
              ·
                refine ⟨11930114893979752326749653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63627279434558679075998149 11930114893979752326749653)
                ·
                  refine ⟨279612067827650445158195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11930114893979752326749653 279612067827650445158195)
                  ·
                    rfl

theorem cell23_4900883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 7].length) (baseStart_4900883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900883 prefixEnd_4900883 := by exact prefixLift 4900883
  have htrace : WordTrace (prefixWord ++ tailWord_4900883) baseStart_4900883 baseEnd_4900883 := by
    simpa [prefixWord, tailWord_4900883, baseEnd_4900883] using wordTrace_append hprefix tailTrace_4900883
  have hstable : (prefixWord ++ tailWord_4900883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900883).length < 2 ^ (prefixWord ++ tailWord_4900883).sum := by decide
  have hdescent : baseEnd_4900883 < baseStart_4900883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900943 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 2, 8]
def baseStart_4900943 : Nat := 118140960795 + 4900943 * 2 ^ 59
def prefixEnd_4900943 : Nat := 4983230072969 + 3 ^ 40 * 4900943 * 2
def baseEnd_4900943 : Nat := 838846473096041257224493

theorem tailTrace_4900943 : CollatzResearch.WordTrace tailWord_4900943 prefixEnd_4900943 838846473096041257224493 := by
  unfold tailWord_4900943
  simp only [CollatzResearch.WordTrace]
  refine ⟨178752076283728000271387483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119168050855818666847591655 178752076283728000271387483)
  ·
    refine ⟨268128114425592000407081225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178752076283728000271387483 268128114425592000407081225)
    ·
      refine ⟨201096085819194000305310919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268128114425592000407081225 201096085819194000305310919)
      ·
        refine ⟨301644128728791000457966379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201096085819194000305310919 301644128728791000457966379)
        ·
          refine ⟨452466193093186500686949569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301644128728791000457966379 452466193093186500686949569)
          ·
            refine ⟨339349644819889875515212177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452466193093186500686949569 339349644819889875515212177)
            ·
              refine ⟨254512233614917406636409133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339349644819889875515212177 254512233614917406636409133)
              ·
                refine ⟨95442087605594027488653425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254512233614917406636409133 95442087605594027488653425)
                ·
                  refine ⟨71581565704195520616490069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95442087605594027488653425 71581565704195520616490069)
                  ·
                    refine ⟨838846473096041257224493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71581565704195520616490069 838846473096041257224493)
                    ·
                      rfl

theorem cell23_4900943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_4900943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900943 prefixEnd_4900943 := by exact prefixLift 4900943
  have htrace : WordTrace (prefixWord ++ tailWord_4900943) baseStart_4900943 baseEnd_4900943 := by
    simpa [prefixWord, tailWord_4900943, baseEnd_4900943] using wordTrace_append hprefix tailTrace_4900943
  have hstable : (prefixWord ++ tailWord_4900943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900943).length < 2 ^ (prefixWord ++ tailWord_4900943).sum := by decide
  have hdescent : baseEnd_4900943 < baseStart_4900943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900967 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_4900967 : Nat := 118140960795 + 4900967 * 2 ^ 59
def prefixEnd_4900967 : Nat := 4983230072969 + 3 ^ 40 * 4900967 * 2
def baseEnd_4900967 : Nat := 2516551742823831677773369

theorem tailTrace_4900967 : CollatzResearch.WordTrace tailWord_4900967 prefixEnd_4900967 2516551742823831677773369 := by
  unfold tailWord_4900967
  simp only [CollatzResearch.WordTrace]
  refine ⟨178752951635641052370261155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119168634423760701580174103 178752951635641052370261155)
  ·
    refine ⟨268129427453461578555391733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178752951635641052370261155 268129427453461578555391733)
    ·
      refine ⟨25137133823762022989567975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 268129427453461578555391733 25137133823762022989567975)
      ·
        refine ⟨37705700735643034484351963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25137133823762022989567975 37705700735643034484351963)
        ·
          refine ⟨56558551103464551726527945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37705700735643034484351963 56558551103464551726527945)
          ·
            refine ⟨42418913327598413794895959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56558551103464551726527945 42418913327598413794895959)
            ·
              refine ⟨63628369991397620692343939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42418913327598413794895959 63628369991397620692343939)
              ·
                refine ⟨95442554987096431038515909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63628369991397620692343939 95442554987096431038515909)
                ·
                  refine ⟨17895479060080580819721733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95442554987096431038515909 17895479060080580819721733)
                  ·
                    refine ⟨3355402323765108903697825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17895479060080580819721733 3355402323765108903697825)
                    ·
                      refine ⟨2516551742823831677773369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355402323765108903697825 2516551742823831677773369)
                      ·
                        rfl

theorem cell23_4900967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_4900967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900967 prefixEnd_4900967 := by exact prefixLift 4900967
  have htrace : WordTrace (prefixWord ++ tailWord_4900967) baseStart_4900967 baseEnd_4900967 := by
    simpa [prefixWord, tailWord_4900967, baseEnd_4900967] using wordTrace_append hprefix tailTrace_4900967
  have hstable : (prefixWord ++ tailWord_4900967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900967).length < 2 ^ (prefixWord ++ tailWord_4900967).sum := by decide
  have hdescent : baseEnd_4900967 < baseStart_4900967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4900977 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 3, 4]
def baseStart_4900977 : Nat := 118140960795 + 4900977 * 2 ^ 59
def prefixEnd_4900977 : Nat := 4983230072969 + 3 ^ 40 * 4900977 * 2
def baseEnd_4900977 : Nat := 838852292543458879549441

theorem tailTrace_4900977 : CollatzResearch.WordTrace tailWord_4900977 prefixEnd_4900977 838852292543458879549441 := by
  unfold tailWord_4900977
  simp only [CollatzResearch.WordTrace]
  refine ⟨178753316365604824078125185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119168877577069882718750123 178753316365604824078125185)
  ·
    refine ⟨134064987274203618058593889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178753316365604824078125185 134064987274203618058593889)
    ·
      refine ⟨100548740455652713543945417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134064987274203618058593889 100548740455652713543945417)
      ·
        refine ⟨75411555341739535157959063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100548740455652713543945417 75411555341739535157959063)
        ·
          refine ⟨113117333012609302736938595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75411555341739535157959063 113117333012609302736938595)
          ·
            refine ⟨169675999518913954105407893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113117333012609302736938595 169675999518913954105407893)
            ·
              refine ⟨7953562477449091598690995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169675999518913954105407893 7953562477449091598690995)
              ·
                refine ⟨11930343716173637398036493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7953562477449091598690995 11930343716173637398036493)
                ·
                  refine ⟨4473878893565114024263685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11930343716173637398036493 4473878893565114024263685)
                  ·
                    refine ⟨838852292543458879549441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473878893565114024263685 838852292543458879549441)
                    ·
                      rfl

theorem cell23_4900977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_4900977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4900977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4900977 prefixEnd_4900977 := by exact prefixLift 4900977
  have htrace : WordTrace (prefixWord ++ tailWord_4900977) baseStart_4900977 baseEnd_4900977 := by
    simpa [prefixWord, tailWord_4900977, baseEnd_4900977] using wordTrace_append hprefix tailTrace_4900977
  have hstable : (prefixWord ++ tailWord_4900977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4900977).length < 2 ^ (prefixWord ++ tailWord_4900977).sum := by decide
  have hdescent : baseEnd_4900977 < baseStart_4900977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4900977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901017 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 3]
def baseStart_4901017 : Nat := 118140960795 + 4901017 * 2 ^ 59
def prefixEnd_4901017 : Nat := 4983230072969 + 3 ^ 40 * 4901017 * 2
def baseEnd_4901017 : Nat := 2516577416856556482148139

theorem tailTrace_4901017 : CollatzResearch.WordTrace tailWord_4901017 prefixEnd_4901017 2516577416856556482148139 := by
  unfold tailWord_4901017
  simp only [CollatzResearch.WordTrace]
  refine ⟨178754775285459910909581305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119169850190306607273054203 178754775285459910909581305)
  ·
    refine ⟨134066081464094933182185979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178754775285459910909581305 134066081464094933182185979)
    ·
      refine ⟨201099122196142399773278969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134066081464094933182185979 201099122196142399773278969)
      ·
        refine ⟨150824341647106799829959227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201099122196142399773278969 150824341647106799829959227)
        ·
          refine ⟨226236512470660199744938841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150824341647106799829959227 226236512470660199744938841)
          ·
            refine ⟨169677384352995149808704131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226236512470660199744938841 169677384352995149808704131)
            ·
              refine ⟨254516076529492724713056197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169677384352995149808704131 254516076529492724713056197)
              ·
                refine ⟨47721764349279885883698037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254516076529492724713056197 47721764349279885883698037)
                ·
                  refine ⟨4473915407744989301596691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47721764349279885883698037 4473915407744989301596691)
                  ·
                    refine ⟨6710873111617483952395037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4473915407744989301596691 6710873111617483952395037)
                    ·
                      refine ⟨2516577416856556482148139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6710873111617483952395037 2516577416856556482148139)
                      ·
                        rfl

theorem cell23_4901017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_4901017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901017 prefixEnd_4901017 := by exact prefixLift 4901017
  have htrace : WordTrace (prefixWord ++ tailWord_4901017) baseStart_4901017 baseEnd_4901017 := by
    simpa [prefixWord, tailWord_4901017, baseEnd_4901017] using wordTrace_append hprefix tailTrace_4901017
  have hstable : (prefixWord ++ tailWord_4901017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901017).length < 2 ^ (prefixWord ++ tailWord_4901017).sum := by decide
  have hdescent : baseEnd_4901017 < baseStart_4901017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901028 : List Nat := [2, 3, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_4901028 : Nat := 118140960795 + 4901028 * 2 ^ 59
def prefixEnd_4901028 : Nat := 4983230072969 + 3 ^ 40 * 4901028 * 2
def baseEnd_4901028 : Nat := 838861021714585313036863

theorem tailTrace_4901028 : CollatzResearch.WordTrace tailWord_4901028 prefixEnd_4901028 838861021714585313036863 := by
  unfold tailWord_4901028
  simp only [CollatzResearch.WordTrace]
  refine ⟨89377588244210029894115869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119170117658946706525487825 89377588244210029894115869)
  ·
    refine ⟨33516595591578761210293451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89377588244210029894115869 33516595591578761210293451)
    ·
      refine ⟨50274893387368141815440177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33516595591578761210293451 50274893387368141815440177)
      ·
        refine ⟨37706170040526106361580133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50274893387368141815440177 37706170040526106361580133)
        ·
          refine ⟨7069906882598644942796275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37706170040526106361580133 7069906882598644942796275)
          ·
            refine ⟨10604860323897967414194413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7069906882598644942796275 10604860323897967414194413)
            ·
              refine ⟨3976822621461737780322905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10604860323897967414194413 3976822621461737780322905)
              ·
                refine ⟨2982616966096303335242179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3976822621461737780322905 2982616966096303335242179)
                ·
                  refine ⟨4473925449144455002863269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982616966096303335242179 4473925449144455002863269)
                  ·
                    refine ⟨838861021714585313036863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473925449144455002863269 838861021714585313036863)
                    ·
                      rfl

theorem cell23_4901028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_4901028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901028 prefixEnd_4901028 := by exact prefixLift 4901028
  have htrace : WordTrace (prefixWord ++ tailWord_4901028) baseStart_4901028 baseEnd_4901028 := by
    simpa [prefixWord, tailWord_4901028, baseEnd_4901028] using wordTrace_append hprefix tailTrace_4901028
  have hstable : (prefixWord ++ tailWord_4901028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901028).length < 2 ^ (prefixWord ++ tailWord_4901028).sum := by decide
  have hdescent : baseEnd_4901028 < baseStart_4901028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901041 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 6]
def baseStart_4901041 : Nat := 118140960795 + 4901041 * 2 ^ 59
def prefixEnd_4901041 : Nat := 4983230072969 + 3 ^ 40 * 4901041 * 2
def baseEnd_4901041 : Nat := 279621082265807154249781

theorem tailTrace_4901041 : CollatzResearch.WordTrace tailWord_4901041 prefixEnd_4901041 279621082265807154249781 := by
  unfold tailWord_4901041
  simp only [CollatzResearch.WordTrace]
  refine ⟨178755650637372963008454977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119170433758248642005636651 178755650637372963008454977)
  ·
    refine ⟨134066737978029722256341233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178755650637372963008454977 134066737978029722256341233)
    ·
      refine ⟨100550053483522291692255925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134066737978029722256341233 100550053483522291692255925)
      ·
        refine ⟨9426567514080214846148993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100550053483522291692255925 9426567514080214846148993)
        ·
          refine ⟨7069925635560161134611745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9426567514080214846148993 7069925635560161134611745)
          ·
            refine ⟨5302444226670120850958809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7069925635560161134611745 5302444226670120850958809)
            ·
              refine ⟨3976833170002590638219107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5302444226670120850958809 3976833170002590638219107)
              ·
                refine ⟨5965249755003885957328661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976833170002590638219107 5965249755003885957328661)
                ·
                  refine ⟨279621082265807154249781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5965249755003885957328661 279621082265807154249781)
                  ·
                    rfl

theorem cell23_4901041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 6].length) (baseStart_4901041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901041 prefixEnd_4901041 := by exact prefixLift 4901041
  have htrace : WordTrace (prefixWord ++ tailWord_4901041) baseStart_4901041 baseEnd_4901041 := by
    simpa [prefixWord, tailWord_4901041, baseEnd_4901041] using wordTrace_append hprefix tailTrace_4901041
  have hstable : (prefixWord ++ tailWord_4901041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901041).length < 2 ^ (prefixWord ++ tailWord_4901041).sum := by decide
  have hdescent : baseEnd_4901041 < baseStart_4901041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901054 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_4901054 : Nat := 118140960795 + 4901054 * 2 ^ 59
def prefixEnd_4901054 : Nat := 4983230072969 + 3 ^ 40 * 4901054 * 2
def baseEnd_4901054 : Nat := 838865471880257612461823

theorem tailTrace_4901054 : CollatzResearch.WordTrace tailWord_4901054 prefixEnd_4901054 838865471880257612461823 := by
  unfold tailWord_4901054
  simp only [CollatzResearch.WordTrace]
  refine ⟨22344515598290733278584777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119170749857550577485785477 22344515598290733278584777)
  ·
    refine ⟨16758386698718049958938583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22344515598290733278584777 16758386698718049958938583)
    ·
      refine ⟨25137580048077074938407875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16758386698718049958938583 25137580048077074938407875)
      ·
        refine ⟨37706370072115612407611813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25137580048077074938407875 37706370072115612407611813)
        ·
          refine ⟨7069944388521677326427215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37706370072115612407611813 7069944388521677326427215)
          ·
            refine ⟨10604916582782515989640823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7069944388521677326427215 10604916582782515989640823)
            ·
              refine ⟨15907374874173773984461235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10604916582782515989640823 15907374874173773984461235)
              ·
                refine ⟨23861062311260660976691853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15907374874173773984461235 23861062311260660976691853)
                ·
                  refine ⟨8947898366722747866259445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23861062311260660976691853 8947898366722747866259445)
                  ·
                    refine ⟨838865471880257612461823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8947898366722747866259445 838865471880257612461823)
                    ·
                      rfl

theorem cell23_4901054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_4901054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901054 prefixEnd_4901054 := by exact prefixLift 4901054
  have htrace : WordTrace (prefixWord ++ tailWord_4901054) baseStart_4901054 baseEnd_4901054 := by
    simpa [prefixWord, tailWord_4901054, baseEnd_4901054] using wordTrace_append hprefix tailTrace_4901054
  have hstable : (prefixWord ++ tailWord_4901054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901054).length < 2 ^ (prefixWord ++ tailWord_4901054).sum := by decide
  have hdescent : baseEnd_4901054 < baseStart_4901054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901078 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4901078 : Nat := 118140960795 + 4901078 * 2 ^ 59
def prefixEnd_4901078 : Nat := 4983230072969 + 3 ^ 40 * 4901078 * 2
def baseEnd_4901078 : Nat := 2516608739176480743485359

theorem tailTrace_4901078 : CollatzResearch.WordTrace tailWord_4901078 prefixEnd_4901078 2516608739176480743485359 := by
  unfold tailWord_4901078
  simp only [CollatzResearch.WordTrace]
  refine ⟨11172312508639932395471993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119171333425492612218367925 11172312508639932395471993)
  ·
    refine ⟨8379234381479949296603995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11172312508639932395471993 8379234381479949296603995)
    ·
      refine ⟨12568851572219923944905993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8379234381479949296603995 12568851572219923944905993)
      ·
        refine ⟨9426638679164942958679495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12568851572219923944905993 9426638679164942958679495)
        ·
          refine ⟨14139958018747414438019243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9426638679164942958679495 14139958018747414438019243)
          ·
            refine ⟨21209937028121121657028865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14139958018747414438019243 21209937028121121657028865)
            ·
              refine ⟨15907452771090841242771649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21209937028121121657028865 15907452771090841242771649)
              ·
                refine ⟨11930589578318130932078737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15907452771090841242771649 11930589578318130932078737)
                ·
                  refine ⟨8947942183738598199059053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11930589578318130932078737 8947942183738598199059053)
                  ·
                    refine ⟨3355478318901974324647145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8947942183738598199059053 3355478318901974324647145)
                    ·
                      refine ⟨2516608739176480743485359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355478318901974324647145 2516608739176480743485359)
                      ·
                        rfl

theorem cell23_4901078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4901078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901078 prefixEnd_4901078 := by exact prefixLift 4901078
  have htrace : WordTrace (prefixWord ++ tailWord_4901078) baseStart_4901078 baseEnd_4901078 := by
    simpa [prefixWord, tailWord_4901078, baseEnd_4901078] using wordTrace_append hprefix tailTrace_4901078
  have hstable : (prefixWord ++ tailWord_4901078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901078).length < 2 ^ (prefixWord ++ tailWord_4901078).sum := by decide
  have hdescent : baseEnd_4901078 < baseStart_4901078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901080 : List Nat := [2, 1, 2, 2, 4, 12]
def baseStart_4901080 : Nat := 118140960795 + 4901080 * 2 ^ 59
def prefixEnd_4901080 : Nat := 4983230072969 + 3 ^ 40 * 4901080 * 2
def baseEnd_4901080 : Nat := 10356418790690492739343

theorem tailTrace_4901080 : CollatzResearch.WordTrace tailWord_4901080 prefixEnd_4901080 10356418790690492739343 := by
  unfold tailWord_4901080
  simp only [CollatzResearch.WordTrace]
  refine ⟨89378536542115836334562347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119171382056154448446083129 89378536542115836334562347)
  ·
    refine ⟨134067804813173754501843521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89378536542115836334562347 134067804813173754501843521)
    ·
      refine ⟨100550853609880315876382641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134067804813173754501843521 100550853609880315876382641)
      ·
        refine ⟨75413140207410236907286981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100550853609880315876382641 75413140207410236907286981)
        ·
          refine ⟨14139963788889419420116309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75413140207410236907286981 14139963788889419420116309)
          ·
            refine ⟨10356418790690492739343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14139963788889419420116309 10356418790690492739343)
            ·
              rfl

theorem cell23_4901080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 12].length) (baseStart_4901080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901080 prefixEnd_4901080 := by exact prefixLift 4901080
  have htrace : WordTrace (prefixWord ++ tailWord_4901080) baseStart_4901080 baseEnd_4901080 := by
    simpa [prefixWord, tailWord_4901080, baseEnd_4901080] using wordTrace_append hprefix tailTrace_4901080
  have hstable : (prefixWord ++ tailWord_4901080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901080).length < 2 ^ (prefixWord ++ tailWord_4901080).sum := by decide
  have hdescent : baseEnd_4901080 < baseStart_4901080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901085 : List Nat := [1, 4, 3, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4901085 : Nat := 118140960795 + 4901085 * 2 ^ 59
def prefixEnd_4901085 : Nat := 4983230072969 + 3 ^ 40 * 4901085 * 2
def baseEnd_4901085 : Nat := 2516612333541062216097827

theorem tailTrace_4901085 : CollatzResearch.WordTrace tailWord_4901085 prefixEnd_4901085 2516612333541062216097827 := by
  unfold tailWord_4901085
  simp only [CollatzResearch.WordTrace]
  refine ⟨178757255449213558523056709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119171503632809039015371139 178757255449213558523056709)
  ·
    refine ⟨33516985396727542223073133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178757255449213558523056709 33516985396727542223073133)
    ·
      refine ⟨12568869523772828333652425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33516985396727542223073133 12568869523772828333652425)
      ·
        refine ⟨9426652142829621250239319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12568869523772828333652425 9426652142829621250239319)
        ·
          refine ⟨14139978214244431875358979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9426652142829621250239319 14139978214244431875358979)
          ·
            refine ⟨21209967321366647813038469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14139978214244431875358979 21209967321366647813038469)
            ·
              refine ⟨3976868872756246464944713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21209967321366647813038469 3976868872756246464944713)
              ·
                refine ⟨2982651654567184848708535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3976868872756246464944713 2982651654567184848708535)
                ·
                  refine ⟨4473977481850777273062803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982651654567184848708535 4473977481850777273062803)
                  ·
                    refine ⟨6710966222776165909594205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4473977481850777273062803 6710966222776165909594205)
                    ·
                      refine ⟨2516612333541062216097827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6710966222776165909594205 2516612333541062216097827)
                      ·
                        rfl

theorem cell23_4901085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4901085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901085 prefixEnd_4901085 := by exact prefixLift 4901085
  have htrace : WordTrace (prefixWord ++ tailWord_4901085) baseStart_4901085 baseEnd_4901085 := by
    simpa [prefixWord, tailWord_4901085, baseEnd_4901085] using wordTrace_append hprefix tailTrace_4901085
  have hstable : (prefixWord ++ tailWord_4901085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901085).length < 2 ^ (prefixWord ++ tailWord_4901085).sum := by decide
  have hdescent : baseEnd_4901085 < baseStart_4901085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901128 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_4901128 : Nat := 118140960795 + 4901128 * 2 ^ 59
def prefixEnd_4901128 : Nat := 4983230072969 + 3 ^ 40 * 4901128 * 2
def baseEnd_4901128 : Nat := 2516634413209205547860129

theorem tailTrace_4901128 : CollatzResearch.WordTrace tailWord_4901128 prefixEnd_4901128 2516634413209205547860129 := by
  unfold tailWord_4901128
  simp only [CollatzResearch.WordTrace]
  refine ⟨89379411894028888433436019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119172549192038517911248025 89379411894028888433436019)
  ·
    refine ⟨134069117841043332650154029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89379411894028888433436019 134069117841043332650154029)
    ·
      refine ⟨50275919190391249743807761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134069117841043332650154029 50275919190391249743807761)
      ·
        refine ⟨37706939392793437307855821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50275919190391249743807761 37706939392793437307855821)
        ·
          refine ⟨14140102272297538990445933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37706939392793437307855821 14140102272297538990445933)
          ·
            refine ⟨5302538352111577121417225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14140102272297538990445933 5302538352111577121417225)
            ·
              refine ⟨3976903764083682841062919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5302538352111577121417225 3976903764083682841062919)
              ·
                refine ⟨5965355646125524261594379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976903764083682841062919 5965355646125524261594379)
                ·
                  refine ⟨8948033469188286392391569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5965355646125524261594379 8948033469188286392391569)
                  ·
                    refine ⟨6711025101891214794293677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8948033469188286392391569 6711025101891214794293677)
                    ·
                      refine ⟨2516634413209205547860129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6711025101891214794293677 2516634413209205547860129)
                      ·
                        rfl

theorem cell23_4901128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_4901128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901128 prefixEnd_4901128 := by exact prefixLift 4901128
  have htrace : WordTrace (prefixWord ++ tailWord_4901128) baseStart_4901128 baseEnd_4901128 := by
    simpa [prefixWord, tailWord_4901128, baseEnd_4901128] using wordTrace_append hprefix tailTrace_4901128
  have hstable : (prefixWord ++ tailWord_4901128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901128).length < 2 ^ (prefixWord ++ tailWord_4901128).sum := by decide
  have hdescent : baseEnd_4901128 < baseStart_4901128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901141 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_4901141 : Nat := 118140960795 + 4901141 * 2 ^ 59
def prefixEnd_4901141 : Nat := 4983230072969 + 3 ^ 40 * 4901141 * 2
def baseEnd_4901141 : Nat := 2516641088457713996997569

theorem tailTrace_4901141 : CollatzResearch.WordTrace tailWord_4901141 prefixEnd_4901141 2516641088457713996997569 := by
  unfold tailWord_4901141
  simp only [CollatzResearch.WordTrace]
  refine ⟨178759297937010680087095277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119172865291340453391396851 178759297937010680087095277)
  ·
    refine ⟨67034736726379005032660729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178759297937010680087095277 67034736726379005032660729)
    ·
      refine ⟨50276052544784253774495547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67034736726379005032660729 50276052544784253774495547)
      ·
        refine ⟨75414078817176380661743321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50276052544784253774495547 75414078817176380661743321)
        ·
          refine ⟨56560559112882285496307491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75414078817176380661743321 56560559112882285496307491)
          ·
            refine ⟨84840838669323428244461237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56560559112882285496307491 84840838669323428244461237)
            ·
              refine ⟨7953828625249071397918241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84840838669323428244461237 7953828625249071397918241)
              ·
                refine ⟨5965371468936803548438681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7953828625249071397918241 5965371468936803548438681)
                ·
                  refine ⟨4474028601702602661329011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5965371468936803548438681 4474028601702602661329011)
                  ·
                    refine ⟨6711042902553903991993517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4474028601702602661329011 6711042902553903991993517)
                    ·
                      refine ⟨2516641088457713996997569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6711042902553903991993517 2516641088457713996997569)
                      ·
                        rfl

theorem cell23_4901141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_4901141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901141 prefixEnd_4901141 := by exact prefixLift 4901141
  have htrace : WordTrace (prefixWord ++ tailWord_4901141) baseStart_4901141 baseEnd_4901141 := by
    simpa [prefixWord, tailWord_4901141, baseEnd_4901141] using wordTrace_append hprefix tailTrace_4901141
  have hstable : (prefixWord ++ tailWord_4901141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901141).length < 2 ^ (prefixWord ++ tailWord_4901141).sum := by decide
  have hdescent : baseEnd_4901141 < baseStart_4901141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901167 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 3]
def baseStart_4901167 : Nat := 118140960795 + 4901167 * 2 ^ 59
def prefixEnd_4901167 : Nat := 4983230072969 + 3 ^ 40 * 4901167 * 2
def baseEnd_4901167 : Nat := 2516654438954730895272449

theorem tailTrace_4901167 : CollatzResearch.WordTrace tailWord_4901167 prefixEnd_4901167 2516654438954730895272449 := by
  unfold tailWord_4901167
  simp only [CollatzResearch.WordTrace]
  refine ⟨178760246234916486527541755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119173497489944324351694503 178760246234916486527541755)
  ·
    refine ⟨268140369352374729791312633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178760246234916486527541755 268140369352374729791312633)
    ·
      refine ⟨201105277014281047343484475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268140369352374729791312633 201105277014281047343484475)
      ·
        refine ⟨301657915521421571015226713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201105277014281047343484475 301657915521421571015226713)
        ·
          refine ⟨226243436641066178261420035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301657915521421571015226713 226243436641066178261420035)
          ·
            refine ⟨339365154961599267392130053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226243436641066178261420035 339365154961599267392130053)
            ·
              refine ⟨63630966555299862636024385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 339365154961599267392130053 63630966555299862636024385)
              ·
                refine ⟨47723224916474896977018289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63630966555299862636024385 47723224916474896977018289)
                ·
                  refine ⟨35792418687356172732763717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47723224916474896977018289 35792418687356172732763717)
                  ·
                    refine ⟨6711078503879282387393197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35792418687356172732763717 6711078503879282387393197)
                    ·
                      refine ⟨2516654438954730895272449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6711078503879282387393197 2516654438954730895272449)
                      ·
                        rfl

theorem cell23_4901167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_4901167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901167 prefixEnd_4901167 := by exact prefixLift 4901167
  have htrace : WordTrace (prefixWord ++ tailWord_4901167) baseStart_4901167 baseEnd_4901167 := by
    simpa [prefixWord, tailWord_4901167, baseEnd_4901167] using wordTrace_append hprefix tailTrace_4901167
  have hstable : (prefixWord ++ tailWord_4901167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901167).length < 2 ^ (prefixWord ++ tailWord_4901167).sum := by decide
  have hdescent : baseEnd_4901167 < baseStart_4901167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901204 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 7]
def baseStart_4901204 : Nat := 118140960795 + 4901204 * 2 ^ 59
def prefixEnd_4901204 : Nat := 4983230072969 + 3 ^ 40 * 4901204 * 2
def baseEnd_4901204 : Nat := 279630381970994138945531

theorem tailTrace_4901204 : CollatzResearch.WordTrace tailWord_4901204 prefixEnd_4901204 279630381970994138945531 := by
  unfold tailWord_4901204
  simp only [CollatzResearch.WordTrace]
  refine ⟨89380797867891220923319333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119174397157188294564425777 89380797867891220923319333)
  ·
    refine ⟨16758899600229603923122375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89380797867891220923319333 16758899600229603923122375)
    ·
      refine ⟨25138349400344405884683563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16758899600229603923122375 25138349400344405884683563)
      ·
        refine ⟨37707524100516608827025345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25138349400344405884683563 37707524100516608827025345)
        ·
          refine ⟨28280643075387456620269009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37707524100516608827025345 28280643075387456620269009)
          ·
            refine ⟨21210482306540592465201757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28280643075387456620269009 21210482306540592465201757)
            ·
              refine ⟨7953930864952722174450659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21210482306540592465201757 7953930864952722174450659)
              ·
                refine ⟨11930896297429083261675989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7953930864952722174450659 11930896297429083261675989)
                ·
                  refine ⟨279630381970994138945531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11930896297429083261675989 279630381970994138945531)
                  ·
                    rfl

theorem cell23_4901204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_4901204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901204 prefixEnd_4901204 := by exact prefixLift 4901204
  have htrace : WordTrace (prefixWord ++ tailWord_4901204) baseStart_4901204 baseEnd_4901204 := by
    simpa [prefixWord, tailWord_4901204, baseEnd_4901204] using wordTrace_append hprefix tailTrace_4901204
  have hstable : (prefixWord ++ tailWord_4901204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901204).length < 2 ^ (prefixWord ++ tailWord_4901204).sum := by decide
  have hdescent : baseEnd_4901204 < baseStart_4901204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901234 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_4901234 : Nat := 118140960795 + 4901234 * 2 ^ 59
def prefixEnd_4901234 : Nat := 4983230072969 + 3 ^ 40 * 4901234 * 2
def baseEnd_4901234 : Nat := 838896280719527377711547

theorem tailTrace_4901234 : CollatzResearch.WordTrace tailWord_4901234 prefixEnd_4901234 838896280719527377711547 := by
  unfold tailWord_4901234
  simp only [CollatzResearch.WordTrace]
  refine ⟨44690672481418439242557689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119175126617115837980153837 44690672481418439242557689)
  ·
    refine ⟨33518004361063829431918267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44690672481418439242557689 33518004361063829431918267)
    ·
      refine ⟨50277006541595744147877401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33518004361063829431918267 50277006541595744147877401)
      ·
        refine ⟨37707754906196808110908051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50277006541595744147877401 37707754906196808110908051)
        ·
          refine ⟨56561632359295212166362077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37707754906196808110908051 56561632359295212166362077)
          ·
            refine ⟨21210612134735704562385779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56561632359295212166362077 21210612134735704562385779)
            ·
              refine ⟨31815918202103556843578669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21210612134735704562385779 31815918202103556843578669)
              ·
                refine ⟨11930969325788833816342001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31815918202103556843578669 11930969325788833816342001)
                ·
                  refine ⟨8948226994341625362256501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11930969325788833816342001 8948226994341625362256501)
                  ·
                    refine ⟨838896280719527377711547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8948226994341625362256501 838896280719527377711547)
                    ·
                      rfl

theorem cell23_4901234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_4901234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901234 prefixEnd_4901234 := by exact prefixLift 4901234
  have htrace : WordTrace (prefixWord ++ tailWord_4901234) baseStart_4901234 baseEnd_4901234 := by
    simpa [prefixWord, tailWord_4901234, baseEnd_4901234] using wordTrace_append hprefix tailTrace_4901234
  have hstable : (prefixWord ++ tailWord_4901234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901234).length < 2 ^ (prefixWord ++ tailWord_4901234).sum := by decide
  have hdescent : baseEnd_4901234 < baseStart_4901234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901288 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4901288 : Nat := 118140960795 + 4901288 * 2 ^ 59
def prefixEnd_4901288 : Nat := 4983230072969 + 3 ^ 40 * 4901288 * 2
def baseEnd_4901288 : Nat := 2516716570113924921859393

theorem tailTrace_4901288 : CollatzResearch.WordTrace tailWord_4901288 prefixEnd_4901288 2516716570113924921859393 := by
  unfold tailWord_4901288
  simp only [CollatzResearch.WordTrace]
  refine ⟨89382329733739062096348259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119176439644985416128464345 89382329733739062096348259)
  ·
    refine ⟨134073494600608593144522389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89382329733739062096348259 134073494600608593144522389)
    ·
      refine ⟨6284695059403527803649487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134073494600608593144522389 6284695059403527803649487)
      ·
        refine ⟨9427042589105291705474231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6284695059403527803649487 9427042589105291705474231)
        ·
          refine ⟨14140563883657937558211347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9427042589105291705474231 14140563883657937558211347)
          ·
            refine ⟨21210845825486906337317021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14140563883657937558211347 21210845825486906337317021)
            ·
              refine ⟨7954067184557589876493883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21210845825486906337317021 7954067184557589876493883)
              ·
                refine ⟨11931100776836384814740825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7954067184557589876493883 11931100776836384814740825)
                ·
                  refine ⟨8948325582627288611055619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11931100776836384814740825 8948325582627288611055619)
                  ·
                    refine ⟨13422488373940932916583429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8948325582627288611055619 13422488373940932916583429)
                    ·
                      refine ⟨2516716570113924921859393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13422488373940932916583429 2516716570113924921859393)
                      ·
                        rfl

theorem cell23_4901288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4901288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901288 prefixEnd_4901288 := by exact prefixLift 4901288
  have htrace : WordTrace (prefixWord ++ tailWord_4901288) baseStart_4901288 baseEnd_4901288 := by
    simpa [prefixWord, tailWord_4901288, baseEnd_4901288] using wordTrace_append hprefix tailTrace_4901288
  have hstable : (prefixWord ++ tailWord_4901288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901288).length < 2 ^ (prefixWord ++ tailWord_4901288).sum := by decide
  have hdescent : baseEnd_4901288 < baseStart_4901288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901298 : List Nat := [3, 2, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_4901298 : Nat := 118140960795 + 4901298 * 2 ^ 59
def prefixEnd_4901298 : Nat := 4983230072969 + 3 ^ 40 * 4901298 * 2
def baseEnd_4901298 : Nat := 838907234973489960911449

theorem tailTrace_4901298 : CollatzResearch.WordTrace tailWord_4901298 prefixEnd_4901298 838907234973489960911449 := by
  unfold tailWord_4901298
  simp only [CollatzResearch.WordTrace]
  refine ⟨44691256049360473975140137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119176682798294597267040365 44691256049360473975140137)
  ·
    refine ⟨33518442037020355481355103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44691256049360473975140137 33518442037020355481355103)
    ·
      refine ⟨50277663055530533222032655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33518442037020355481355103 50277663055530533222032655)
      ·
        refine ⟨75416494583295799833048983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50277663055530533222032655 75416494583295799833048983)
        ·
          refine ⟨113124741874943699749573475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75416494583295799833048983 113124741874943699749573475)
          ·
            refine ⟨169687112812415549624360213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113124741874943699749573475 169687112812415549624360213)
            ·
              refine ⟨7954083413081978888641885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169687112812415549624360213 7954083413081978888641885)
              ·
                refine ⟨2982781279905742083240707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7954083413081978888641885 2982781279905742083240707)
                ·
                  refine ⟨4474171919858613124861061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982781279905742083240707 4474171919858613124861061)
                  ·
                    refine ⟨838907234973489960911449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4474171919858613124861061 838907234973489960911449)
                    ·
                      rfl

theorem cell23_4901298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_4901298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901298 prefixEnd_4901298 := by exact prefixLift 4901298
  have htrace : WordTrace (prefixWord ++ tailWord_4901298) baseStart_4901298 baseEnd_4901298 := by
    simpa [prefixWord, tailWord_4901298, baseEnd_4901298] using wordTrace_append hprefix tailTrace_4901298
  have hstable : (prefixWord ++ tailWord_4901298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901298).length < 2 ^ (prefixWord ++ tailWord_4901298).sum := by decide
  have hdescent : baseEnd_4901298 < baseStart_4901298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901321 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 3]
def baseStart_4901321 : Nat := 118140960795 + 4901321 * 2 ^ 59
def prefixEnd_4901321 : Nat := 4983230072969 + 3 ^ 40 * 4901321 * 2
def baseEnd_4901321 : Nat := 2516733514975523292746741

theorem tailTrace_4901321 : CollatzResearch.WordTrace tailWord_4901321 prefixEnd_4901321 2516733514975523292746741 := by
  unfold tailWord_4901321
  simp only [CollatzResearch.WordTrace]
  refine ⟨178765863076358570828647817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119177242050905713885765211 178765863076358570828647817)
  ·
    refine ⟨134074397307268928121485863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178765863076358570828647817 134074397307268928121485863)
    ·
      refine ⟨201111595960903392182228795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134074397307268928121485863 201111595960903392182228795)
      ·
        refine ⟨301667393941355088273343193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201111595960903392182228795 301667393941355088273343193)
        ·
          refine ⟨226250545456016316205007395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301667393941355088273343193 226250545456016316205007395)
          ·
            refine ⟨339375818184024474307511093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226250545456016316205007395 339375818184024474307511093)
            ·
              refine ⟨31816482954752294466329165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 339375818184024474307511093 31816482954752294466329165)
              ·
                refine ⟨11931181108032110424873437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31816482954752294466329165 11931181108032110424873437)
                ·
                  refine ⟨4474192915512041409327539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11931181108032110424873437 4474192915512041409327539)
                  ·
                    refine ⟨6711289373268062113991309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4474192915512041409327539 6711289373268062113991309)
                    ·
                      refine ⟨2516733514975523292746741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6711289373268062113991309 2516733514975523292746741)
                      ·
                        rfl

theorem cell23_4901321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 3].length) (baseStart_4901321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901321 prefixEnd_4901321 := by exact prefixLift 4901321
  have htrace : WordTrace (prefixWord ++ tailWord_4901321) baseStart_4901321 baseEnd_4901321 := by
    simpa [prefixWord, tailWord_4901321, baseEnd_4901321] using wordTrace_append hprefix tailTrace_4901321
  have hstable : (prefixWord ++ tailWord_4901321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901321).length < 2 ^ (prefixWord ++ tailWord_4901321).sum := by decide
  have hdescent : baseEnd_4901321 < baseStart_4901321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901361 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_4901361 : Nat := 118140960795 + 4901361 * 2 ^ 59
def prefixEnd_4901361 : Nat := 4983230072969 + 3 ^ 40 * 4901361 * 2
def baseEnd_4901361 : Nat := 2516754054201703136246557

theorem tailTrace_4901361 : CollatzResearch.WordTrace tailWord_4901361 prefixEnd_4901361 2516754054201703136246557 := by
  unfold tailWord_4901361
  simp only [CollatzResearch.WordTrace]
  refine ⟨178767321996213657660103937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119178214664142438440069291 178767321996213657660103937)
  ·
    refine ⟨134075491497160243245077953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178767321996213657660103937 134075491497160243245077953)
    ·
      refine ⟨100556618622870182433808465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134075491497160243245077953 100556618622870182433808465)
      ·
        refine ⟨75417463967152636825356349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100556618622870182433808465 75417463967152636825356349)
        ·
          refine ⟨28281548987682238809508631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75417463967152636825356349 28281548987682238809508631)
          ·
            refine ⟨42422323481523358214262947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28281548987682238809508631 42422323481523358214262947)
            ·
              refine ⟨63633485222285037321394421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42422323481523358214262947 63633485222285037321394421)
              ·
                refine ⟨5965639239589222248880727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63633485222285037321394421 5965639239589222248880727)
                ·
                  refine ⟨8948458859383833373321091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5965639239589222248880727 8948458859383833373321091)
                  ·
                    refine ⟨13422688289075750059981637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8948458859383833373321091 13422688289075750059981637)
                    ·
                      refine ⟨2516754054201703136246557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13422688289075750059981637 2516754054201703136246557)
                      ·
                        rfl

theorem cell23_4901361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_4901361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901361 prefixEnd_4901361 := by exact prefixLift 4901361
  have htrace : WordTrace (prefixWord ++ tailWord_4901361) baseStart_4901361 baseEnd_4901361 := by
    simpa [prefixWord, tailWord_4901361, baseEnd_4901361] using wordTrace_append hprefix tailTrace_4901361
  have hstable : (prefixWord ++ tailWord_4901361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901361).length < 2 ^ (prefixWord ++ tailWord_4901361).sum := by decide
  have hdescent : baseEnd_4901361 < baseStart_4901361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901388 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_4901388 : Nat := 118140960795 + 4901388 * 2 ^ 59
def prefixEnd_4901388 : Nat := 4983230072969 + 3 ^ 40 * 4901388 * 2
def baseEnd_4901388 : Nat := 838922639393124843536311

theorem tailTrace_4901388 : CollatzResearch.WordTrace tailWord_4901388 prefixEnd_4901388 838922639393124843536311 := by
  unfold tailWord_4901388
  simp only [CollatzResearch.WordTrace]
  refine ⟨89384153383557920635668409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119178871178077227514224545 89384153383557920635668409)
  ·
    refine ⟨67038115037668440476751307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89384153383557920635668409 67038115037668440476751307)
    ·
      refine ⟨100557172556502660715126961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67038115037668440476751307 100557172556502660715126961)
      ·
        refine ⟨75417879417376995536345221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100557172556502660715126961 75417879417376995536345221)
        ·
          refine ⟨14140852390758186663064729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75417879417376995536345221 14140852390758186663064729)
          ·
            refine ⟨10605639293068639997298547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14140852390758186663064729 10605639293068639997298547)
            ·
              refine ⟨15908458939602959995947821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10605639293068639997298547 15908458939602959995947821)
              ·
                refine ⟨5965672102351109998480433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15908458939602959995947821 5965672102351109998480433)
                ·
                  refine ⟨4474254076763332498860325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5965672102351109998480433 4474254076763332498860325)
                  ·
                    refine ⟨838922639393124843536311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4474254076763332498860325 838922639393124843536311)
                    ·
                      rfl

theorem cell23_4901388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_4901388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901388 prefixEnd_4901388 := by exact prefixLift 4901388
  have htrace : WordTrace (prefixWord ++ tailWord_4901388) baseStart_4901388 baseEnd_4901388 := by
    simpa [prefixWord, tailWord_4901388, baseEnd_4901388] using wordTrace_append hprefix tailTrace_4901388
  have hstable : (prefixWord ++ tailWord_4901388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901388).length < 2 ^ (prefixWord ++ tailWord_4901388).sum := by decide
  have hdescent : baseEnd_4901388 < baseStart_4901388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901408 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4901408 : Nat := 118140960795 + 4901408 * 2 ^ 59
def prefixEnd_4901408 : Nat := 4983230072969 + 3 ^ 40 * 4901408 * 2
def baseEnd_4901408 : Nat := 2516778187792464452358841

theorem tailTrace_4901408 : CollatzResearch.WordTrace tailWord_4901408 prefixEnd_4901408 2516778187792464452358841 := by
  unfold tailWord_4901408
  simp only [CollatzResearch.WordTrace]
  refine ⟨89384518113521692343532439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119179357484695589791376585 89384518113521692343532439)
  ·
    refine ⟨134076777170282538515298659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89384518113521692343532439 134076777170282538515298659)
    ·
      refine ⟨201115165755423807772947989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134076777170282538515298659 201115165755423807772947989)
      ·
        refine ⟨9427273394785490989356937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 201115165755423807772947989 9427273394785490989356937)
        ·
          refine ⟨7070455046089118242017703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9427273394785490989356937 7070455046089118242017703)
          ·
            refine ⟨10605682569133677363026555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070455046089118242017703 10605682569133677363026555)
            ·
              refine ⟨15908523853700516044539833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10605682569133677363026555 15908523853700516044539833)
              ·
                refine ⟨11931392890275387033404875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15908523853700516044539833 11931392890275387033404875)
                ·
                  refine ⟨17897089335413080550107313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11931392890275387033404875 17897089335413080550107313)
                  ·
                    refine ⟨13422817001559810412580485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17897089335413080550107313 13422817001559810412580485)
                    ·
                      refine ⟨2516778187792464452358841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13422817001559810412580485 2516778187792464452358841)
                      ·
                        rfl

theorem cell23_4901408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4901408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901408 prefixEnd_4901408 := by exact prefixLift 4901408
  have htrace : WordTrace (prefixWord ++ tailWord_4901408) baseStart_4901408 baseEnd_4901408 := by
    simpa [prefixWord, tailWord_4901408, baseEnd_4901408] using wordTrace_append hprefix tailTrace_4901408
  have hstable : (prefixWord ++ tailWord_4901408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901408).length < 2 ^ (prefixWord ++ tailWord_4901408).sum := by decide
  have hdescent : baseEnd_4901408 < baseStart_4901408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901411 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 3]
def baseStart_4901411 : Nat := 118140960795 + 4901411 * 2 ^ 59
def prefixEnd_4901411 : Nat := 4983230072969 + 3 ^ 40 * 4901411 * 2
def baseEnd_4901411 : Nat := 2516779728234427940621327

theorem tailTrace_4901411 : CollatzResearch.WordTrace tailWord_4901411 prefixEnd_4901411 2516779728234427940621327 := by
  unfold tailWord_4901411
  simp only [CollatzResearch.WordTrace]
  refine ⟨178769145646032516199424087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119179430430688344132949391 178769145646032516199424087)
  ·
    refine ⟨268153718469048774299136131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178769145646032516199424087 268153718469048774299136131)
    ·
      refine ⟨402230577703573161448704197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268153718469048774299136131 402230577703573161448704197)
      ·
        refine ⟨75418233319419967771632037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 402230577703573161448704197 75418233319419967771632037)
        ·
          refine ⟨14140918747391243957181007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75418233319419967771632037 14140918747391243957181007)
          ·
            refine ⟨21211378121086865935771511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14140918747391243957181007 21211378121086865935771511)
            ·
              refine ⟨31817067181630298903657267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21211378121086865935771511 31817067181630298903657267)
              ·
                refine ⟨47725600772445448355485901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31817067181630298903657267 47725600772445448355485901)
                ·
                  refine ⟨17897100289667043133307213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47725600772445448355485901 17897100289667043133307213)
                  ·
                    refine ⟨6711412608625141174990205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17897100289667043133307213 6711412608625141174990205)
                    ·
                      refine ⟨2516779728234427940621327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6711412608625141174990205 2516779728234427940621327)
                      ·
                        rfl

theorem cell23_4901411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_4901411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901411 prefixEnd_4901411 := by exact prefixLift 4901411
  have htrace : WordTrace (prefixWord ++ tailWord_4901411) baseStart_4901411 baseEnd_4901411 := by
    simpa [prefixWord, tailWord_4901411, baseEnd_4901411] using wordTrace_append hprefix tailTrace_4901411
  have hstable : (prefixWord ++ tailWord_4901411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901411).length < 2 ^ (prefixWord ++ tailWord_4901411).sum := by decide
  have hdescent : baseEnd_4901411 < baseStart_4901411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901412 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4901412 : Nat := 118140960795 + 4901412 * 2 ^ 59
def prefixEnd_4901412 : Nat := 4983230072969 + 3 ^ 40 * 4901412 * 2
def baseEnd_4901412 : Nat := 2516780241715082436708823

theorem tailTrace_4901412 : CollatzResearch.WordTrace tailWord_4901412 prefixEnd_4901412 2516780241715082436708823 := by
  unfold tailWord_4901412
  simp only [CollatzResearch.WordTrace]
  refine ⟨89384591059514446685105245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119179454746019262246806993 89384591059514446685105245)
  ·
    refine ⟨33519221647317917506914467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89384591059514446685105245 33519221647317917506914467)
    ·
      refine ⟨50278832470976876260371701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33519221647317917506914467 50278832470976876260371701)
      ·
        refine ⟨4713640544154082149409847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50278832470976876260371701 4713640544154082149409847)
        ·
          refine ⟨7070460816231123224114771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713640544154082149409847 7070460816231123224114771)
          ·
            refine ⟨10605691224346684836172157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070460816231123224114771 10605691224346684836172157)
            ·
              refine ⟨3977134209130006813564559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10605691224346684836172157 3977134209130006813564559)
              ·
                refine ⟨5965701313695010220346839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3977134209130006813564559 5965701313695010220346839)
                ·
                  refine ⟨8948551970542515330520259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5965701313695010220346839 8948551970542515330520259)
                  ·
                    refine ⟨13422827955813772995780389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8948551970542515330520259 13422827955813772995780389)
                    ·
                      refine ⟨2516780241715082436708823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13422827955813772995780389 2516780241715082436708823)
                      ·
                        rfl

theorem cell23_4901412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4901412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901412 prefixEnd_4901412 := by exact prefixLift 4901412
  have htrace : WordTrace (prefixWord ++ tailWord_4901412) baseStart_4901412 baseEnd_4901412 := by
    simpa [prefixWord, tailWord_4901412, baseEnd_4901412] using wordTrace_append hprefix tailTrace_4901412
  have hstable : (prefixWord ++ tailWord_4901412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901412).length < 2 ^ (prefixWord ++ tailWord_4901412).sum := by decide
  have hdescent : baseEnd_4901412 < baseStart_4901412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901424 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_4901424 : Nat := 118140960795 + 4901424 * 2 ^ 59
def prefixEnd_4901424 : Nat := 4983230072969 + 3 ^ 40 * 4901424 * 2
def baseEnd_4901424 : Nat := 2516786403482936389758767

theorem tailTrace_4901424 : CollatzResearch.WordTrace tailWord_4901424 prefixEnd_4901424 2516786403482936389758767 := by
  unfold tailWord_4901424
  simp only [CollatzResearch.WordTrace]
  refine ⟨89384809897492709709823663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119179746529990279613098217 89384809897492709709823663)
  ·
    refine ⟨134077214846239064564735495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89384809897492709709823663 134077214846239064564735495)
    ·
      refine ⟨201115822269358596847103243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134077214846239064564735495 201115822269358596847103243)
      ·
        refine ⟨301673733404037895270654865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201115822269358596847103243 301673733404037895270654865)
        ·
          refine ⟨226255300053028421452991149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301673733404037895270654865 226255300053028421452991149)
          ·
            refine ⟨84845737519885658044871681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226255300053028421452991149 84845737519885658044871681)
            ·
              refine ⟨63634303139914243533653761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84845737519885658044871681 63634303139914243533653761)
              ·
                refine ⟨47725727354935682650240321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63634303139914243533653761 47725727354935682650240321)
                ·
                  refine ⟨35794295516201761987680241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47725727354935682650240321 35794295516201761987680241)
                  ·
                    refine ⟨26845721637151321490760181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35794295516201761987680241 26845721637151321490760181)
                    ·
                      refine ⟨2516786403482936389758767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26845721637151321490760181 2516786403482936389758767)
                      ·
                        rfl

theorem cell23_4901424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_4901424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901424 prefixEnd_4901424 := by exact prefixLift 4901424
  have htrace : WordTrace (prefixWord ++ tailWord_4901424) baseStart_4901424 baseEnd_4901424 := by
    simpa [prefixWord, tailWord_4901424, baseEnd_4901424] using wordTrace_append hprefix tailTrace_4901424
  have hstable : (prefixWord ++ tailWord_4901424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901424).length < 2 ^ (prefixWord ++ tailWord_4901424).sum := by decide
  have hdescent : baseEnd_4901424 < baseStart_4901424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901553 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4901553 : Nat := 118140960795 + 4901553 * 2 ^ 59
def prefixEnd_4901553 : Nat := 4983230072969 + 3 ^ 40 * 4901553 * 2
def baseEnd_4901553 : Nat := 2516852642487366385045675

theorem tailTrace_4901553 : CollatzResearch.WordTrace tailWord_4901553 prefixEnd_4901553 2516852642487366385045675 := by
  unfold tailWord_4901553
  simp only [CollatzResearch.WordTrace]
  refine ⟨178774324811518074451093313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119182883207678716300728875 178774324811518074451093313)
  ·
    refine ⟨134080743608638555838319985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178774324811518074451093313 134080743608638555838319985)
    ·
      refine ⟨100560557706478916878739989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134080743608638555838319985 100560557706478916878739989)
      ·
        refine ⟨4713776142491199228690937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100560557706478916878739989 4713776142491199228690937)
        ·
          refine ⟨3535332106868399421518203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4713776142491199228690937 3535332106868399421518203)
          ·
            refine ⟨5302998160302599132277305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535332106868399421518203 5302998160302599132277305)
            ·
              refine ⟨3977248620226949349207979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5302998160302599132277305 3977248620226949349207979)
              ·
                refine ⟨5965872930340424023811969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3977248620226949349207979 5965872930340424023811969)
                ·
                  refine ⟨4474404697755318017858977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5965872930340424023811969 4474404697755318017858977)
                  ·
                    refine ⟨3355803523316488513394233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4474404697755318017858977 3355803523316488513394233)
                    ·
                      refine ⟨2516852642487366385045675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355803523316488513394233 2516852642487366385045675)
                      ·
                        rfl

theorem cell23_4901553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4901553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901553 prefixEnd_4901553 := by exact prefixLift 4901553
  have htrace : WordTrace (prefixWord ++ tailWord_4901553) baseStart_4901553 baseEnd_4901553 := by
    simpa [prefixWord, tailWord_4901553, baseEnd_4901553] using wordTrace_append hprefix tailTrace_4901553
  have hstable : (prefixWord ++ tailWord_4901553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901553).length < 2 ^ (prefixWord ++ tailWord_4901553).sum := by decide
  have hdescent : baseEnd_4901553 < baseStart_4901553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901585 : List Nat := [1, 2, 2, 1, 2, 3, 2, 5, 1, 4]
def baseStart_4901585 : Nat := 118140960795 + 4901585 * 2 ^ 59
def prefixEnd_4901585 : Nat := 4983230072969 + 3 ^ 40 * 4901585 * 2
def baseEnd_4901585 : Nat := 838956357956103419948509

theorem tailTrace_4901585 : CollatzResearch.WordTrace tailWord_4901585 prefixEnd_4901585 838956357956103419948509 := by
  unfold tailWord_4901585
  simp only [CollatzResearch.WordTrace]
  refine ⟨178775491947402143916258209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119183661298268095944172139 178775491947402143916258209)
  ·
    refine ⟨134081618960551607937193657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178775491947402143916258209 134081618960551607937193657)
    ·
      refine ⟨100561214220413705952895243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134081618960551607937193657 100561214220413705952895243)
      ·
        refine ⟨150841821330620558929342865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100561214220413705952895243 150841821330620558929342865)
        ·
          refine ⟨113131365997965419197007149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150841821330620558929342865 113131365997965419197007149)
          ·
            refine ⟨42424262249237032198877681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113131365997965419197007149 42424262249237032198877681)
            ·
              refine ⟨31818196686927774149158261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42424262249237032198877681 31818196686927774149158261)
              ·
                refine ⟨2982955939399478826483587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31818196686927774149158261 2982955939399478826483587)
                ·
                  refine ⟨4474433909099218239725381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982955939399478826483587 4474433909099218239725381)
                  ·
                    refine ⟨838956357956103419948509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4474433909099218239725381 838956357956103419948509)
                    ·
                      rfl

theorem cell23_4901585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_4901585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901585 prefixEnd_4901585 := by exact prefixLift 4901585
  have htrace : WordTrace (prefixWord ++ tailWord_4901585) baseStart_4901585 baseEnd_4901585 := by
    simpa [prefixWord, tailWord_4901585, baseEnd_4901585] using wordTrace_append hprefix tailTrace_4901585
  have hstable : (prefixWord ++ tailWord_4901585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901585).length < 2 ^ (prefixWord ++ tailWord_4901585).sum := by decide
  have hdescent : baseEnd_4901585 < baseStart_4901585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901628 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_4901628 : Nat := 118140960795 + 4901628 * 2 ^ 59
def prefixEnd_4901628 : Nat := 4983230072969 + 3 ^ 40 * 4901628 * 2
def baseEnd_4901628 : Nat := 838963717845484530535943

theorem tailTrace_4901628 : CollatzResearch.WordTrace tailWord_4901628 prefixEnd_4901628 838963717845484530535943 := by
  unfold tailWord_4901628
  simp only [CollatzResearch.WordTrace]
  refine ⟨89388530143123181130036769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119184706857497574840049025 89388530143123181130036769)
  ·
    refine ⟨67041397607342385847527577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89388530143123181130036769 67041397607342385847527577)
    ·
      refine ⟨50281048205506789385645683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67041397607342385847527577 50281048205506789385645683)
      ·
        refine ⟨75421572308260184078468525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50281048205506789385645683 75421572308260184078468525)
        ·
          refine ⟨28283089615597569029425697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75421572308260184078468525 28283089615597569029425697)
          ·
            refine ⟨21212317211698176772069273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28283089615597569029425697 21212317211698176772069273)
            ·
              refine ⟨15909237908773632579051955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21212317211698176772069273 15909237908773632579051955)
              ·
                refine ⟨23863856863160448868577933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15909237908773632579051955 23863856863160448868577933)
                ·
                  refine ⟨8948946323685168325716725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23863856863160448868577933 8948946323685168325716725)
                  ·
                    refine ⟨838963717845484530535943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8948946323685168325716725 838963717845484530535943)
                    ·
                      rfl

theorem cell23_4901628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_4901628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901628 prefixEnd_4901628 := by exact prefixLift 4901628
  have htrace : WordTrace (prefixWord ++ tailWord_4901628) baseStart_4901628 baseEnd_4901628 := by
    simpa [prefixWord, tailWord_4901628, baseEnd_4901628] using wordTrace_append hprefix tailTrace_4901628
  have hstable : (prefixWord ++ tailWord_4901628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901628).length < 2 ^ (prefixWord ++ tailWord_4901628).sum := by decide
  have hdescent : baseEnd_4901628 < baseStart_4901628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901682 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_4901682 : Nat := 118140960795 + 4901682 * 2 ^ 59
def prefixEnd_4901682 : Nat := 4983230072969 + 3 ^ 40 * 4901682 * 2
def baseEnd_4901682 : Nat := 2516918881491796380332581

theorem tailTrace_4901682 : CollatzResearch.WordTrace tailWord_4901682 prefixEnd_4901682 2516918881491796380332581 := by
  unfold tailWord_4901682
  simp only [CollatzResearch.WordTrace]
  refine ⟨44694757457012682370634825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119186019885367152988359533 44694757457012682370634825)
  ·
    refine ⟨33521068092759511777976119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44694757457012682370634825 33521068092759511777976119)
    ·
      refine ⟨50281602139139267666964179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33521068092759511777976119 50281602139139267666964179)
      ·
        refine ⟨75422403208708901500446269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50281602139139267666964179 75422403208708901500446269)
        ·
          refine ⟨28283401203265838062667351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75422403208708901500446269 28283401203265838062667351)
          ·
            refine ⟨42425101804898757094001027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28283401203265838062667351 42425101804898757094001027)
            ·
              refine ⟨63637652707348135641001541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42425101804898757094001027 63637652707348135641001541)
              ·
                refine ⟨11932059882627775432687789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63637652707348135641001541 11932059882627775432687789)
                ·
                  refine ⟨4474522455985415787257921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11932059882627775432687789 4474522455985415787257921)
                  ·
                    refine ⟨3355891841989061840443441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4474522455985415787257921 3355891841989061840443441)
                    ·
                      refine ⟨2516918881491796380332581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355891841989061840443441 2516918881491796380332581)
                      ·
                        rfl

theorem cell23_4901682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_4901682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901682 prefixEnd_4901682 := by exact prefixLift 4901682
  have htrace : WordTrace (prefixWord ++ tailWord_4901682) baseStart_4901682 baseEnd_4901682 := by
    simpa [prefixWord, tailWord_4901682, baseEnd_4901682] using wordTrace_append hprefix tailTrace_4901682
  have hstable : (prefixWord ++ tailWord_4901682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901682).length < 2 ^ (prefixWord ++ tailWord_4901682).sum := by decide
  have hdescent : baseEnd_4901682 < baseStart_4901682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901693 : List Nat := [1, 4, 1, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4901693 : Nat := 118140960795 + 4901693 * 2 ^ 59
def prefixEnd_4901693 : Nat := 4983230072969 + 3 ^ 40 * 4901693 * 2
def baseEnd_4901693 : Nat := 2516924529778995837295031

theorem tailTrace_4901693 : CollatzResearch.WordTrace tailWord_4901693 prefixEnd_4901693 2516924529778995837295031 := by
  unfold tailWord_4901693
  simp only [CollatzResearch.WordTrace]
  refine ⟨178779431031010878361189733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119186287354007252240793155 178779431031010878361189733)
  ·
    refine ⟨33521143318314539692723075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178779431031010878361189733 33521143318314539692723075)
    ·
      refine ⟨50281714977471809539084613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33521143318314539692723075 50281714977471809539084613)
      ·
        refine ⟨9427821558275964288578365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50281714977471809539084613 9427821558275964288578365)
        ·
          refine ⟨3535433084353486608216887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9427821558275964288578365 3535433084353486608216887)
          ·
            refine ⟨5303149626530229912325331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535433084353486608216887 5303149626530229912325331)
            ·
              refine ⟨7954724439795344868487997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303149626530229912325331 7954724439795344868487997)
              ·
                refine ⟨2983021664923254325682999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7954724439795344868487997 2983021664923254325682999)
                ·
                  refine ⟨4474532497384881488524499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983021664923254325682999 4474532497384881488524499)
                  ·
                    refine ⟨6711798746077322232786749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4474532497384881488524499 6711798746077322232786749)
                    ·
                      refine ⟨2516924529778995837295031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6711798746077322232786749 2516924529778995837295031)
                      ·
                        rfl

theorem cell23_4901693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4901693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901693 prefixEnd_4901693 := by exact prefixLift 4901693
  have htrace : WordTrace (prefixWord ++ tailWord_4901693) baseStart_4901693 baseEnd_4901693 := by
    simpa [prefixWord, tailWord_4901693, baseEnd_4901693] using wordTrace_append hprefix tailTrace_4901693
  have hstable : (prefixWord ++ tailWord_4901693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901693).length < 2 ^ (prefixWord ++ tailWord_4901693).sum := by decide
  have hdescent : baseEnd_4901693 < baseStart_4901693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901716 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_4901716 : Nat := 118140960795 + 4901716 * 2 ^ 59
def prefixEnd_4901716 : Nat := 4983230072969 + 3 ^ 40 * 4901716 * 2
def baseEnd_4901716 : Nat := 2516936339834049247307425

theorem tailTrace_4901716 : CollatzResearch.WordTrace tailWord_4901716 prefixEnd_4901716 2516936339834049247307425 := by
  unfold tailWord_4901716
  simp only [CollatzResearch.WordTrace]
  refine ⟨89390134954963776644638501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119186846606618368859518001 89390134954963776644638501)
  ·
    refine ⟨16760650304055708120869719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89390134954963776644638501 16760650304055708120869719)
    ·
      refine ⟨25140975456083562181304579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16760650304055708120869719 25140975456083562181304579)
      ·
        refine ⟨37711463184125343271956869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25140975456083562181304579 37711463184125343271956869)
        ·
          refine ⟨7070899347023501863491913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37711463184125343271956869 7070899347023501863491913)
          ·
            refine ⟨5303174510267626397618935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7070899347023501863491913 5303174510267626397618935)
            ·
              refine ⟨7954761765401439596428403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303174510267626397618935 7954761765401439596428403)
              ·
                refine ⟨11932142648102159394642605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7954761765401439596428403 11932142648102159394642605)
                ·
                  refine ⟨4474553493038309772990977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11932142648102159394642605 4474553493038309772990977)
                  ·
                    refine ⟨3355915119778732329743233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4474553493038309772990977 3355915119778732329743233)
                    ·
                      refine ⟨2516936339834049247307425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355915119778732329743233 2516936339834049247307425)
                      ·
                        rfl

theorem cell23_4901716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_4901716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901716 prefixEnd_4901716 := by exact prefixLift 4901716
  have htrace : WordTrace (prefixWord ++ tailWord_4901716) baseStart_4901716 baseEnd_4901716 := by
    simpa [prefixWord, tailWord_4901716, baseEnd_4901716] using wordTrace_append hprefix tailTrace_4901716
  have hstable : (prefixWord ++ tailWord_4901716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901716).length < 2 ^ (prefixWord ++ tailWord_4901716).sum := by decide
  have hdescent : baseEnd_4901716 < baseStart_4901716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901755 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 3, 4, 2]
def baseStart_4901755 : Nat := 118140960795 + 4901755 * 2 ^ 59
def prefixEnd_4901755 : Nat := 4983230072969 + 3 ^ 40 * 4901755 * 2
def baseEnd_4901755 : Nat := 2516956365579574594719745

theorem tailTrace_4901755 : CollatzResearch.WordTrace tailWord_4901755 prefixEnd_4901755 2516956365579574594719745 := by
  unfold tailWord_4901755
  simp only [CollatzResearch.WordTrace]
  refine ⟨178781692356786262949946719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119187794904524175299964479 178781692356786262949946719)
  ·
    refine ⟨268172538535179394424920079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178781692356786262949946719 268172538535179394424920079)
    ·
      refine ⟨402258807802769091637380119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268172538535179394424920079 402258807802769091637380119)
      ·
        refine ⟨603388211704153637456070179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402258807802769091637380119 603388211704153637456070179)
        ·
          refine ⟨905082317556230456184105269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603388211704153637456070179 905082317556230456184105269)
          ·
            refine ⟨84851467270896605267259869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 905082317556230456184105269 84851467270896605267259869)
            ·
              refine ⟨31819300226586226975222451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84851467270896605267259869 31819300226586226975222451)
              ·
                refine ⟨47728950339879340462833677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31819300226586226975222451 47728950339879340462833677)
                ·
                  refine ⟨17898356377454752673562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47728950339879340462833677 17898356377454752673562629)
                  ·
                    refine ⟨3355941820772766126292993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17898356377454752673562629 3355941820772766126292993)
                    ·
                      refine ⟨2516956365579574594719745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355941820772766126292993 2516956365579574594719745)
                      ·
                        rfl

theorem cell23_4901755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 4, 2].length) (baseStart_4901755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901755 prefixEnd_4901755 := by exact prefixLift 4901755
  have htrace : WordTrace (prefixWord ++ tailWord_4901755) baseStart_4901755 baseEnd_4901755 := by
    simpa [prefixWord, tailWord_4901755, baseEnd_4901755] using wordTrace_append hprefix tailTrace_4901755
  have hstable : (prefixWord ++ tailWord_4901755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901755).length < 2 ^ (prefixWord ++ tailWord_4901755).sum := by decide
  have hdescent : baseEnd_4901755 < baseStart_4901755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901772 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 4, 2, 2]
def baseStart_4901772 : Nat := 118140960795 + 4901772 * 2 ^ 59
def prefixEnd_4901772 : Nat := 4983230072969 + 3 ^ 40 * 4901772 * 2
def baseEnd_4901772 : Nat := 2516965094750701028207167

theorem tailTrace_4901772 : CollatzResearch.WordTrace tailWord_4901772 prefixEnd_4901772 2516965094750701028207167 := by
  unfold tailWord_4901772
  simp only [CollatzResearch.WordTrace]
  refine ⟨89391156198862337426657785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119188208265149783235543713 89391156198862337426657785)
  ·
    refine ⟨67043367149146753069993339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89391156198862337426657785 67043367149146753069993339)
    ·
      refine ⟨100565050723720129604990009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67043367149146753069993339 100565050723720129604990009)
      ·
        refine ⟨75423788042790097203742507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100565050723720129604990009 75423788042790097203742507)
        ·
          refine ⟨113135682064185145805613761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75423788042790097203742507 113135682064185145805613761)
          ·
            refine ⟨84851761548138859354210321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113135682064185145805613761 84851761548138859354210321)
            ·
              refine ⟨63638821161104144515657741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84851761548138859354210321 63638821161104144515657741)
              ·
                refine ⟨23864557935414054193371653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63638821161104144515657741 23864557935414054193371653)
                ·
                  refine ⟨4474604612890135161257185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23864557935414054193371653 4474604612890135161257185)
                  ·
                    refine ⟨3355953459667601370942889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4474604612890135161257185 3355953459667601370942889)
                    ·
                      refine ⟨2516965094750701028207167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355953459667601370942889 2516965094750701028207167)
                      ·
                        rfl

theorem cell23_4901772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_4901772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901772 prefixEnd_4901772 := by exact prefixLift 4901772
  have htrace : WordTrace (prefixWord ++ tailWord_4901772) baseStart_4901772 baseEnd_4901772 := by
    simpa [prefixWord, tailWord_4901772, baseEnd_4901772] using wordTrace_append hprefix tailTrace_4901772
  have hstable : (prefixWord ++ tailWord_4901772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901772).length < 2 ^ (prefixWord ++ tailWord_4901772).sum := by decide
  have hdescent : baseEnd_4901772 < baseStart_4901772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901789 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_4901789 : Nat := 118140960795 + 4901789 * 2 ^ 59
def prefixEnd_4901789 : Nat := 4983230072969 + 3 ^ 40 * 4901789 * 2
def baseEnd_4901789 : Nat := 2516973823921827461694589

theorem tailTrace_4901789 : CollatzResearch.WordTrace tailWord_4901789 prefixEnd_4901789 2516973823921827461694589 := by
  unfold tailWord_4901789
  simp only [CollatzResearch.WordTrace]
  refine ⟨178782932438663086756684421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119188621625775391171122947 178782932438663086756684421)
  ·
    refine ⟨33521799832249328766878329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178782932438663086756684421 33521799832249328766878329)
    ·
      refine ⟨25141349874186996575158747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33521799832249328766878329 25141349874186996575158747)
      ·
        refine ⟨37712024811280494862738121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25141349874186996575158747 37712024811280494862738121)
        ·
          refine ⟨28284018608460371147053591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37712024811280494862738121 28284018608460371147053591)
          ·
            refine ⟨42426027912690556720580387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28284018608460371147053591 42426027912690556720580387)
            ·
              refine ⟨63639041869035835080870581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42426027912690556720580387 63639041869035835080870581)
              ·
                refine ⟨5966160175222109538831617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63639041869035835080870581 5966160175222109538831617)
                ·
                  refine ⟨4474620131416582154123713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5966160175222109538831617 4474620131416582154123713)
                  ·
                    refine ⟨3355965098562436615592785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4474620131416582154123713 3355965098562436615592785)
                    ·
                      refine ⟨2516973823921827461694589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3355965098562436615592785 2516973823921827461694589)
                      ·
                        rfl

theorem cell23_4901789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_4901789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901789 prefixEnd_4901789 := by exact prefixLift 4901789
  have htrace : WordTrace (prefixWord ++ tailWord_4901789) baseStart_4901789 baseEnd_4901789 := by
    simpa [prefixWord, tailWord_4901789, baseEnd_4901789] using wordTrace_append hprefix tailTrace_4901789
  have hstable : (prefixWord ++ tailWord_4901789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901789).length < 2 ^ (prefixWord ++ tailWord_4901789).sum := by decide
  have hdescent : baseEnd_4901789 < baseStart_4901789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901865 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 3]
def baseStart_4901865 : Nat := 118140960795 + 4901865 * 2 ^ 59
def prefixEnd_4901865 : Nat := 4983230072969 + 3 ^ 40 * 4901865 * 2
def baseEnd_4901865 : Nat := 2517012848451569164344239

theorem tailTrace_4901865 : CollatzResearch.WordTrace tailWord_4901865 prefixEnd_4901865 2517012848451569164344239 := by
  unfold tailWord_4901865
  simp only [CollatzResearch.WordTrace]
  refine ⟨178785704386387751736451049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119190469590925167824300699 178785704386387751736451049)
  ·
    refine ⟨134089278289790813802338287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178785704386387751736451049 134089278289790813802338287)
    ·
      refine ⟨201133917434686220703507431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134089278289790813802338287 201133917434686220703507431)
      ·
        refine ⟨301700876152029331055261147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201133917434686220703507431 301700876152029331055261147)
        ·
          refine ⟨452551314228043996582891721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301700876152029331055261147 452551314228043996582891721)
          ·
            refine ⟨339413485671032997437168791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452551314228043996582891721 339413485671032997437168791)
            ·
              refine ⟨509120228506549496155753187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339413485671032997437168791 509120228506549496155753187)
              ·
                refine ⟨763680342759824244233629781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509120228506549496155753187 763680342759824244233629781)
                ·
                  refine ⟨8949379016716690362112849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 763680342759824244233629781 8949379016716690362112849)
                  ·
                    refine ⟨6712034262537517771584637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8949379016716690362112849 6712034262537517771584637)
                    ·
                      refine ⟨2517012848451569164344239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6712034262537517771584637 2517012848451569164344239)
                      ·
                        rfl

theorem cell23_4901865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_4901865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901865 prefixEnd_4901865 := by exact prefixLift 4901865
  have htrace : WordTrace (prefixWord ++ tailWord_4901865) baseStart_4901865 baseEnd_4901865 := by
    simpa [prefixWord, tailWord_4901865, baseEnd_4901865] using wordTrace_append hprefix tailTrace_4901865
  have hstable : (prefixWord ++ tailWord_4901865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901865).length < 2 ^ (prefixWord ++ tailWord_4901865).sum := by decide
  have hdescent : baseEnd_4901865 < baseStart_4901865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901885 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 6]
def baseStart_4901885 : Nat := 118140960795 + 4901885 * 2 ^ 59
def prefixEnd_4901885 : Nat := 4983230072969 + 3 ^ 40 * 4901885 * 2
def baseEnd_4901885 : Nat := 279669235340517676232683

theorem tailTrace_4901885 : CollatzResearch.WordTrace tailWord_4901885 prefixEnd_4901885 279669235340517676232683 := by
  unfold tailWord_4901885
  simp only [CollatzResearch.WordTrace]
  refine ⟨178786433846315295152179109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119190955897543530101452739 178786433846315295152179109)
  ·
    refine ⟨33522456346184117841033583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178786433846315295152179109 33522456346184117841033583)
    ·
      refine ⟨50283684519276176761550375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33522456346184117841033583 50283684519276176761550375)
      ·
        refine ⟨75425526778914265142325563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50283684519276176761550375 75425526778914265142325563)
        ·
          refine ⟨113138290168371397713488345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75425526778914265142325563 113138290168371397713488345)
          ·
            refine ⟨84853717626278548285116259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113138290168371397713488345 84853717626278548285116259)
            ·
              refine ⟨127280576439417822427674389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84853717626278548285116259 127280576439417822427674389)
              ·
                refine ⟨5966277020597710426297237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127280576439417822427674389 5966277020597710426297237)
                ·
                  refine ⟨279669235340517676232683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5966277020597710426297237 279669235340517676232683)
                  ·
                    rfl

theorem cell23_4901885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_4901885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901885 prefixEnd_4901885 := by exact prefixLift 4901885
  have htrace : WordTrace (prefixWord ++ tailWord_4901885) baseStart_4901885 baseEnd_4901885 := by
    simpa [prefixWord, tailWord_4901885, baseEnd_4901885] using wordTrace_append hprefix tailTrace_4901885
  have hstable : (prefixWord ++ tailWord_4901885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901885).length < 2 ^ (prefixWord ++ tailWord_4901885).sum := by decide
  have hdescent : baseEnd_4901885 < baseStart_4901885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901889 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 3, 4]
def baseStart_4901889 : Nat := 118140960795 + 4901889 * 2 ^ 59
def prefixEnd_4901889 : Nat := 4983230072969 + 3 ^ 40 * 4901889 * 2
def baseEnd_4901889 : Nat := 839008390662425690148043

theorem tailTrace_4901889 : CollatzResearch.WordTrace tailWord_4901889 prefixEnd_4901889 839008390662425690148043 := by
  unfold tailWord_4901889
  simp only [CollatzResearch.WordTrace]
  refine ⟨178786579738300803835324721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119191053158867202556883147 178786579738300803835324721)
  ·
    refine ⟨134089934803725602876493541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178786579738300803835324721 134089934803725602876493541)
    ·
      refine ⟨25141862775698550539342539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134089934803725602876493541 25141862775698550539342539)
      ·
        refine ⟨37712794163547825809013809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25141862775698550539342539 37712794163547825809013809)
        ·
          refine ⟨28284595622660869356760357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37712794163547825809013809 28284595622660869356760357)
          ·
            refine ⟨5303361679248913004392567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28284595622660869356760357 5303361679248913004392567)
            ·
              refine ⟨7955042518873369506588851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303361679248913004392567 7955042518873369506588851)
              ·
                refine ⟨11932563778310054259883277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7955042518873369506588851 11932563778310054259883277)
                ·
                  refine ⟨4474711416866270347456229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11932563778310054259883277 4474711416866270347456229)
                  ·
                    refine ⟨839008390662425690148043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4474711416866270347456229 839008390662425690148043)
                    ·
                      rfl

theorem cell23_4901889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_4901889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901889 prefixEnd_4901889 := by exact prefixLift 4901889
  have htrace : WordTrace (prefixWord ++ tailWord_4901889) baseStart_4901889 baseEnd_4901889 := by
    simpa [prefixWord, tailWord_4901889, baseEnd_4901889] using wordTrace_append hprefix tailTrace_4901889
  have hstable : (prefixWord ++ tailWord_4901889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901889).length < 2 ^ (prefixWord ++ tailWord_4901889).sum := by decide
  have hdescent : baseEnd_4901889 < baseStart_4901889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901902 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_4901902 : Nat := 118140960795 + 4901902 * 2 ^ 59
def prefixEnd_4901902 : Nat := 4983230072969 + 3 ^ 40 * 4901902 * 2
def baseEnd_4901902 : Nat := 279670205248420613286841

theorem tailTrace_4901902 : CollatzResearch.WordTrace tailWord_4901902 prefixEnd_4901902 279670205248420613286841 := by
  unfold tailWord_4901902
  simp only [CollatzResearch.WordTrace]
  refine ⟨22348381735906713381943495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119191369258169138037031973 22348381735906713381943495)
  ·
    refine ⟨33522572603860070072915243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22348381735906713381943495 33522572603860070072915243)
    ·
      refine ⟨50283858905790105109372865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33522572603860070072915243 50283858905790105109372865)
      ·
        refine ⟨37712894179342578832029649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50283858905790105109372865 37712894179342578832029649)
        ·
          refine ⟨28284670634506934124022237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37712894179342578832029649 28284670634506934124022237)
          ·
            refine ⟨10606751487940100296508339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28284670634506934124022237 10606751487940100296508339)
            ·
              refine ⟨15910127231910150444762509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10606751487940100296508339 15910127231910150444762509)
              ·
                refine ⟨5966297711966306416785941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15910127231910150444762509 5966297711966306416785941)
                ·
                  refine ⟨279670205248420613286841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5966297711966306416785941 279670205248420613286841)
                  ·
                    rfl

theorem cell23_4901902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_4901902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901902 prefixEnd_4901902 := by exact prefixLift 4901902
  have htrace : WordTrace (prefixWord ++ tailWord_4901902) baseStart_4901902 baseEnd_4901902 := by
    simpa [prefixWord, tailWord_4901902, baseEnd_4901902] using wordTrace_append hprefix tailTrace_4901902
  have hstable : (prefixWord ++ tailWord_4901902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901902).length < 2 ^ (prefixWord ++ tailWord_4901902).sum := by decide
  have hdescent : baseEnd_4901902 < baseStart_4901902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901940 : List Nat := [2, 5, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_4901940 : Nat := 118140960795 + 4901940 * 2 ^ 59
def prefixEnd_4901940 : Nat := 4983230072969 + 3 ^ 40 * 4901940 * 2
def baseEnd_4901940 : Nat := 839017119833552123635465

theorem tailTrace_4901940 : CollatzResearch.WordTrace tailWord_4901940 prefixEnd_4901940 839017119833552123635465 := by
  unfold tailWord_4901940
  simp only [CollatzResearch.WordTrace]
  refine ⟨89394219930558019772715637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119192293240744026363620849 89394219930558019772715637)
  ·
    refine ⟨8380708118489814353692091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89394219930558019772715637 8380708118489814353692091)
    ·
      refine ⟨12571062177734721530538137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8380708118489814353692091 12571062177734721530538137)
      ·
        refine ⟨9428296633301041147903603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12571062177734721530538137 9428296633301041147903603)
        ·
          refine ⟨14142444949951561721855405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9428296633301041147903603 14142444949951561721855405)
          ·
            refine ⟨5303416856231835645695777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14142444949951561721855405 5303416856231835645695777)
            ·
              refine ⟨3977562642173876734271833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303416856231835645695777 3977562642173876734271833)
              ·
                refine ⟨2983171981630407550703875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977562642173876734271833 2983171981630407550703875)
                ·
                  refine ⟨4474757972445611326055813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983171981630407550703875 4474757972445611326055813)
                  ·
                    refine ⟨839017119833552123635465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4474757972445611326055813 839017119833552123635465)
                    ·
                      rfl

theorem cell23_4901940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_4901940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901940 prefixEnd_4901940 := by exact prefixLift 4901940
  have htrace : WordTrace (prefixWord ++ tailWord_4901940) baseStart_4901940 baseEnd_4901940 := by
    simpa [prefixWord, tailWord_4901940, baseEnd_4901940] using wordTrace_append hprefix tailTrace_4901940
  have hstable : (prefixWord ++ tailWord_4901940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901940).length < 2 ^ (prefixWord ++ tailWord_4901940).sum := by decide
  have hdescent : baseEnd_4901940 < baseStart_4901940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901955 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 5]
def baseStart_4901955 : Nat := 118140960795 + 4901955 * 2 ^ 59
def prefixEnd_4901955 : Nat := 4983230072969 + 3 ^ 40 * 4901955 * 2
def baseEnd_4901955 : Nat := 2517059061710473812218825

theorem tailTrace_4901955 : CollatzResearch.WordTrace tailWord_4901955 prefixEnd_4901955 2517059061710473812218825 := by
  unfold tailWord_4901955
  simp only [CollatzResearch.WordTrace]
  refine ⟨178788986956061697107227319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119192657970707798071484879 178788986956061697107227319)
  ·
    refine ⟨268183480434092545660840979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178788986956061697107227319 268183480434092545660840979)
    ·
      refine ⟨402275220651138818491261469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268183480434092545660840979 402275220651138818491261469)
      ·
        refine ⟨150853207744177056934223051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 402275220651138818491261469 150853207744177056934223051)
        ·
          refine ⟨226279811616265585401334577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150853207744177056934223051 226279811616265585401334577)
          ·
            refine ⟨169709858712199189051000933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226279811616265585401334577 169709858712199189051000933)
            ·
              refine ⟨31820598508537347947062675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169709858712199189051000933 31820598508537347947062675)
              ·
                refine ⟨47730897762806021920594013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31820598508537347947062675 47730897762806021920594013)
                ·
                  refine ⟨17899086661052258220222755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47730897762806021920594013 17899086661052258220222755)
                  ·
                    refine ⟨26848629991578387330334133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17899086661052258220222755 26848629991578387330334133)
                    ·
                      refine ⟨2517059061710473812218825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26848629991578387330334133 2517059061710473812218825)
                      ·
                        rfl

theorem cell23_4901955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_4901955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901955 prefixEnd_4901955 := by exact prefixLift 4901955
  have htrace : WordTrace (prefixWord ++ tailWord_4901955) baseStart_4901955 baseEnd_4901955 := by
    simpa [prefixWord, tailWord_4901955, baseEnd_4901955] using wordTrace_append hprefix tailTrace_4901955
  have hstable : (prefixWord ++ tailWord_4901955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901955).length < 2 ^ (prefixWord ++ tailWord_4901955).sum := by decide
  have hdescent : baseEnd_4901955 < baseStart_4901955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901969 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 5, 2, 2]
def baseStart_4901969 : Nat := 118140960795 + 4901969 * 2 ^ 59
def prefixEnd_4901969 : Nat := 4983230072969 + 3 ^ 40 * 4901969 * 2
def baseEnd_4901969 : Nat := 2517066250439636757443761

theorem tailTrace_4901969 : CollatzResearch.WordTrace tailWord_4901969 prefixEnd_4901969 2517066250439636757443761 := by
  unfold tailWord_4901969
  simp only [CollatzResearch.WordTrace]
  refine ⟨178789497578010977498236961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119192998385340651665491307 178789497578010977498236961)
  ·
    refine ⟨134092123183508233123677721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178789497578010977498236961 134092123183508233123677721)
    ·
      refine ⟨100569092387631174842758291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134092123183508233123677721 100569092387631174842758291)
      ·
        refine ⟨150853638581446762264137437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100569092387631174842758291 150853638581446762264137437)
        ·
          refine ⟨56570114468042535849051539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150853638581446762264137437 56570114468042535849051539)
          ·
            refine ⟨84855171702063803773577309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56570114468042535849051539 84855171702063803773577309)
            ·
              refine ⟨31820689388273926415091491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84855171702063803773577309 31820689388273926415091491)
              ·
                refine ⟨47731034082410889622637237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31820689388273926415091491 47731034082410889622637237)
                ·
                  refine ⟨4474784445226020902122241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47731034082410889622637237 4474784445226020902122241)
                  ·
                    refine ⟨3356088333919515676591681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4474784445226020902122241 3356088333919515676591681)
                    ·
                      refine ⟨2517066250439636757443761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356088333919515676591681 2517066250439636757443761)
                      ·
                        rfl

theorem cell23_4901969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_4901969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901969 prefixEnd_4901969 := by exact prefixLift 4901969
  have htrace : WordTrace (prefixWord ++ tailWord_4901969) baseStart_4901969 baseEnd_4901969 := by
    simpa [prefixWord, tailWord_4901969, baseEnd_4901969] using wordTrace_append hprefix tailTrace_4901969
  have hstable : (prefixWord ++ tailWord_4901969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901969).length < 2 ^ (prefixWord ++ tailWord_4901969).sum := by decide
  have hdescent : baseEnd_4901969 < baseStart_4901969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901986 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4901986 : Nat := 118140960795 + 4901986 * 2 ^ 59
def prefixEnd_4901986 : Nat := 4983230072969 + 3 ^ 40 * 4901986 * 2
def baseEnd_4901986 : Nat := 2517074979610763190931183

theorem tailTrace_4901986 : CollatzResearch.WordTrace tailWord_4901986 prefixEnd_4901986 2517074979610763190931183 := by
  unfold tailWord_4901986
  simp only [CollatzResearch.WordTrace]
  refine ⟨44697529404737347350401453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119193411745966259601070541 44697529404737347350401453)
  ·
    refine ⟨16761573526776505256400545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44697529404737347350401453 16761573526776505256400545)
    ·
      refine ⟨12571180145082378942300409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16761573526776505256400545 12571180145082378942300409)
      ·
        refine ⟨9428385108811784206725307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12571180145082378942300409 9428385108811784206725307)
        ·
          refine ⟨14142577663217676310087961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9428385108811784206725307 14142577663217676310087961)
          ·
            refine ⟨10606933247413257232565971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14142577663217676310087961 10606933247413257232565971)
            ·
              refine ⟨15910399871119885848848957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10606933247413257232565971 15910399871119885848848957)
              ·
                refine ⟨5966399951669957193318359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15910399871119885848848957 5966399951669957193318359)
                ·
                  refine ⟨8949599927504935789977539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5966399951669957193318359 8949599927504935789977539)
                  ·
                    refine ⟨13424399891257403684966309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8949599927504935789977539 13424399891257403684966309)
                    ·
                      refine ⟨2517074979610763190931183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13424399891257403684966309 2517074979610763190931183)
                      ·
                        rfl

theorem cell23_4901986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4901986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901986 prefixEnd_4901986 := by exact prefixLift 4901986
  have htrace : WordTrace (prefixWord ++ tailWord_4901986) baseStart_4901986 baseEnd_4901986 := by
    simpa [prefixWord, tailWord_4901986, baseEnd_4901986] using wordTrace_append hprefix tailTrace_4901986
  have hstable : (prefixWord ++ tailWord_4901986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901986).length < 2 ^ (prefixWord ++ tailWord_4901986).sum := by decide
  have hdescent : baseEnd_4901986 < baseStart_4901986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4901989 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_4901989 : Nat := 118140960795 + 4901989 * 2 ^ 59
def prefixEnd_4901989 : Nat := 4983230072969 + 3 ^ 40 * 4901989 * 2
def baseEnd_4901989 : Nat := 2517076520052726679193669

theorem tailTrace_4901989 : CollatzResearch.WordTrace tailWord_4901989 prefixEnd_4901989 2517076520052726679193669 := by
  unfold tailWord_4901989
  simp only [CollatzResearch.WordTrace]
  refine ⟨178790227037938520913965021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119193484691959013942643347 178790227037938520913965021)
  ·
    refine ⟨67046335139226945342736883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178790227037938520913965021 67046335139226945342736883)
    ·
      refine ⟨100569502708840418014105325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67046335139226945342736883 100569502708840418014105325)
      ·
        refine ⟨37713563515815156755289497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100569502708840418014105325 37713563515815156755289497)
        ·
          refine ⟨28285172636861367566467123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37713563515815156755289497 28285172636861367566467123)
          ·
            refine ⟨42427758955292051349700685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28285172636861367566467123 42427758955292051349700685)
            ·
              refine ⟨15910409608234519256137757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42427758955292051349700685 15910409608234519256137757)
              ·
                refine ⟨5966403603087944721051659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15910409608234519256137757 5966403603087944721051659)
                ·
                  refine ⟨8949605404631917081577489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5966403603087944721051659 8949605404631917081577489)
                  ·
                    refine ⟨6712204053473937811183117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8949605404631917081577489 6712204053473937811183117)
                    ·
                      refine ⟨2517076520052726679193669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6712204053473937811183117 2517076520052726679193669)
                      ·
                        rfl

theorem cell23_4901989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_4901989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4901989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4901989 prefixEnd_4901989 := by exact prefixLift 4901989
  have htrace : WordTrace (prefixWord ++ tailWord_4901989) baseStart_4901989 baseEnd_4901989 := by
    simpa [prefixWord, tailWord_4901989, baseEnd_4901989] using wordTrace_append hprefix tailTrace_4901989
  have hstable : (prefixWord ++ tailWord_4901989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4901989).length < 2 ^ (prefixWord ++ tailWord_4901989).sum := by decide
  have hdescent : baseEnd_4901989 < baseStart_4901989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4901989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902015 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_4902015 : Nat := 118140960795 + 4902015 * 2 ^ 59
def prefixEnd_4902015 : Nat := 4983230072969 + 3 ^ 40 * 4902015 * 2
def baseEnd_4902015 : Nat := 2517089870549743577468549

theorem tailTrace_4902015 : CollatzResearch.WordTrace tailWord_4902015 prefixEnd_4902015 2517089870549743577468549 := by
  unfold tailWord_4902015
  simp only [CollatzResearch.WordTrace]
  refine ⟨178791175335844327354411499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119194116890562884902940999 178791175335844327354411499)
  ·
    refine ⟨268186763003766491031617249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178791175335844327354411499 268186763003766491031617249)
    ·
      refine ⟨201140072252824868273712937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268186763003766491031617249 201140072252824868273712937)
      ·
        refine ⟨150855054189618651205284703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201140072252824868273712937 150855054189618651205284703)
        ·
          refine ⟨226282581284427976807927055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150855054189618651205284703 226282581284427976807927055)
          ·
            refine ⟨339423871926641965211890583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226282581284427976807927055 339423871926641965211890583)
            ·
              refine ⟨509135807889962947817835875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339423871926641965211890583 509135807889962947817835875)
              ·
                refine ⟨763703711834944421726753813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509135807889962947817835875 763703711834944421726753813)
                ·
                  refine ⟨35798611492263019768441585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 763703711834944421726753813 35798611492263019768441585)
                  ·
                    refine ⟨26848958619197264826331189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35798611492263019768441585 26848958619197264826331189)
                    ·
                      refine ⟨2517089870549743577468549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26848958619197264826331189 2517089870549743577468549)
                      ·
                        rfl

theorem cell23_4902015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_4902015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902015 prefixEnd_4902015 := by exact prefixLift 4902015
  have htrace : WordTrace (prefixWord ++ tailWord_4902015) baseStart_4902015 baseEnd_4902015 := by
    simpa [prefixWord, tailWord_4902015, baseEnd_4902015] using wordTrace_append hprefix tailTrace_4902015
  have hstable : (prefixWord ++ tailWord_4902015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902015).length < 2 ^ (prefixWord ++ tailWord_4902015).sum := by decide
  have hdescent : baseEnd_4902015 < baseStart_4902015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902035 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 1, 8]
def baseStart_4902035 : Nat := 118140960795 + 4902035 * 2 ^ 59
def prefixEnd_4902035 : Nat := 4983230072969 + 3 ^ 40 * 4902035 * 2
def baseEnd_4902035 : Nat := 839033380054277833072819

theorem tailTrace_4902035 : CollatzResearch.WordTrace tailWord_4902035 prefixEnd_4902035 839033380054277833072819 := by
  unfold tailWord_4902035
  simp only [CollatzResearch.WordTrace]
  refine ⟨178791904795771870770139559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119194603197181247180093039 178791904795771870770139559)
  ·
    refine ⟨268187857193657806155209339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178791904795771870770139559 268187857193657806155209339)
    ·
      refine ⟨402281785790486709232814009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268187857193657806155209339 402281785790486709232814009)
      ·
        refine ⟨301711339342865031924610507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402281785790486709232814009 301711339342865031924610507)
        ·
          refine ⟨452567009014297547886915761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301711339342865031924610507 452567009014297547886915761)
          ·
            refine ⟨339425256760723160915186821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452567009014297547886915761 339425256760723160915186821)
            ·
              refine ⟨63642235642635592671597529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 339425256760723160915186821 63642235642635592671597529)
              ·
                refine ⟨47731676731976694503698147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63642235642635592671597529 47731676731976694503698147)
                ·
                  refine ⟨71597515097965041755547221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47731676731976694503698147 71597515097965041755547221)
                  ·
                    refine ⟨839033380054277833072819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71597515097965041755547221 839033380054277833072819)
                    ·
                      rfl

theorem cell23_4902035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 8].length) (baseStart_4902035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902035 prefixEnd_4902035 := by exact prefixLift 4902035
  have htrace : WordTrace (prefixWord ++ tailWord_4902035) baseStart_4902035 baseEnd_4902035 := by
    simpa [prefixWord, tailWord_4902035, baseEnd_4902035] using wordTrace_append hprefix tailTrace_4902035
  have hstable : (prefixWord ++ tailWord_4902035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902035).length < 2 ^ (prefixWord ++ tailWord_4902035).sum := by decide
  have hdescent : baseEnd_4902035 < baseStart_4902035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902080 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 1, 3, 2]
def baseStart_4902080 : Nat := 118140960795 + 4902080 * 2 ^ 59
def prefixEnd_4902080 : Nat := 4983230072969 + 3 ^ 40 * 4902080 * 2
def baseEnd_4902080 : Nat := 2517123246792285823155751

theorem tailTrace_4902080 : CollatzResearch.WordTrace tailWord_4902080 prefixEnd_4902080 2517123246792285823155751 := by
  unfold tailWord_4902080
  simp only [CollatzResearch.WordTrace]
  refine ⟨89396773040304421727763847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119195697387072562303685129 89396773040304421727763847)
  ·
    refine ⟨134095159560456632591645771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89396773040304421727763847 134095159560456632591645771)
    ·
      refine ⟨201142739340684948887468657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134095159560456632591645771 201142739340684948887468657)
      ·
        refine ⟨150857054505513711665601493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201142739340684948887468657 150857054505513711665601493)
        ·
          refine ⟨3535712214972977617162535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 150857054505513711665601493 3535712214972977617162535)
          ·
            refine ⟨5303568322459466425743803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535712214972977617162535 5303568322459466425743803)
            ·
              refine ⟨7955352483689199638615705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303568322459466425743803 7955352483689199638615705)
              ·
                refine ⟨5966514362766899728961779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7955352483689199638615705 5966514362766899728961779)
                ·
                  refine ⟨8949771544150349593442669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5966514362766899728961779 8949771544150349593442669)
                  ·
                    refine ⟨3356164329056381097541001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8949771544150349593442669 3356164329056381097541001)
                    ·
                      refine ⟨2517123246792285823155751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356164329056381097541001 2517123246792285823155751)
                      ·
                        rfl

theorem cell23_4902080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_4902080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902080 prefixEnd_4902080 := by exact prefixLift 4902080
  have htrace : WordTrace (prefixWord ++ tailWord_4902080) baseStart_4902080 baseEnd_4902080 := by
    simpa [prefixWord, tailWord_4902080, baseEnd_4902080] using wordTrace_append hprefix tailTrace_4902080
  have hstable : (prefixWord ++ tailWord_4902080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902080).length < 2 ^ (prefixWord ++ tailWord_4902080).sum := by decide
  have hdescent : baseEnd_4902080 < baseStart_4902080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902116 : List Nat := [2, 3, 1, 1, 1, 2, 6, 2, 5]
def baseStart_4902116 : Nat := 118140960795 + 4902116 * 2 ^ 59
def prefixEnd_4902116 : Nat := 4983230072969 + 3 ^ 40 * 4902116 * 2
def baseEnd_4902116 : Nat := 279682414677316409145065

theorem tailTrace_4902116 : CollatzResearch.WordTrace tailWord_4902116 prefixEnd_4902116 279682414677316409145065 := by
  unfold tailWord_4902116
  simp only [CollatzResearch.WordTrace]
  refine ⟨89397429554239210801919101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119196572738985614402558801 89397429554239210801919101)
  ·
    refine ⟨33524036082839704050719663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89397429554239210801919101 33524036082839704050719663)
    ·
      refine ⟨50286054124259556076079495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33524036082839704050719663 50286054124259556076079495)
      ·
        refine ⟨75429081186389334114119243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50286054124259556076079495 75429081186389334114119243)
        ·
          refine ⟨113143621779584001171178865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75429081186389334114119243 113143621779584001171178865)
          ·
            refine ⟨84857716334688000878384149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113143621779584001171178865 84857716334688000878384149)
            ·
              refine ⟨3977705453188500041174257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84857716334688000878384149 3977705453188500041174257)
              ·
                refine ⟨2983279089891375030880693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977705453188500041174257 2983279089891375030880693)
                ·
                  refine ⟨279682414677316409145065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2983279089891375030880693 279682414677316409145065)
                  ·
                    rfl

theorem cell23_4902116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_4902116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902116 prefixEnd_4902116 := by exact prefixLift 4902116
  have htrace : WordTrace (prefixWord ++ tailWord_4902116) baseStart_4902116 baseEnd_4902116 := by
    simpa [prefixWord, tailWord_4902116, baseEnd_4902116] using wordTrace_append hprefix tailTrace_4902116
  have hstable : (prefixWord ++ tailWord_4902116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902116).length < 2 ^ (prefixWord ++ tailWord_4902116).sum := by decide
  have hdescent : baseEnd_4902116 < baseStart_4902116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902146 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_4902146 : Nat := 118140960795 + 4902146 * 2 ^ 59
def prefixEnd_4902146 : Nat := 4983230072969 + 3 ^ 40 * 4902146 * 2
def baseEnd_4902146 : Nat := 839052378838494188310149

theorem tailTrace_4902146 : CollatzResearch.WordTrace tailWord_4902146 prefixEnd_4902146 839052378838494188310149 := by
  unfold tailWord_4902146
  simp only [CollatzResearch.WordTrace]
  refine ⟨44698988324592434181857573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119197302198913157818286861 44698988324592434181857573)
  ·
    refine ⟨8381060310861081409098295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44698988324592434181857573 8381060310861081409098295)
    ·
      refine ⟨12571590466291622113647443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8381060310861081409098295 12571590466291622113647443)
      ·
        refine ⟨18857385699437433170471165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12571590466291622113647443 18857385699437433170471165)
        ·
          refine ⟨7071519637289037438926687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18857385699437433170471165 7071519637289037438926687)
          ·
            refine ⟨10607279455933556158390031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7071519637289037438926687 10607279455933556158390031)
            ·
              refine ⟨15910919183900334237585047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10607279455933556158390031 15910919183900334237585047)
              ·
                refine ⟨23866378775850501356377571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15910919183900334237585047 23866378775850501356377571)
                ·
                  refine ⟨35799568163775752034566357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23866378775850501356377571 35799568163775752034566357)
                  ·
                    refine ⟨839052378838494188310149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35799568163775752034566357 839052378838494188310149)
                    ·
                      rfl

theorem cell23_4902146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_4902146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902146 prefixEnd_4902146 := by exact prefixLift 4902146
  have htrace : WordTrace (prefixWord ++ tailWord_4902146) baseStart_4902146 baseEnd_4902146 := by
    simpa [prefixWord, tailWord_4902146, baseEnd_4902146] using wordTrace_append hprefix tailTrace_4902146
  have hstable : (prefixWord ++ tailWord_4902146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902146).length < 2 ^ (prefixWord ++ tailWord_4902146).sum := by decide
  have hdescent : baseEnd_4902146 < baseStart_4902146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902149 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 1, 6, 2]
def baseStart_4902149 : Nat := 118140960795 + 4902149 * 2 ^ 59
def prefixEnd_4902149 : Nat := 4983230072969 + 3 ^ 40 * 4902149 * 2
def baseEnd_4902149 : Nat := 2517158676957446053192933

theorem tailTrace_4902149 : CollatzResearch.WordTrace tailWord_4902149 prefixEnd_4902149 2517158676957446053192933 := by
  unfold tailWord_4902149
  simp only [CollatzResearch.WordTrace]
  refine ⟨178796062717358868239789501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119197375144905912159859667 178796062717358868239789501)
  ·
    refine ⟨67048523519009575589921063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178796062717358868239789501 67048523519009575589921063)
    ·
      refine ⟨100572785278514363384881595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67048523519009575589921063 100572785278514363384881595)
      ·
        refine ⟨150859177917771545077322393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100572785278514363384881595 150859177917771545077322393)
        ·
          refine ⟨113144383438328658807991795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150859177917771545077322393 113144383438328658807991795)
          ·
            refine ⟨169716575157492988211987693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113144383438328658807991795 169716575157492988211987693)
            ·
              refine ⟨63643715684059870579495385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169716575157492988211987693 63643715684059870579495385)
              ·
                refine ⟨47732786763044902934621539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63643715684059870579495385 47732786763044902934621539)
                ·
                  refine ⟨71599180144567354401932309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47732786763044902934621539 71599180144567354401932309)
                  ·
                    refine ⟨3356211569276594737590577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71599180144567354401932309 3356211569276594737590577)
                    ·
                      refine ⟨2517158676957446053192933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356211569276594737590577 2517158676957446053192933)
                      ·
                        rfl

theorem cell23_4902149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_4902149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902149 prefixEnd_4902149 := by exact prefixLift 4902149
  have htrace : WordTrace (prefixWord ++ tailWord_4902149) baseStart_4902149 baseEnd_4902149 := by
    simpa [prefixWord, tailWord_4902149, baseEnd_4902149] using wordTrace_append hprefix tailTrace_4902149
  have hstable : (prefixWord ++ tailWord_4902149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902149).length < 2 ^ (prefixWord ++ tailWord_4902149).sum := by decide
  have hdescent : baseEnd_4902149 < baseStart_4902149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902186 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4902186 : Nat := 118140960795 + 4902186 * 2 ^ 59
def prefixEnd_4902186 : Nat := 4983230072969 + 3 ^ 40 * 4902186 * 2
def baseEnd_4902186 : Nat := 2517177675741662408430263

theorem tailTrace_4902186 : CollatzResearch.WordTrace tailWord_4902186 prefixEnd_4902186 2517177675741662408430263 := by
  unfold tailWord_4902186
  simp only [CollatzResearch.WordTrace]
  refine ⟨44699353054556205889721603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119198274812149882372590941 44699353054556205889721603)
  ·
    refine ⟨67049029581834308834582405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44699353054556205889721603 67049029581834308834582405)
    ·
      refine ⟨12571693046593932906484201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67049029581834308834582405 12571693046593932906484201)
      ·
        refine ⟨9428769784945449679863151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12571693046593932906484201 9428769784945449679863151)
        ·
          refine ⟨14143154677418174519794727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9428769784945449679863151 14143154677418174519794727)
          ·
            refine ⟨21214732016127261779692091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14143154677418174519794727 21214732016127261779692091)
            ·
              refine ⟨31822098024190892669538137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21214732016127261779692091 31822098024190892669538137)
              ·
                refine ⟨23866573518143169502153603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31822098024190892669538137 23866573518143169502153603)
                ·
                  refine ⟨35799860277214754253230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23866573518143169502153603 35799860277214754253230405)
                  ·
                    refine ⟨6712473801977766422480701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35799860277214754253230405 6712473801977766422480701)
                    ·
                      refine ⟨2517177675741662408430263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6712473801977766422480701 2517177675741662408430263)
                      ·
                        rfl

theorem cell23_4902186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4902186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902186 prefixEnd_4902186 := by exact prefixLift 4902186
  have htrace : WordTrace (prefixWord ++ tailWord_4902186) baseStart_4902186 baseEnd_4902186 := by
    simpa [prefixWord, tailWord_4902186, baseEnd_4902186] using wordTrace_append hprefix tailTrace_4902186
  have hstable : (prefixWord ++ tailWord_4902186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902186).length < 2 ^ (prefixWord ++ tailWord_4902186).sum := by decide
  have hdescent : baseEnd_4902186 < baseStart_4902186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902192 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_4902192 : Nat := 118140960795 + 4902192 * 2 ^ 59
def prefixEnd_4902192 : Nat := 4983230072969 + 3 ^ 40 * 4902192 * 2
def baseEnd_4902192 : Nat := 2517180756625589384955235

theorem tailTrace_4902192 : CollatzResearch.WordTrace tailWord_4902192 prefixEnd_4902192 2517180756625589384955235 := by
  unfold tailWord_4902192
  simp only [CollatzResearch.WordTrace]
  refine ⟨89398815528101543291802415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119198420704135391055736553 89398815528101543291802415)
  ·
    refine ⟨134098223292152314937703623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89398815528101543291802415 134098223292152314937703623)
    ·
      refine ⟨201147334938228472406555435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134098223292152314937703623 201147334938228472406555435)
      ·
        refine ⟨301721002407342708609833153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201147334938228472406555435 301721002407342708609833153)
        ·
          refine ⟨226290751805507031457374865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301721002407342708609833153 226290751805507031457374865)
          ·
            refine ⟨169718063854130273593031149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226290751805507031457374865 169718063854130273593031149)
            ·
              refine ⟨63644273945298852597386681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169718063854130273593031149 63644273945298852597386681)
              ·
                refine ⟨47733205458974139448040011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63644273945298852597386681 47733205458974139448040011)
                ·
                  refine ⟨71599808188461209172060017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47733205458974139448040011 71599808188461209172060017)
                  ·
                    refine ⟨53699856141345906879045013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71599808188461209172060017 53699856141345906879045013)
                    ·
                      refine ⟨2517180756625589384955235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53699856141345906879045013 2517180756625589384955235)
                      ·
                        rfl

theorem cell23_4902192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_4902192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902192 prefixEnd_4902192 := by exact prefixLift 4902192
  have htrace : WordTrace (prefixWord ++ tailWord_4902192) baseStart_4902192 baseEnd_4902192 := by
    simpa [prefixWord, tailWord_4902192, baseEnd_4902192] using wordTrace_append hprefix tailTrace_4902192
  have hstable : (prefixWord ++ tailWord_4902192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902192).length < 2 ^ (prefixWord ++ tailWord_4902192).sum := by decide
  have hdescent : baseEnd_4902192 < baseStart_4902192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902233 : List Nat := [1, 2, 1, 2, 2, 2, 2, 6, 1, 1, 3]
def baseStart_4902233 : Nat := 118140960795 + 4902233 * 2 ^ 59
def prefixEnd_4902233 : Nat := 4983230072969 + 3 ^ 40 * 4902233 * 2
def baseEnd_4902233 : Nat := 2517201809332423724542547

theorem tailTrace_4902233 : CollatzResearch.WordTrace tailWord_4902233 prefixEnd_4902233 2517201809332423724542547 := by
  unfold tailWord_4902233
  simp only [CollatzResearch.WordTrace]
  refine ⟨178799126449054550585847353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119199417632703033723898235 178799126449054550585847353)
  ·
    refine ⟨134099344836790912939385515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178799126449054550585847353 134099344836790912939385515)
    ·
      refine ⟨201149017255186369409078273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134099344836790912939385515 201149017255186369409078273)
      ·
        refine ⟨150861762941389777056808705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201149017255186369409078273 150861762941389777056808705)
        ·
          refine ⟨113146322206042332792606529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150861762941389777056808705 113146322206042332792606529)
          ·
            refine ⟨84859741654531749594454897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113146322206042332792606529 84859741654531749594454897)
            ·
              refine ⟨63644806240898812195841173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84859741654531749594454897 63644806240898812195841173)
              ·
                refine ⟨2983350292542131821680055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63644806240898812195841173 2983350292542131821680055)
                ·
                  refine ⟨4475025438813197732520083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983350292542131821680055 4475025438813197732520083)
                  ·
                    refine ⟨6712538158219796598780125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4475025438813197732520083 6712538158219796598780125)
                    ·
                      refine ⟨2517201809332423724542547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6712538158219796598780125 2517201809332423724542547)
                      ·
                        rfl

theorem cell23_4902233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_4902233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902233 prefixEnd_4902233 := by exact prefixLift 4902233
  have htrace : WordTrace (prefixWord ++ tailWord_4902233) baseStart_4902233 baseEnd_4902233 := by
    simpa [prefixWord, tailWord_4902233, baseEnd_4902233] using wordTrace_append hprefix tailTrace_4902233
  have hstable : (prefixWord ++ tailWord_4902233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902233).length < 2 ^ (prefixWord ++ tailWord_4902233).sum := by decide
  have hdescent : baseEnd_4902233 < baseStart_4902233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902239 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_4902239 : Nat := 118140960795 + 4902239 * 2 ^ 59
def prefixEnd_4902239 : Nat := 4983230072969 + 3 ^ 40 * 4902239 * 2
def baseEnd_4902239 : Nat := 2517204890216350701067519

theorem tailTrace_4902239 : CollatzResearch.WordTrace tailWord_4902239 prefixEnd_4902239 2517204890216350701067519 := by
  unfold tailWord_4902239
  simp only [CollatzResearch.WordTrace]
  refine ⟨178799345287032813610565771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119199563524688542407043847 178799345287032813610565771)
  ·
    refine ⟨268199017930549220415848657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178799345287032813610565771 268199017930549220415848657)
    ·
      refine ⟨201149263447911915311886493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268199017930549220415848657 201149263447911915311886493)
      ·
        refine ⟨75430973792966968241957435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201149263447911915311886493 75430973792966968241957435)
        ·
          refine ⟨113146460689450452362936153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75430973792966968241957435 113146460689450452362936153)
          ·
            refine ⟨84859845517087839272202115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113146460689450452362936153 84859845517087839272202115)
            ·
              refine ⟨127289768275631758908303173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84859845517087839272202115 127289768275631758908303173)
              ·
                refine ⟨23866831551680954795306845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127289768275631758908303173 23866831551680954795306845)
                ·
                  refine ⟨8950061831880358048240067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23866831551680954795306845 8950061831880358048240067)
                  ·
                    refine ⟨13425092747820537072360101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8950061831880358048240067 13425092747820537072360101)
                    ·
                      refine ⟨2517204890216350701067519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13425092747820537072360101 2517204890216350701067519)
                      ·
                        rfl

theorem cell23_4902239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_4902239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902239 prefixEnd_4902239 := by exact prefixLift 4902239
  have htrace : WordTrace (prefixWord ++ tailWord_4902239) baseStart_4902239 baseEnd_4902239 := by
    simpa [prefixWord, tailWord_4902239, baseEnd_4902239] using wordTrace_append hprefix tailTrace_4902239
  have hstable : (prefixWord ++ tailWord_4902239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902239).length < 2 ^ (prefixWord ++ tailWord_4902239).sum := by decide
  have hdescent : baseEnd_4902239 < baseStart_4902239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902249 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 6, 4]
def baseStart_4902249 : Nat := 118140960795 + 4902249 * 2 ^ 59
def prefixEnd_4902249 : Nat := 4983230072969 + 3 ^ 40 * 4902249 * 2
def baseEnd_4902249 : Nat := 839070008340965220647491

theorem tailTrace_4902249 : CollatzResearch.WordTrace tailWord_4902249 prefixEnd_4902249 839070008340965220647491 := by
  unfold tailWord_4902249
  simp only [CollatzResearch.WordTrace]
  refine ⟨178799710016996585318429801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119199806677997723545619867 178799710016996585318429801)
  ·
    refine ⟨134099782512747438988822351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178799710016996585318429801 134099782512747438988822351)
    ·
      refine ⟨201149673769121158483233527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134099782512747438988822351 201149673769121158483233527)
      ·
        refine ⟨301724510653681737724850291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201149673769121158483233527 301724510653681737724850291)
        ·
          refine ⟨452586765980522606587275437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301724510653681737724850291 452586765980522606587275437)
          ·
            refine ⟨169720037242695977470228289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 452586765980522606587275437 169720037242695977470228289)
            ·
              refine ⟨127290027932021983102671217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169720037242695977470228289 127290027932021983102671217)
              ·
                refine ⟨95467520949016487327003413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127290027932021983102671217 95467520949016487327003413)
                ·
                  refine ⟨4475040044485147843453285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95467520949016487327003413 4475040044485147843453285)
                  ·
                    refine ⟨839070008340965220647491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4475040044485147843453285 839070008340965220647491)
                    ·
                      rfl

theorem cell23_4902249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 4].length) (baseStart_4902249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902249 prefixEnd_4902249 := by exact prefixLift 4902249
  have htrace : WordTrace (prefixWord ++ tailWord_4902249) baseStart_4902249 baseEnd_4902249 := by
    simpa [prefixWord, tailWord_4902249, baseEnd_4902249] using wordTrace_append hprefix tailTrace_4902249
  have hstable : (prefixWord ++ tailWord_4902249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902249).length < 2 ^ (prefixWord ++ tailWord_4902249).sum := by decide
  have hdescent : baseEnd_4902249 < baseStart_4902249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902253 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_4902253 : Nat := 118140960795 + 4902253 * 2 ^ 59
def prefixEnd_4902253 : Nat := 4983230072969 + 3 ^ 40 * 4902253 * 2
def baseEnd_4902253 : Nat := 839070692981837882097485

theorem tailTrace_4902253 : CollatzResearch.WordTrace tailWord_4902253 prefixEnd_4902253 839070692981837882097485 := by
  unfold tailWord_4902253
  simp only [CollatzResearch.WordTrace]
  refine ⟨178799855908982094001575413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119199903939321396001050275 178799855908982094001575413)
  ·
    refine ⟨16762486491467071312647695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178799855908982094001575413 16762486491467071312647695)
    ·
      refine ⟨25143729737200606968971543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16762486491467071312647695 25143729737200606968971543)
      ·
        refine ⟨37715594605800910453457315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25143729737200606968971543 37715594605800910453457315)
        ·
          refine ⟨56573391908701365680185973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37715594605800910453457315 56573391908701365680185973)
          ·
            refine ⟨5303755491440753032517435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56573391908701365680185973 5303755491440753032517435)
            ·
              refine ⟨7955633237161129548776153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303755491440753032517435 7955633237161129548776153)
              ·
                refine ⟨5966724927870847161582115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7955633237161129548776153 5966724927870847161582115)
                ·
                  refine ⟨8950087391806270742373173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5966724927870847161582115 8950087391806270742373173)
                  ·
                    refine ⟨839070692981837882097485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8950087391806270742373173 839070692981837882097485)
                    ·
                      rfl

theorem cell23_4902253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_4902253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902253 prefixEnd_4902253 := by exact prefixLift 4902253
  have htrace : WordTrace (prefixWord ++ tailWord_4902253) baseStart_4902253 baseEnd_4902253 := by
    simpa [prefixWord, tailWord_4902253, baseEnd_4902253] using wordTrace_append hprefix tailTrace_4902253
  have hstable : (prefixWord ++ tailWord_4902253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902253).length < 2 ^ (prefixWord ++ tailWord_4902253).sum := by decide
  have hdescent : baseEnd_4902253 < baseStart_4902253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902276 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_4902276 : Nat := 118140960795 + 4902276 * 2 ^ 59
def prefixEnd_4902276 : Nat := 4983230072969 + 3 ^ 40 * 4902276 * 2
def baseEnd_4902276 : Nat := 2517223889000567056304849

theorem tailTrace_4902276 : CollatzResearch.WordTrace tailWord_4902276 prefixEnd_4902276 2517223889000567056304849 := by
  unfold tailWord_4902276
  simp only [CollatzResearch.WordTrace]
  refine ⟨89400347393949384464831341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119200463191932512619775121 89400347393949384464831341)
  ·
    refine ⟨33525130272731019174311753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89400347393949384464831341 33525130272731019174311753)
    ·
      refine ⟨25143847704548264380733815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33525130272731019174311753 25143847704548264380733815)
      ·
        refine ⟨37715771556822396571100723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25143847704548264380733815 37715771556822396571100723)
        ·
          refine ⟨56573657335233594856651085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37715771556822396571100723 56573657335233594856651085)
          ·
            refine ⟨21215121500712598071244157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56573657335233594856651085 21215121500712598071244157)
            ·
              refine ⟨7955670562767224276716559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21215121500712598071244157 7955670562767224276716559)
              ·
                refine ⟨11933505844150836415074839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7955670562767224276716559 11933505844150836415074839)
                ·
                  refine ⟨17900258766226254622612259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11933505844150836415074839 17900258766226254622612259)
                  ·
                    refine ⟨26850388149339381933918389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17900258766226254622612259 26850388149339381933918389)
                    ·
                      refine ⟨2517223889000567056304849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26850388149339381933918389 2517223889000567056304849)
                      ·
                        rfl

theorem cell23_4902276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_4902276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902276 prefixEnd_4902276 := by exact prefixLift 4902276
  have htrace : WordTrace (prefixWord ++ tailWord_4902276) baseStart_4902276 baseEnd_4902276 := by
    simpa [prefixWord, tailWord_4902276, baseEnd_4902276] using wordTrace_append hprefix tailTrace_4902276
  have hstable : (prefixWord ++ tailWord_4902276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902276).length < 2 ^ (prefixWord ++ tailWord_4902276).sum := by decide
  have hdescent : baseEnd_4902276 < baseStart_4902276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902339 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 2, 6]
def baseStart_4902339 : Nat := 118140960795 + 4902339 * 2 ^ 59
def prefixEnd_4902339 : Nat := 4983230072969 + 3 ^ 40 * 4902339 * 2
def baseEnd_4902339 : Nat := 839085412760600103272353

theorem tailTrace_4902339 : CollatzResearch.WordTrace tailWord_4902339 prefixEnd_4902339 839085412760600103272353 := by
  unfold tailWord_4902339
  simp only [CollatzResearch.WordTrace]
  refine ⟨178802992586670530689206071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119201995057780353792804047 178802992586670530689206071)
  ·
    refine ⟨268204488880005796033809107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178802992586670530689206071 268204488880005796033809107)
    ·
      refine ⟨402306733320008694050713661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268204488880005796033809107 402306733320008694050713661)
      ·
        refine ⟨150865024995003260269017623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 402306733320008694050713661 150865024995003260269017623)
        ·
          refine ⟨226297537492504890403526435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150865024995003260269017623 226297537492504890403526435)
          ·
            refine ⟨339446306238757335605289653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226297537492504890403526435 339446306238757335605289653)
            ·
              refine ⟨31823091209883500212995905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 339446306238757335605289653 31823091209883500212995905)
              ·
                refine ⟨23867318407412625159746929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31823091209883500212995905 23867318407412625159746929)
                ·
                  refine ⟨17900488805559468869810197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23867318407412625159746929 17900488805559468869810197)
                  ·
                    refine ⟨839085412760600103272353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17900488805559468869810197 839085412760600103272353)
                    ·
                      rfl

theorem cell23_4902339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 6].length) (baseStart_4902339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902339 prefixEnd_4902339 := by exact prefixLift 4902339
  have htrace : WordTrace (prefixWord ++ tailWord_4902339) baseStart_4902339 baseEnd_4902339 := by
    simpa [prefixWord, tailWord_4902339, baseEnd_4902339] using wordTrace_append hprefix tailTrace_4902339
  have hstable : (prefixWord ++ tailWord_4902339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902339).length < 2 ^ (prefixWord ++ tailWord_4902339).sum := by decide
  have hdescent : baseEnd_4902339 < baseStart_4902339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902340 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_4902340 : Nat := 118140960795 + 4902340 * 2 ^ 59
def prefixEnd_4902340 : Nat := 4983230072969 + 3 ^ 40 * 4902340 * 2
def baseEnd_4902340 : Nat := 2517256751762454805904555

theorem tailTrace_4902340 : CollatzResearch.WordTrace tailWord_4902340 prefixEnd_4902340 2517256751762454805904555 := by
  unfold tailWord_4902340
  simp only [CollatzResearch.WordTrace]
  refine ⟨89401514529833453929996237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119202019373111271906661649 89401514529833453929996237)
  ·
    refine ⟨33525567948687545223748589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89401514529833453929996237 33525567948687545223748589)
    ·
      refine ⟨12572087980757829458905721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33525567948687545223748589 12572087980757829458905721)
      ·
        refine ⟨9429065985568372094179291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12572087980757829458905721 9429065985568372094179291)
        ·
          refine ⟨14143598978352558141268937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9429065985568372094179291 14143598978352558141268937)
          ·
            refine ⟨10607699233764418605951703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14143598978352558141268937 10607699233764418605951703)
            ·
              refine ⟨15911548850646627908927555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10607699233764418605951703 15911548850646627908927555)
              ·
                refine ⟨23867323275969941863391333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15911548850646627908927555 23867323275969941863391333)
                ·
                  refine ⟨4475123114244364099385875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23867323275969941863391333 4475123114244364099385875)
                  ·
                    refine ⟨6712684671366546149078813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4475123114244364099385875 6712684671366546149078813)
                    ·
                      refine ⟨2517256751762454805904555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6712684671366546149078813 2517256751762454805904555)
                      ·
                        rfl

theorem cell23_4902340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_4902340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902340 prefixEnd_4902340 := by exact prefixLift 4902340
  have htrace : WordTrace (prefixWord ++ tailWord_4902340) baseStart_4902340 baseEnd_4902340 := by
    simpa [prefixWord, tailWord_4902340, baseEnd_4902340] using wordTrace_append hprefix tailTrace_4902340
  have hstable : (prefixWord ++ tailWord_4902340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902340).length < 2 ^ (prefixWord ++ tailWord_4902340).sum := by decide
  have hdescent : baseEnd_4902340 < baseStart_4902340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902396 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_4902396 : Nat := 118140960795 + 4902396 * 2 ^ 59
def prefixEnd_4902396 : Nat := 4983230072969 + 3 ^ 40 * 4902396 * 2
def baseEnd_4902396 : Nat := 2517285506679106586804297

theorem tailTrace_4902396 : CollatzResearch.WordTrace tailWord_4902396 prefixEnd_4902396 2517285506679106586804297 := by
  unfold tailWord_4902396
  simp only [CollatzResearch.WordTrace]
  refine ⟨89402535773732014712015521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119203381031642686282687361 89402535773732014712015521)
  ·
    refine ⟨67051901830299011034011641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89402535773732014712015521 67051901830299011034011641)
    ·
      refine ⟨50288926372724258275508731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67051901830299011034011641 50288926372724258275508731)
      ·
        refine ⟨75433389559086387413263097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50288926372724258275508731 75433389559086387413263097)
        ·
          refine ⟨56575042169314790559947323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75433389559086387413263097 56575042169314790559947323)
          ·
            refine ⟨84862563253972185839920985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56575042169314790559947323 84862563253972185839920985)
            ·
              refine ⟨63646922440479139379940739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84862563253972185839920985 63646922440479139379940739)
              ·
                refine ⟨95470383660718709069911109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63646922440479139379940739 95470383660718709069911109)
                ·
                  refine ⟨17900696936384757950608333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95470383660718709069911109 17900696936384757950608333)
                  ·
                    refine ⟨6712761351144284231478125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17900696936384757950608333 6712761351144284231478125)
                    ·
                      refine ⟨2517285506679106586804297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6712761351144284231478125 2517285506679106586804297)
                      ·
                        rfl

theorem cell23_4902396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_4902396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902396 prefixEnd_4902396 := by exact prefixLift 4902396
  have htrace : WordTrace (prefixWord ++ tailWord_4902396) baseStart_4902396 baseEnd_4902396 := by
    simpa [prefixWord, tailWord_4902396, baseEnd_4902396] using wordTrace_append hprefix tailTrace_4902396
  have hstable : (prefixWord ++ tailWord_4902396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902396).length < 2 ^ (prefixWord ++ tailWord_4902396).sum := by decide
  have hdescent : baseEnd_4902396 < baseStart_4902396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902399 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 3, 7]
def baseStart_4902399 : Nat := 118140960795 + 4902399 * 2 ^ 59
def prefixEnd_4902399 : Nat := 4983230072969 + 3 ^ 40 * 4902399 * 2
def baseEnd_4902399 : Nat := 839095682373690025022261

theorem tailTrace_4902399 : CollatzResearch.WordTrace tailWord_4902399 prefixEnd_4902399 839095682373690025022261 := by
  unfold tailWord_4902399
  simp only [CollatzResearch.WordTrace]
  refine ⟨178805180966453160936390251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119203453977635440624260167 178805180966453160936390251)
  ·
    refine ⟨268207771449679741404585377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178805180966453160936390251 268207771449679741404585377)
    ·
      refine ⟨201155828587259806053439033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268207771449679741404585377 201155828587259806053439033)
      ·
        refine ⟨150866871440444854540079275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201155828587259806053439033 150866871440444854540079275)
        ·
          refine ⟨226300307160667281810118913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150866871440444854540079275 226300307160667281810118913)
          ·
            refine ⟨169725230370500461357589185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226300307160667281810118913 169725230370500461357589185)
            ·
              refine ⟨127293922777875346018191889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169725230370500461357589185 127293922777875346018191889)
              ·
                refine ⟨95470442083406509513643917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127293922777875346018191889 95470442083406509513643917)
                ·
                  refine ⟨35801415781277441067616469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95470442083406509513643917 35801415781277441067616469)
                  ·
                    refine ⟨839095682373690025022261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35801415781277441067616469 839095682373690025022261)
                    ·
                      rfl

theorem cell23_4902399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_4902399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902399 prefixEnd_4902399 := by exact prefixLift 4902399
  have htrace : WordTrace (prefixWord ++ tailWord_4902399) baseStart_4902399 baseEnd_4902399 := by
    simpa [prefixWord, tailWord_4902399, baseEnd_4902399] using wordTrace_append hprefix tailTrace_4902399
  have hstable : (prefixWord ++ tailWord_4902399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902399).length < 2 ^ (prefixWord ++ tailWord_4902399).sum := by decide
  have hdescent : baseEnd_4902399 < baseStart_4902399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902433 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 2, 5]
def baseStart_4902433 : Nat := 118140960795 + 4902433 * 2 ^ 59
def prefixEnd_4902433 : Nat := 4983230072969 + 3 ^ 40 * 4902433 * 2
def baseEnd_4902433 : Nat := 839101501821107647347209

theorem tailTrace_4902433 : CollatzResearch.WordTrace tailWord_4902433 prefixEnd_4902433 839101501821107647347209 := by
  unfold tailWord_4902433
  simp only [CollatzResearch.WordTrace]
  refine ⟨178806421048329984743127953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119204280698886656495418635 178806421048329984743127953)
  ·
    refine ⟨134104815786247488557345965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178806421048329984743127953 134104815786247488557345965)
    ·
      refine ⟨50289305919842808209004737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134104815786247488557345965 50289305919842808209004737)
      ·
        refine ⟨37716979439882106156753553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50289305919842808209004737 37716979439882106156753553)
        ·
          refine ⟨28287734579911579617565165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37716979439882106156753553 28287734579911579617565165)
          ·
            refine ⟨10607900467466842356586937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28287734579911579617565165 10607900467466842356586937)
            ·
              refine ⟨7955925350600131767440203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10607900467466842356586937 7955925350600131767440203)
              ·
                refine ⟨11933888025900197651160305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7955925350600131767440203 11933888025900197651160305)
                ·
                  refine ⟨8950416019425148238370229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11933888025900197651160305 8950416019425148238370229)
                  ·
                    refine ⟨839101501821107647347209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8950416019425148238370229 839101501821107647347209)
                    ·
                      rfl

theorem cell23_4902433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_4902433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902433 prefixEnd_4902433 := by exact prefixLift 4902433
  have htrace : WordTrace (prefixWord ++ tailWord_4902433) baseStart_4902433 baseEnd_4902433 := by
    simpa [prefixWord, tailWord_4902433, baseEnd_4902433] using wordTrace_append hprefix tailTrace_4902433
  have hstable : (prefixWord ++ tailWord_4902433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902433).length < 2 ^ (prefixWord ++ tailWord_4902433).sum := by decide
  have hdescent : baseEnd_4902433 < baseStart_4902433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902453 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_4902453 : Nat := 118140960795 + 4902453 * 2 ^ 59
def prefixEnd_4902453 : Nat := 4983230072969 + 3 ^ 40 * 4902453 * 2
def baseEnd_4902453 : Nat := 2517314775076412863791535

theorem tailTrace_4902453 : CollatzResearch.WordTrace tailWord_4902453 prefixEnd_4902453 2517314775076412863791535 := by
  unfold tailWord_4902453
  simp only [CollatzResearch.WordTrace]
  refine ⟨178807150508257528158856013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119204767005505018772570675 178807150508257528158856013)
  ·
    refine ⟨67052681440596573059571005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178807150508257528158856013 67052681440596573059571005)
    ·
      refine ⟨25144755540223714897339127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67052681440596573059571005 25144755540223714897339127)
      ·
        refine ⟨37717133310335572346008691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25144755540223714897339127 37717133310335572346008691)
        ·
          refine ⟨56575699965503358519013037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37717133310335572346008691 56575699965503358519013037)
          ·
            refine ⟨21215887487063759444629889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56575699965503358519013037 21215887487063759444629889)
            ·
              refine ⟨15911915615297819583472417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21215887487063759444629889 15911915615297819583472417)
              ·
                refine ⟨11933936711473364687604313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15911915615297819583472417 11933936711473364687604313)
                ·
                  refine ⟨8950452533605023515703235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11933936711473364687604313 8950452533605023515703235)
                  ·
                    refine ⟨13425678800407535273554853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8950452533605023515703235 13425678800407535273554853)
                    ·
                      refine ⟨2517314775076412863791535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13425678800407535273554853 2517314775076412863791535)
                      ·
                        rfl

theorem cell23_4902453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_4902453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902453 prefixEnd_4902453 := by exact prefixLift 4902453
  have htrace : WordTrace (prefixWord ++ tailWord_4902453) baseStart_4902453 baseEnd_4902453 := by
    simpa [prefixWord, tailWord_4902453, baseEnd_4902453] using wordTrace_append hprefix tailTrace_4902453
  have hstable : (prefixWord ++ tailWord_4902453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902453).length < 2 ^ (prefixWord ++ tailWord_4902453).sum := by decide
  have hdescent : baseEnd_4902453 < baseStart_4902453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902454 : List Nat := [5, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_4902454 : Nat := 118140960795 + 4902454 * 2 ^ 59
def prefixEnd_4902454 : Nat := 4983230072969 + 3 ^ 40 * 4902454 * 2
def baseEnd_4902454 : Nat := 279701698728563039986559

theorem tailTrace_4902454 : CollatzResearch.WordTrace tailWord_4902454 prefixEnd_4902454 279701698728563039986559 := by
  unfold tailWord_4902454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11175449186328369083102651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119204791320835936886428277 11175449186328369083102651)
  ·
    refine ⟨16763173779492553624653977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11175449186328369083102651 16763173779492553624653977)
    ·
      refine ⟨12572380334619415218490483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16763173779492553624653977 12572380334619415218490483)
      ·
        refine ⟨18858570501929122827735725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12572380334619415218490483 18858570501929122827735725)
        ·
          refine ⟨7071963938223421060400897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18858570501929122827735725 7071963938223421060400897)
          ·
            refine ⟨5303972953667565795300673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7071963938223421060400897 5303972953667565795300673)
            ·
              refine ⟨3977979715250674346475505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303972953667565795300673 3977979715250674346475505)
              ·
                refine ⟨2983484786438005759856629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977979715250674346475505 2983484786438005759856629)
                ·
                  refine ⟨279701698728563039986559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2983484786438005759856629 279701698728563039986559)
                  ·
                    rfl

theorem cell23_4902454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_4902454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902454 prefixEnd_4902454 := by exact prefixLift 4902454
  have htrace : WordTrace (prefixWord ++ tailWord_4902454) baseStart_4902454 baseEnd_4902454 := by
    simpa [prefixWord, tailWord_4902454, baseEnd_4902454] using wordTrace_append hprefix tailTrace_4902454
  have hstable : (prefixWord ++ tailWord_4902454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902454).length < 2 ^ (prefixWord ++ tailWord_4902454).sum := by decide
  have hdescent : baseEnd_4902454 < baseStart_4902454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902560 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 4]
def baseStart_4902560 : Nat := 118140960795 + 4902560 * 2 ^ 59
def prefixEnd_4902560 : Nat := 4983230072969 + 3 ^ 40 * 4902560 * 2
def baseEnd_4902560 : Nat := 2517369717506443945153543

theorem tailTrace_4902560 : CollatzResearch.WordTrace tailWord_4902560 prefixEnd_4902560 2517369717506443945153543 := by
  unfold tailWord_4902560
  simp only [CollatzResearch.WordTrace]
  refine ⟨89405526559434942716500567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119207368745913256955334089 89405526559434942716500567)
  ·
    refine ⟨134108289839152414074750851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89405526559434942716500567 134108289839152414074750851)
    ·
      refine ⟨201162434758728621112126277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134108289839152414074750851 201162434758728621112126277)
      ·
        refine ⟨37717956517261616458523677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201162434758728621112126277 37717956517261616458523677)
        ·
          refine ⟨14144233693973106171946379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37717956517261616458523677 14144233693973106171946379)
          ·
            refine ⟨21216350540959659257919569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14144233693973106171946379 21216350540959659257919569)
            ·
              refine ⟨15912262905719744443439677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21216350540959659257919569 15912262905719744443439677)
              ·
                refine ⟨5967098589644904166289879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15912262905719744443439677 5967098589644904166289879)
                ·
                  refine ⟨8950647884467356249434819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5967098589644904166289879 8950647884467356249434819)
                  ·
                    refine ⟨13425971826701034374152229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8950647884467356249434819 13425971826701034374152229)
                    ·
                      refine ⟨2517369717506443945153543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13425971826701034374152229 2517369717506443945153543)
                      ·
                        rfl

theorem cell23_4902560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_4902560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902560 prefixEnd_4902560 := by exact prefixLift 4902560
  have htrace : WordTrace (prefixWord ++ tailWord_4902560) baseStart_4902560 baseEnd_4902560 := by
    simpa [prefixWord, tailWord_4902560, baseEnd_4902560] using wordTrace_append hprefix tailTrace_4902560
  have hstable : (prefixWord ++ tailWord_4902560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902560).length < 2 ^ (prefixWord ++ tailWord_4902560).sum := by decide
  have hdescent : baseEnd_4902560 < baseStart_4902560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902563 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 5]
def baseStart_4902563 : Nat := 118140960795 + 4902563 * 2 ^ 59
def prefixEnd_4902563 : Nat := 4983230072969 + 3 ^ 40 * 4902563 * 2
def baseEnd_4902563 : Nat := 2517371257948407433416029

theorem tailTrace_4902563 : CollatzResearch.WordTrace tailWord_4902563 prefixEnd_4902563 2517371257948407433416029 := by
  unfold tailWord_4902563
  simp only [CollatzResearch.WordTrace]
  refine ⟨178811162537859016945360343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119207441691906011296906895 178811162537859016945360343)
  ·
    refine ⟨268216743806788525418040515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178811162537859016945360343 268216743806788525418040515)
    ·
      refine ⟨402325115710182788127060773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268216743806788525418040515 402325115710182788127060773)
      ·
        refine ⟨75435959195659272773823895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 402325115710182788127060773 75435959195659272773823895)
        ·
          refine ⟨113153938793488909160735843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75435959195659272773823895 113153938793488909160735843)
          ·
            refine ⟨169730908190233363741103765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113153938793488909160735843 169730908190233363741103765)
            ·
              refine ⟨7956136321417188925364239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169730908190233363741103765 7956136321417188925364239)
              ·
                refine ⟨11934204482125783388046359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7956136321417188925364239 11934204482125783388046359)
                ·
                  refine ⟨17901306723188675082069539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11934204482125783388046359 17901306723188675082069539)
                  ·
                    refine ⟨26851960084783012623104309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17901306723188675082069539 26851960084783012623104309)
                    ·
                      refine ⟨2517371257948407433416029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26851960084783012623104309 2517371257948407433416029)
                      ·
                        rfl

theorem cell23_4902563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_4902563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902563 prefixEnd_4902563 := by exact prefixLift 4902563
  have htrace : WordTrace (prefixWord ++ tailWord_4902563) baseStart_4902563 baseEnd_4902563 := by
    simpa [prefixWord, tailWord_4902563, baseEnd_4902563] using wordTrace_append hprefix tailTrace_4902563
  have hstable : (prefixWord ++ tailWord_4902563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902563).length < 2 ^ (prefixWord ++ tailWord_4902563).sum := by decide
  have hdescent : baseEnd_4902563 < baseStart_4902563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902573 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_4902573 : Nat := 118140960795 + 4902573 * 2 ^ 59
def prefixEnd_4902573 : Nat := 4983230072969 + 3 ^ 40 * 4902573 * 2
def baseEnd_4902573 : Nat := 2517376392754952394290983

theorem tailTrace_4902573 : CollatzResearch.WordTrace tailWord_4902573 prefixEnd_4902573 2517376392754952394290983 := by
  unfold tailWord_4902573
  simp only [CollatzResearch.WordTrace]
  refine ⟨178811527267822788653224373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119207684845215192435482915 178811527267822788653224373)
  ·
    refine ⟨16763580681358386436239785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178811527267822788653224373 16763580681358386436239785)
    ·
      refine ⟨12572685511018789827179839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16763580681358386436239785 12572685511018789827179839)
      ·
        refine ⟨18859028266528184740769759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12572685511018789827179839 18859028266528184740769759)
        ·
          refine ⟨28288542399792277111154639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18859028266528184740769759 28288542399792277111154639)
          ·
            refine ⟨42432813599688415666731959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28288542399792277111154639 42432813599688415666731959)
            ·
              refine ⟨63649220399532623500097939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42432813599688415666731959 63649220399532623500097939)
              ·
                refine ⟨95473830599298935250146909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63649220399532623500097939 95473830599298935250146909)
                ·
                  refine ⟨35802686474737100718805091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95473830599298935250146909 35802686474737100718805091)
                  ·
                    refine ⟨53704029712105651078207637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35802686474737100718805091 53704029712105651078207637)
                    ·
                      refine ⟨2517376392754952394290983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53704029712105651078207637 2517376392754952394290983)
                      ·
                        rfl

theorem cell23_4902573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_4902573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902573 prefixEnd_4902573 := by exact prefixLift 4902573
  have htrace : WordTrace (prefixWord ++ tailWord_4902573) baseStart_4902573 baseEnd_4902573 := by
    simpa [prefixWord, tailWord_4902573, baseEnd_4902573] using wordTrace_append hprefix tailTrace_4902573
  have hstable : (prefixWord ++ tailWord_4902573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902573).length < 2 ^ (prefixWord ++ tailWord_4902573).sum := by decide
  have hdescent : baseEnd_4902573 < baseStart_4902573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902583 : List Nat := [1, 1, 3, 1, 5, 2, 2, 8]
def baseStart_4902583 : Nat := 118140960795 + 4902583 * 2 ^ 59
def prefixEnd_4902583 : Nat := 4983230072969 + 3 ^ 40 * 4902583 * 2
def baseEnd_4902583 : Nat := 93236352872648050191331

theorem tailTrace_4902583 : CollatzResearch.WordTrace tailWord_4902583 prefixEnd_4902583 93236352872648050191331 := by
  unfold tailWord_4902583
  simp only [CollatzResearch.WordTrace]
  refine ⟨178811891997786560361088403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119207927998524373574058935 178811891997786560361088403)
  ·
    refine ⟨268217837996679840541632605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178811891997786560361088403 268217837996679840541632605)
    ·
      refine ⟨100581689248754940203112227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268217837996679840541632605 100581689248754940203112227)
      ·
        refine ⟨150872533873132410304668341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100581689248754940203112227 150872533873132410304668341)
        ·
          refine ⟨14144300050606163466062657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150872533873132410304668341 14144300050606163466062657)
          ·
            refine ⟨10608225037954622599546993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14144300050606163466062657 10608225037954622599546993)
            ·
              refine ⟨7956168778465966949660245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10608225037954622599546993 7956168778465966949660245)
              ·
                refine ⟨93236352872648050191331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7956168778465966949660245 93236352872648050191331)
                ·
                  rfl

theorem cell23_4902583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 8].length) (baseStart_4902583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902583 prefixEnd_4902583 := by exact prefixLift 4902583
  have htrace : WordTrace (prefixWord ++ tailWord_4902583) baseStart_4902583 baseEnd_4902583 := by
    simpa [prefixWord, tailWord_4902583, baseEnd_4902583] using wordTrace_append hprefix tailTrace_4902583
  have hstable : (prefixWord ++ tailWord_4902583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902583).length < 2 ^ (prefixWord ++ tailWord_4902583).sum := by decide
  have hdescent : baseEnd_4902583 < baseStart_4902583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902610 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_4902610 : Nat := 118140960795 + 4902610 * 2 ^ 59
def prefixEnd_4902610 : Nat := 4983230072969 + 3 ^ 40 * 4902610 * 2
def baseEnd_4902610 : Nat := 2517395391539168749528313

theorem tailTrace_4902610 : CollatzResearch.WordTrace tailWord_4902610 prefixEnd_4902610 2517395391539168749528313 := by
  unfold tailWord_4902610
  simp only [CollatzResearch.WordTrace]
  refine ⟨44703219192172185993080321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119208584512459162648214189 44703219192172185993080321)
  ·
    refine ⟨33527414394129139494810241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44703219192172185993080321 33527414394129139494810241)
    ·
      refine ⟨25145560795596854621107681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33527414394129139494810241 25145560795596854621107681)
      ·
        refine ⟨18859170596697640965830761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25145560795596854621107681 18859170596697640965830761)
        ·
          refine ⟨14144377947523230724373071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18859170596697640965830761 14144377947523230724373071)
          ·
            refine ⟨21216566921284846086559607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14144377947523230724373071 21216566921284846086559607)
            ·
              refine ⟨31824850381927269129839411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21216566921284846086559607 31824850381927269129839411)
              ·
                refine ⟨47737275572890903694759117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31824850381927269129839411 47737275572890903694759117)
                ·
                  refine ⟨17901478339834088885534669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47737275572890903694759117 17901478339834088885534669)
                  ·
                    refine ⟨6713054377437783332075501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17901478339834088885534669 6713054377437783332075501)
                    ·
                      refine ⟨2517395391539168749528313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713054377437783332075501 2517395391539168749528313)
                      ·
                        rfl

theorem cell23_4902610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_4902610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902610 prefixEnd_4902610 := by exact prefixLift 4902610
  have htrace : WordTrace (prefixWord ++ tailWord_4902610) baseStart_4902610 baseEnd_4902610 := by
    simpa [prefixWord, tailWord_4902610, baseEnd_4902610] using wordTrace_append hprefix tailTrace_4902610
  have hstable : (prefixWord ++ tailWord_4902610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902610).length < 2 ^ (prefixWord ++ tailWord_4902610).sum := by decide
  have hdescent : baseEnd_4902610 < baseStart_4902610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902637 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_4902637 : Nat := 118140960795 + 4902637 * 2 ^ 59
def prefixEnd_4902637 : Nat := 4983230072969 + 3 ^ 40 * 4902637 * 2
def baseEnd_4902637 : Nat := 2517409255516840143890689

theorem tailTrace_4902637 : CollatzResearch.WordTrace tailWord_4902637 prefixEnd_4902637 2517409255516840143890689 := by
  unfold tailWord_4902637
  simp only [CollatzResearch.WordTrace]
  refine ⟨178813861539590927583554165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119209241026393951722369443 178813861539590927583554165)
  ·
    refine ⟨16763799519336649460958203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178813861539590927583554165 16763799519336649460958203)
    ·
      refine ⟨25145699279004974191437305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16763799519336649460958203 25145699279004974191437305)
      ·
        refine ⟨18859274459253730643577979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25145699279004974191437305 18859274459253730643577979)
        ·
          refine ⟨28288911688880595965366969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18859274459253730643577979 28288911688880595965366969)
          ·
            refine ⟨21216683766660446974025227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28288911688880595965366969 21216683766660446974025227)
            ·
              refine ⟨31825025649990670461037841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21216683766660446974025227 31825025649990670461037841)
              ·
                refine ⟨23868769237493002845778381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31825025649990670461037841 23868769237493002845778381)
                ·
                  refine ⟨8950788464059876067166893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23868769237493002845778381 8950788464059876067166893)
                  ·
                    refine ⟨3356545674022453525187585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8950788464059876067166893 3356545674022453525187585)
                    ·
                      refine ⟨2517409255516840143890689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356545674022453525187585 2517409255516840143890689)
                      ·
                        rfl

theorem cell23_4902637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_4902637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902637 prefixEnd_4902637 := by exact prefixLift 4902637
  have htrace : WordTrace (prefixWord ++ tailWord_4902637) baseStart_4902637 baseEnd_4902637 := by
    simpa [prefixWord, tailWord_4902637, baseEnd_4902637] using wordTrace_append hprefix tailTrace_4902637
  have hstable : (prefixWord ++ tailWord_4902637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902637).length < 2 ^ (prefixWord ++ tailWord_4902637).sum := by decide
  have hdescent : baseEnd_4902637 < baseStart_4902637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902644 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4902644 : Nat := 118140960795 + 4902644 * 2 ^ 59
def prefixEnd_4902644 : Nat := 4983230072969 + 3 ^ 40 * 4902644 * 2
def baseEnd_4902644 : Nat := 2517412849881421616503157

theorem tailTrace_4902644 : CollatzResearch.WordTrace tailWord_4902644 prefixEnd_4902644 2517412849881421616503157 := by
  unfold tailWord_4902644
  simp only [CollatzResearch.WordTrace]
  refine ⟨89407058425282783889529493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119209411233710378519372657 89407058425282783889529493)
  ·
    refine ⟨4190955863685130494821695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89407058425282783889529493 4190955863685130494821695)
    ·
      refine ⟨6286433795527695742232543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4190955863685130494821695 6286433795527695742232543)
      ·
        refine ⟨9429650693291543613348815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6286433795527695742232543 9429650693291543613348815)
        ·
          refine ⟨14144476039937315420023223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9429650693291543613348815 14144476039937315420023223)
          ·
            refine ⟨21216714059905973130034835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14144476039937315420023223 21216714059905973130034835)
            ·
              refine ⟨31825071089858959695052253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21216714059905973130034835 31825071089858959695052253)
              ·
                refine ⟨11934401658697109885644595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31825071089858959695052253 11934401658697109885644595)
                ·
                  refine ⟨17901602488045664828466893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11934401658697109885644595 17901602488045664828466893)
                  ·
                    refine ⟨6713100933017124310675085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17901602488045664828466893 6713100933017124310675085)
                    ·
                      refine ⟨2517412849881421616503157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713100933017124310675085 2517412849881421616503157)
                      ·
                        rfl

theorem cell23_4902644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4902644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902644 prefixEnd_4902644 := by exact prefixLift 4902644
  have htrace : WordTrace (prefixWord ++ tailWord_4902644) baseStart_4902644 baseEnd_4902644 := by
    simpa [prefixWord, tailWord_4902644, baseEnd_4902644] using wordTrace_append hprefix tailTrace_4902644
  have hstable : (prefixWord ++ tailWord_4902644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902644).length < 2 ^ (prefixWord ++ tailWord_4902644).sum := by decide
  have hdescent : baseEnd_4902644 < baseStart_4902644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902653 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_4902653 : Nat := 118140960795 + 4902653 * 2 ^ 59
def prefixEnd_4902653 : Nat := 4983230072969 + 3 ^ 40 * 4902653 * 2
def baseEnd_4902653 : Nat := 2517417471207312081290615

theorem tailTrace_4902653 : CollatzResearch.WordTrace tailWord_4902653 prefixEnd_4902653 2517417471207312081290615 := by
  unfold tailWord_4902653
  simp only [CollatzResearch.WordTrace]
  refine ⟨178814445107532962316136613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119209630071688641544091075 178814445107532962316136613)
  ·
    refine ⟨33527708457662430434275615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178814445107532962316136613 33527708457662430434275615)
    ·
      refine ⟨50291562686493645651413423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33527708457662430434275615 50291562686493645651413423)
      ·
        refine ⟨75437344029740468477120135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50291562686493645651413423 75437344029740468477120135)
        ·
          refine ⟨113156016044610702715680203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75437344029740468477120135 113156016044610702715680203)
          ·
            refine ⟨169734024066916054073520305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113156016044610702715680203 169734024066916054073520305)
            ·
              refine ⟨127300518050187040555140229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169734024066916054073520305 127300518050187040555140229)
              ·
                refine ⟨23868847134410070104088793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127300518050187040555140229 23868847134410070104088793)
                ·
                  refine ⟨17901635350807552578066595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23868847134410070104088793 17901635350807552578066595)
                  ·
                    refine ⟨26852453026211328867099893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17901635350807552578066595 26852453026211328867099893)
                    ·
                      refine ⟨2517417471207312081290615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26852453026211328867099893 2517417471207312081290615)
                      ·
                        rfl

theorem cell23_4902653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_4902653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902653 prefixEnd_4902653 := by exact prefixLift 4902653
  have htrace : WordTrace (prefixWord ++ tailWord_4902653) baseStart_4902653 baseEnd_4902653 := by
    simpa [prefixWord, tailWord_4902653, baseEnd_4902653] using wordTrace_append hprefix tailTrace_4902653
  have hstable : (prefixWord ++ tailWord_4902653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902653).length < 2 ^ (prefixWord ++ tailWord_4902653).sum := by decide
  have hdescent : baseEnd_4902653 < baseStart_4902653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902662 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4902662 : Nat := 118140960795 + 4902662 * 2 ^ 59
def prefixEnd_4902662 : Nat := 4983230072969 + 3 ^ 40 * 4902662 * 2
def baseEnd_4902662 : Nat := 2517422092533202546078075

theorem tailTrace_4902662 : CollatzResearch.WordTrace tailWord_4902662 prefixEnd_4902662 2517422092533202546078075 := by
  unfold tailWord_4902662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587961667640636151662945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 119209848909666904568809493 5587961667640636151662945)
  ·
    refine ⟨4190971250730477113747209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5587961667640636151662945 4190971250730477113747209)
    ·
      refine ⟨3143228438047857835310407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4190971250730477113747209 3143228438047857835310407)
      ·
        refine ⟨4714842657071786752965611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3143228438047857835310407 4714842657071786752965611)
        ·
          refine ⟨7072263985607680129448417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4714842657071786752965611 7072263985607680129448417)
          ·
            refine ⟨5304197989205760097086313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7072263985607680129448417 5304197989205760097086313)
            ·
              refine ⟨3978148491904320072814735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5304197989205760097086313 3978148491904320072814735)
              ·
                refine ⟨5967222737856480109222103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978148491904320072814735 5967222737856480109222103)
                ·
                  refine ⟨8950834106784720163833155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5967222737856480109222103 8950834106784720163833155)
                  ·
                    refine ⟨13426251160177080245749733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8950834106784720163833155 13426251160177080245749733)
                    ·
                      refine ⟨2517422092533202546078075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13426251160177080245749733 2517422092533202546078075)
                      ·
                        rfl

theorem cell23_4902662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4902662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902662 prefixEnd_4902662 := by exact prefixLift 4902662
  have htrace : WordTrace (prefixWord ++ tailWord_4902662) baseStart_4902662 baseEnd_4902662 := by
    simpa [prefixWord, tailWord_4902662, baseEnd_4902662] using wordTrace_append hprefix tailTrace_4902662
  have hstable : (prefixWord ++ tailWord_4902662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902662).length < 2 ^ (prefixWord ++ tailWord_4902662).sum := by decide
  have hdescent : baseEnd_4902662 < baseStart_4902662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902683 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 3]
def baseStart_4902683 : Nat := 118140960795 + 4902683 * 2 ^ 59
def prefixEnd_4902683 : Nat := 4983230072969 + 3 ^ 40 * 4902683 * 2
def baseEnd_4902683 : Nat := 2517432875626946963915477

theorem tailTrace_4902683 : CollatzResearch.WordTrace tailWord_4902683 prefixEnd_4902683 2517432875626946963915477 := by
  unfold tailWord_4902683
  simp only [CollatzResearch.WordTrace]
  refine ⟨178815539297424277439728703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119210359531616184959819135 178815539297424277439728703)
  ·
    refine ⟨268223308946136416159593055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178815539297424277439728703 268223308946136416159593055)
    ·
      refine ⟨402334963419204624239389583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268223308946136416159593055 402334963419204624239389583)
      ·
        refine ⟨603502445128806936359084375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402334963419204624239389583 603502445128806936359084375)
        ·
          refine ⟨905253667693210404538626563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603502445128806936359084375 905253667693210404538626563)
          ·
            refine ⟨1357880501539815606807939845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905253667693210404538626563 1357880501539815606807939845)
            ·
              refine ⟨254602594038715426276488721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1357880501539815606807939845 254602594038715426276488721)
              ·
                refine ⟨190951945529036569707366541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254602594038715426276488721 190951945529036569707366541)
                ·
                  refine ⟨71606979573388713640262453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190951945529036569707366541 71606979573388713640262453)
                  ·
                    refine ⟨6713154335005191903774605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71606979573388713640262453 6713154335005191903774605)
                    ·
                      refine ⟨2517432875626946963915477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713154335005191903774605 2517432875626946963915477)
                      ·
                        rfl

theorem cell23_4902683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 3].length) (baseStart_4902683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902683 prefixEnd_4902683 := by exact prefixLift 4902683
  have htrace : WordTrace (prefixWord ++ tailWord_4902683) baseStart_4902683 baseEnd_4902683 := by
    simpa [prefixWord, tailWord_4902683, baseEnd_4902683] using wordTrace_append hprefix tailTrace_4902683
  have hstable : (prefixWord ++ tailWord_4902683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902683).length < 2 ^ (prefixWord ++ tailWord_4902683).sum := by decide
  have hdescent : baseEnd_4902683 < baseStart_4902683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902690 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 7]
def baseStart_4902690 : Nat := 118140960795 + 4902690 * 2 ^ 59
def prefixEnd_4902690 : Nat := 4983230072969 + 3 ^ 40 * 4902690 * 2
def baseEnd_4902690 : Nat := 279715163332392048503105

theorem tailTrace_4902690 : CollatzResearch.WordTrace tailWord_4902690 prefixEnd_4902690 279715163332392048503105 := by
  unfold tailWord_4902690
  simp only [CollatzResearch.WordTrace]
  refine ⟨44703948652099729408808381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119210529738932611756822349 44703948652099729408808381)
  ·
    refine ⟨16763980744537398528303143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44703948652099729408808381 16763980744537398528303143)
    ·
      refine ⟨25145971116806097792454715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16763980744537398528303143 25145971116806097792454715)
      ·
        refine ⟨37718956675209146688682073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25145971116806097792454715 37718956675209146688682073)
        ·
          refine ⟨28289217506406860016511555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37718956675209146688682073 28289217506406860016511555)
          ·
            refine ⟨42433826259610290024767333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28289217506406860016511555 42433826259610290024767333)
            ·
              refine ⟨7956342423676929379643875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42433826259610290024767333 7956342423676929379643875)
              ·
                refine ⟨11934513635515394069465813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7956342423676929379643875 11934513635515394069465813)
                ·
                  refine ⟨279715163332392048503105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11934513635515394069465813 279715163332392048503105)
                  ·
                    rfl

theorem cell23_4902690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_4902690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902690 prefixEnd_4902690 := by exact prefixLift 4902690
  have htrace : WordTrace (prefixWord ++ tailWord_4902690) baseStart_4902690 baseEnd_4902690 := by
    simpa [prefixWord, tailWord_4902690, baseEnd_4902690] using wordTrace_append hprefix tailTrace_4902690
  have hstable : (prefixWord ++ tailWord_4902690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902690).length < 2 ^ (prefixWord ++ tailWord_4902690).sum := by decide
  have hdescent : baseEnd_4902690 < baseStart_4902690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902700 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_4902700 : Nat := 118140960795 + 4902700 * 2 ^ 59
def prefixEnd_4902700 : Nat := 4983230072969 + 3 ^ 40 * 4902700 * 2
def baseEnd_4902700 : Nat := 2517441604798073397402899

theorem tailTrace_4902700 : CollatzResearch.WordTrace tailWord_4902700 prefixEnd_4902700 2517441604798073397402899 := by
  unfold tailWord_4902700
  simp only [CollatzResearch.WordTrace]
  refine ⟨89408079669181344671548777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119210772892241792895398369 89408079669181344671548777)
  ·
    refine ⟨67056059751886008503661583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89408079669181344671548777 67056059751886008503661583)
    ·
      refine ⟨100584089627829012755492375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67056059751886008503661583 100584089627829012755492375)
      ·
        refine ⟨150876134441743519133238563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100584089627829012755492375 150876134441743519133238563)
        ·
          refine ⟨226314201662615278699857845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150876134441743519133238563 226314201662615278699857845)
          ·
            refine ⟨21216956405870182378111673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 226314201662615278699857845 21216956405870182378111673)
            ·
              refine ⟨15912717304402636783583755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21216956405870182378111673 15912717304402636783583755)
              ·
                refine ⟨23869075956603955175375633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15912717304402636783583755 23869075956603955175375633)
                ·
                  refine ⟨17901806967452966381531725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23869075956603955175375633 17901806967452966381531725)
                  ·
                    refine ⟨6713177612794862393074397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17901806967452966381531725 6713177612794862393074397)
                    ·
                      refine ⟨2517441604798073397402899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713177612794862393074397 2517441604798073397402899)
                      ·
                        rfl

theorem cell23_4902700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_4902700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902700 prefixEnd_4902700 := by exact prefixLift 4902700
  have htrace : WordTrace (prefixWord ++ tailWord_4902700) baseStart_4902700 baseEnd_4902700 := by
    simpa [prefixWord, tailWord_4902700, baseEnd_4902700] using wordTrace_append hprefix tailTrace_4902700
  have hstable : (prefixWord ++ tailWord_4902700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902700).length < 2 ^ (prefixWord ++ tailWord_4902700).sum := by decide
  have hdescent : baseEnd_4902700 < baseStart_4902700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902703 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 4, 5]
def baseStart_4902703 : Nat := 118140960795 + 4902703 * 2 ^ 59
def prefixEnd_4902703 : Nat := 4983230072969 + 3 ^ 40 * 4902703 * 2
def baseEnd_4902703 : Nat := 839147715080012295221795

theorem tailTrace_4902703 : CollatzResearch.WordTrace tailWord_4902703 prefixEnd_4902703 839147715080012295221795 := by
  unfold tailWord_4902703
  simp only [CollatzResearch.WordTrace]
  refine ⟨178816268757351820855456763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119210845838234547236971175 178816268757351820855456763)
  ·
    refine ⟨268224403136027731283185145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178816268757351820855456763 268224403136027731283185145)
    ·
      refine ⟨201168302352020798462388859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268224403136027731283185145 201168302352020798462388859)
      ·
        refine ⟨301752453528031197693583289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201168302352020798462388859 301752453528031197693583289)
        ·
          refine ⟨226314340146023398270187467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301752453528031197693583289 226314340146023398270187467)
          ·
            refine ⟨339471510219035097405281201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226314340146023398270187467 339471510219035097405281201)
            ·
              refine ⟨254603632664276323053960901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339471510219035097405281201 254603632664276323053960901)
              ·
                refine ⟨47738181124551810572617669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254603632664276323053960901 47738181124551810572617669)
                ·
                  refine ⟨8950908960853464482365813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47738181124551810572617669 8950908960853464482365813)
                  ·
                    refine ⟨839147715080012295221795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8950908960853464482365813 839147715080012295221795)
                    ·
                      rfl

theorem cell23_4902703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_4902703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902703 prefixEnd_4902703 := by exact prefixLift 4902703
  have htrace : WordTrace (prefixWord ++ tailWord_4902703) baseStart_4902703 baseEnd_4902703 := by
    simpa [prefixWord, tailWord_4902703, baseEnd_4902703] using wordTrace_append hprefix tailTrace_4902703
  have hstable : (prefixWord ++ tailWord_4902703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902703).length < 2 ^ (prefixWord ++ tailWord_4902703).sum := by decide
  have hdescent : baseEnd_4902703 < baseStart_4902703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902777 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 3]
def baseStart_4902777 : Nat := 118140960795 + 4902777 * 2 ^ 59
def prefixEnd_4902777 : Nat := 4983230072969 + 3 ^ 40 * 4902777 * 2
def baseEnd_4902777 : Nat := 2517481142808469596140045

theorem tailTrace_4902777 : CollatzResearch.WordTrace tailWord_4902777 prefixEnd_4902777 2517481142808469596140045 := by
  unfold tailWord_4902777
  simp only [CollatzResearch.WordTrace]
  refine ⟨178818967759083731493650585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119212645172722487662433723 178818967759083731493650585)
  ·
    refine ⟨134114225819312798620237939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178818967759083731493650585 134114225819312798620237939)
    ·
      refine ⟨201171338728969197930356909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134114225819312798620237939 201171338728969197930356909)
      ·
        refine ⟨75439252023363449223883841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201171338728969197930356909 75439252023363449223883841)
        ·
          refine ⟨56579439017522586917912881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75439252023363449223883841 56579439017522586917912881)
          ·
            refine ⟨42434579263141940188434661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56579439017522586917912881 42434579263141940188434661)
            ·
              refine ⟨7956483611839113785331499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42434579263141940188434661 7956483611839113785331499)
              ·
                refine ⟨11934725417758670677997249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7956483611839113785331499 11934725417758670677997249)
                ·
                  refine ⟨8951044063319003008497937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11934725417758670677997249 8951044063319003008497937)
                  ·
                    refine ⟨6713283047489252256373453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8951044063319003008497937 6713283047489252256373453)
                    ·
                      refine ⟨2517481142808469596140045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713283047489252256373453 2517481142808469596140045)
                      ·
                        rfl

theorem cell23_4902777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_4902777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902777 prefixEnd_4902777 := by exact prefixLift 4902777
  have htrace : WordTrace (prefixWord ++ tailWord_4902777) baseStart_4902777 baseEnd_4902777 := by
    simpa [prefixWord, tailWord_4902777, baseEnd_4902777] using wordTrace_append hprefix tailTrace_4902777
  have hstable : (prefixWord ++ tailWord_4902777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902777).length < 2 ^ (prefixWord ++ tailWord_4902777).sum := by decide
  have hdescent : baseEnd_4902777 < baseStart_4902777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902783 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_4902783 : Nat := 118140960795 + 4902783 * 2 ^ 59
def prefixEnd_4902783 : Nat := 4983230072969 + 3 ^ 40 * 4902783 * 2
def baseEnd_4902783 : Nat := 2517484223692396572665017

theorem tailTrace_4902783 : CollatzResearch.WordTrace tailWord_4902783 prefixEnd_4902783 2517484223692396572665017 := by
  unfold tailWord_4902783
  simp only [CollatzResearch.WordTrace]
  refine ⟨178819186597061994518369003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119212791064707996345579335 178819186597061994518369003)
  ·
    refine ⟨268228779895592991777553505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178819186597061994518369003 268228779895592991777553505)
    ·
      refine ⟨201171584921694743833165129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268228779895592991777553505 201171584921694743833165129)
      ·
        refine ⟨150878688691271057874873847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201171584921694743833165129 150878688691271057874873847)
        ·
          refine ⟨226318033036906586812310771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150878688691271057874873847 226318033036906586812310771)
          ·
            refine ⟨339477049555359880218466157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226318033036906586812310771 339477049555359880218466157)
            ·
              refine ⟨127303893583259955081924809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339477049555359880218466157 127303893583259955081924809)
              ·
                refine ⟨95477920187444966311443607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127303893583259955081924809 95477920187444966311443607)
                ·
                  refine ⟨143216880281167449467165411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95477920187444966311443607 143216880281167449467165411)
                  ·
                    refine ⟨214825320421751174200748117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 143216880281167449467165411 214825320421751174200748117)
                    ·
                      refine ⟨2517484223692396572665017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 214825320421751174200748117 2517484223692396572665017)
                      ·
                        rfl

theorem cell23_4902783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_4902783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902783 prefixEnd_4902783 := by exact prefixLift 4902783
  have htrace : WordTrace (prefixWord ++ tailWord_4902783) baseStart_4902783 baseEnd_4902783 := by
    simpa [prefixWord, tailWord_4902783, baseEnd_4902783] using wordTrace_append hprefix tailTrace_4902783
  have hstable : (prefixWord ++ tailWord_4902783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902783).length < 2 ^ (prefixWord ++ tailWord_4902783).sum := by decide
  have hdescent : baseEnd_4902783 < baseStart_4902783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902840 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 1, 6]
def baseStart_4902840 : Nat := 118140960795 + 4902840 * 2 ^ 59
def prefixEnd_4902840 : Nat := 4983230072969 + 3 ^ 40 * 4902840 * 2
def baseEnd_4902840 : Nat := 839171164029900949884085

theorem tailTrace_4902840 : CollatzResearch.WordTrace tailWord_4902840 prefixEnd_4902840 839171164029900949884085 := by
  unfold tailWord_4902840
  simp only [CollatzResearch.WordTrace]
  refine ⟨89410632778927746626596987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119214177038570328835462649 89410632778927746626596987)
  ·
    refine ⟨134115949168391619939895481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89410632778927746626596987 134115949168391619939895481)
    ·
      refine ⟨100586961876293714954921611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134115949168391619939895481 100586961876293714954921611)
      ·
        refine ⟨150880442814440572432382417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100586961876293714954921611 150880442814440572432382417)
        ·
          refine ⟨113160332110830429324286813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150880442814440572432382417 113160332110830429324286813)
          ·
            refine ⟨42435124541561410996607555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113160332110830429324286813 42435124541561410996607555)
            ·
              refine ⟨63652686812342116494911333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42435124541561410996607555 63652686812342116494911333)
              ·
                refine ⟨11934878777314146842795875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63652686812342116494911333 11934878777314146842795875)
                ·
                  refine ⟨17902318165971220264193813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11934878777314146842795875 17902318165971220264193813)
                  ·
                    refine ⟨839171164029900949884085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17902318165971220264193813 839171164029900949884085)
                    ·
                      rfl

theorem cell23_4902840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_4902840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902840 prefixEnd_4902840 := by exact prefixLift 4902840
  have htrace : WordTrace (prefixWord ++ tailWord_4902840) baseStart_4902840 baseEnd_4902840 := by
    simpa [prefixWord, tailWord_4902840, baseEnd_4902840] using wordTrace_append hprefix tailTrace_4902840
  have hstable : (prefixWord ++ tailWord_4902840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902840).length < 2 ^ (prefixWord ++ tailWord_4902840).sum := by decide
  have hdescent : baseEnd_4902840 < baseStart_4902840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902841 : List Nat := [1, 2, 1, 4, 2, 1, 4, 3, 1, 1, 3]
def baseStart_4902841 : Nat := 118140960795 + 4902841 * 2 ^ 59
def prefixEnd_4902841 : Nat := 4983230072969 + 3 ^ 40 * 4902841 * 2
def baseEnd_4902841 : Nat := 2517514005570357345739751

theorem tailTrace_4902841 : CollatzResearch.WordTrace tailWord_4902841 prefixEnd_4902841 2517514005570357345739751 := by
  unfold tailWord_4902841
  simp only [CollatzResearch.WordTrace]
  refine ⟨178821302030851870423980377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119214201353901246949320251 178821302030851870423980377)
  ·
    refine ⟨134115976523138902817985283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178821302030851870423980377 134115976523138902817985283)
    ·
      refine ⟨201173964784708354226977925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134115976523138902817985283 201173964784708354226977925)
      ·
        refine ⟨37720118397132816417558361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201173964784708354226977925 37720118397132816417558361)
        ·
          refine ⟨28290088797849612313168771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37720118397132816417558361 28290088797849612313168771)
          ·
            refine ⟨42435133196774418469753157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28290088797849612313168771 42435133196774418469753157)
            ·
              refine ⟨7956587474395203463078717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42435133196774418469753157 7956587474395203463078717)
              ·
                refine ⟨2983720302898201298654519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7956587474395203463078717 2983720302898201298654519)
                ·
                  refine ⟨4475580454347301947981779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983720302898201298654519 4475580454347301947981779)
                  ·
                    refine ⟨6713370681520952921972669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4475580454347301947981779 6713370681520952921972669)
                    ·
                      refine ⟨2517514005570357345739751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713370681520952921972669 2517514005570357345739751)
                      ·
                        rfl

theorem cell23_4902841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_4902841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902841 prefixEnd_4902841 := by exact prefixLift 4902841
  have htrace : WordTrace (prefixWord ++ tailWord_4902841) baseStart_4902841 baseEnd_4902841 := by
    simpa [prefixWord, tailWord_4902841, baseEnd_4902841] using wordTrace_append hprefix tailTrace_4902841
  have hstable : (prefixWord ++ tailWord_4902841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902841).length < 2 ^ (prefixWord ++ tailWord_4902841).sum := by decide
  have hdescent : baseEnd_4902841 < baseStart_4902841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902847 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 4]
def baseStart_4902847 : Nat := 118140960795 + 4902847 * 2 ^ 59
def prefixEnd_4902847 : Nat := 4983230072969 + 3 ^ 40 * 4902847 * 2
def baseEnd_4902847 : Nat := 2517517086454284322264723

theorem tailTrace_4902847 : CollatzResearch.WordTrace tailWord_4902847 prefixEnd_4902847 2517517086454284322264723 := by
  unfold tailWord_4902847
  simp only [CollatzResearch.WordTrace]
  refine ⟨178821520868830133448698795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119214347245886755632465863 178821520868830133448698795)
  ·
    refine ⟨268232281303245200173048193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178821520868830133448698795 268232281303245200173048193)
    ·
      refine ⟨201174210977433900129786145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268232281303245200173048193 201174210977433900129786145)
      ·
        refine ⟨150880658233075425097339609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201174210977433900129786145 150880658233075425097339609)
        ·
          refine ⟨113160493674806568823004707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150880658233075425097339609 113160493674806568823004707)
          ·
            refine ⟨169740740512209853234507061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113160493674806568823004707 169740740512209853234507061)
            ·
              refine ⟨15913194423019673740735037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169740740512209853234507061 15913194423019673740735037)
              ·
                refine ⟨5967447908632377652775639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15913194423019673740735037 5967447908632377652775639)
                ·
                  refine ⟨8951171862948566479163459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5967447908632377652775639 8951171862948566479163459)
                  ·
                    refine ⟨13426757794422849718745189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8951171862948566479163459 13426757794422849718745189)
                    ·
                      refine ⟨2517517086454284322264723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13426757794422849718745189 2517517086454284322264723)
                      ·
                        rfl

theorem cell23_4902847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_4902847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902847 prefixEnd_4902847 := by exact prefixLift 4902847
  have htrace : WordTrace (prefixWord ++ tailWord_4902847) baseStart_4902847 baseEnd_4902847 := by
    simpa [prefixWord, tailWord_4902847, baseEnd_4902847] using wordTrace_append hprefix tailTrace_4902847
  have hstable : (prefixWord ++ tailWord_4902847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902847).length < 2 ^ (prefixWord ++ tailWord_4902847).sum := by decide
  have hdescent : baseEnd_4902847 < baseStart_4902847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902864 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 3, 2, 2]
def baseStart_4902864 : Nat := 118140960795 + 4902864 * 2 ^ 59
def prefixEnd_4902864 : Nat := 4983230072969 + 3 ^ 40 * 4902864 * 2
def baseEnd_4902864 : Nat := 2517525815625410755752145

theorem tailTrace_4902864 : CollatzResearch.WordTrace tailWord_4902864 prefixEnd_4902864 2517525815625410755752145 := by
  unfold tailWord_4902864
  simp only [CollatzResearch.WordTrace]
  refine ⟨89411070454884272676033823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119214760606512363568045097 89411070454884272676033823)
  ·
    refine ⟨134116605682326409014050735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89411070454884272676033823 134116605682326409014050735)
    ·
      refine ⟨201174908523489613521076103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134116605682326409014050735 201174908523489613521076103)
      ·
        refine ⟨301762362785234420281614155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201174908523489613521076103 301762362785234420281614155)
        ·
          refine ⟨452643544177851630422421233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301762362785234420281614155 452643544177851630422421233)
          ·
            refine ⟨339482658133388722816815925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452643544177851630422421233 339482658133388722816815925)
            ·
              refine ⟨31826499200005192764076493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 339482658133388722816815925 31826499200005192764076493)
              ·
                refine ⟨11934937200001947286528685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31826499200005192764076493 11934937200001947286528685)
                ·
                  refine ⟨4475601450000730232448257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11934937200001947286528685 4475601450000730232448257)
                  ·
                    refine ⟨3356701087500547674336193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4475601450000730232448257 3356701087500547674336193)
                    ·
                      refine ⟨2517525815625410755752145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356701087500547674336193 2517525815625410755752145)
                      ·
                        rfl

theorem cell23_4902864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 2, 2].length) (baseStart_4902864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902864 prefixEnd_4902864 := by exact prefixLift 4902864
  have htrace : WordTrace (prefixWord ++ tailWord_4902864) baseStart_4902864 baseEnd_4902864 := by
    simpa [prefixWord, tailWord_4902864, baseEnd_4902864] using wordTrace_append hprefix tailTrace_4902864
  have hstable : (prefixWord ++ tailWord_4902864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902864).length < 2 ^ (prefixWord ++ tailWord_4902864).sum := by decide
  have hdescent : baseEnd_4902864 < baseStart_4902864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902874 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_4902874 : Nat := 118140960795 + 4902874 * 2 ^ 59
def prefixEnd_4902874 : Nat := 4983230072969 + 3 ^ 40 * 4902874 * 2
def baseEnd_4902874 : Nat := 839176983477318572209033

theorem tailTrace_4902874 : CollatzResearch.WordTrace tailWord_4902874 prefixEnd_4902874 839176983477318572209033 := by
  unfold tailWord_4902874
  simp only [CollatzResearch.WordTrace]
  refine ⟨44705626409933079264982919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119215003759821544706621117 44705626409933079264982919)
  ·
    refine ⟨67058439614899618897474379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44705626409933079264982919 67058439614899618897474379)
    ·
      refine ⟨100587659422349428346211569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67058439614899618897474379 100587659422349428346211569)
      ·
        refine ⟨75440744566762071259658677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100587659422349428346211569 75440744566762071259658677)
        ·
          refine ⟨7072569803133944180593001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75440744566762071259658677 7072569803133944180593001)
          ·
            refine ⟨5304427352350458135444751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7072569803133944180593001 5304427352350458135444751)
            ·
              refine ⟨7956641028525687203167127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304427352350458135444751 7956641028525687203167127)
              ·
                refine ⟨11934961542788530804750691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7956641028525687203167127 11934961542788530804750691)
                ·
                  refine ⟨17902442314182796207126037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11934961542788530804750691 17902442314182796207126037)
                  ·
                    refine ⟨839176983477318572209033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17902442314182796207126037 839176983477318572209033)
                    ·
                      rfl

theorem cell23_4902874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_4902874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902874 prefixEnd_4902874 := by exact prefixLift 4902874
  have htrace : WordTrace (prefixWord ++ tailWord_4902874) baseStart_4902874 baseEnd_4902874 := by
    simpa [prefixWord, tailWord_4902874, baseEnd_4902874] using wordTrace_append hprefix tailTrace_4902874
  have hstable : (prefixWord ++ tailWord_4902874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902874).length < 2 ^ (prefixWord ++ tailWord_4902874).sum := by decide
  have hdescent : baseEnd_4902874 < baseStart_4902874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902884 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_4902884 : Nat := 118140960795 + 4902884 * 2 ^ 59
def prefixEnd_4902884 : Nat := 4983230072969 + 3 ^ 40 * 4902884 * 2
def baseEnd_4902884 : Nat := 2517536085238500677502053

theorem tailTrace_4902884 : CollatzResearch.WordTrace tailWord_4902884 prefixEnd_4902884 2517536085238500677502053 := by
  unfold tailWord_4902884
  simp only [CollatzResearch.WordTrace]
  refine ⟨89411435184848044383897853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119215246913130725845197137 89411435184848044383897853)
  ·
    refine ⟨33529288194318016643961695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89411435184848044383897853 33529288194318016643961695)
    ·
      refine ⟨50293932291477024965942543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33529288194318016643961695 50293932291477024965942543)
      ·
        refine ⟨75440898437215537448913815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50293932291477024965942543 75440898437215537448913815)
        ·
          refine ⟨113161347655823306173370723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75440898437215537448913815 113161347655823306173370723)
          ·
            refine ⟨169742021483734959260056085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113161347655823306173370723 169742021483734959260056085)
            ·
              refine ⟨7956657257050076215315129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169742021483734959260056085 7956657257050076215315129)
              ·
                refine ⟨5967492942787557161486347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7956657257050076215315129 5967492942787557161486347)
                ·
                  refine ⟨8951239414181335742229521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5967492942787557161486347 8951239414181335742229521)
                  ·
                    refine ⟨6713429560636001806672141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8951239414181335742229521 6713429560636001806672141)
                    ·
                      refine ⟨2517536085238500677502053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713429560636001806672141 2517536085238500677502053)
                      ·
                        rfl

theorem cell23_4902884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_4902884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902884 prefixEnd_4902884 := by exact prefixLift 4902884
  have htrace : WordTrace (prefixWord ++ tailWord_4902884) baseStart_4902884 baseEnd_4902884 := by
    simpa [prefixWord, tailWord_4902884, baseEnd_4902884] using wordTrace_append hprefix tailTrace_4902884
  have hstable : (prefixWord ++ tailWord_4902884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902884).length < 2 ^ (prefixWord ++ tailWord_4902884).sum := by decide
  have hdescent : baseEnd_4902884 < baseStart_4902884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902887 : List Nat := [1, 1, 5, 2, 3, 1, 1, 9]
def baseStart_4902887 : Nat := 118140960795 + 4902887 * 2 ^ 59
def prefixEnd_4902887 : Nat := 4983230072969 + 3 ^ 40 * 4902887 * 2
def baseEnd_4902887 : Nat := 93242134284461635769057

theorem tailTrace_4902887 : CollatzResearch.WordTrace tailWord_4902887 prefixEnd_4902887 93242134284461635769057 := by
  unfold tailWord_4902887
  simp only [CollatzResearch.WordTrace]
  refine ⟨178822979788685220280154915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119215319859123480186769943 178822979788685220280154915)
  ·
    refine ⟨268234469683027830420232373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178822979788685220280154915 268234469683027830420232373)
    ·
      refine ⟨25146981532783859101896785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 268234469683027830420232373 25146981532783859101896785)
      ·
        refine ⟨18860236149587894326422589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25146981532783859101896785 18860236149587894326422589)
        ·
          refine ⟨7072588556095460372408471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18860236149587894326422589 7072588556095460372408471)
          ·
            refine ⟨10608882834143190558612707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7072588556095460372408471 10608882834143190558612707)
            ·
              refine ⟨15913324251214785837919061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10608882834143190558612707 15913324251214785837919061)
              ·
                refine ⟨93242134284461635769057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15913324251214785837919061 93242134284461635769057)
                ·
                  rfl

theorem cell23_4902887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 9].length) (baseStart_4902887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902887 prefixEnd_4902887 := by exact prefixLift 4902887
  have htrace : WordTrace (prefixWord ++ tailWord_4902887) baseStart_4902887 baseEnd_4902887 := by
    simpa [prefixWord, tailWord_4902887, baseEnd_4902887] using wordTrace_append hprefix tailTrace_4902887
  have hstable : (prefixWord ++ tailWord_4902887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902887).length < 2 ^ (prefixWord ++ tailWord_4902887).sum := by decide
  have hdescent : baseEnd_4902887 < baseStart_4902887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902924 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 3, 3, 2]
def baseStart_4902924 : Nat := 118140960795 + 4902924 * 2 ^ 59
def prefixEnd_4902924 : Nat := 4983230072969 + 3 ^ 40 * 4902924 * 2
def baseEnd_4902924 : Nat := 2517556624464680521001869

theorem tailTrace_4902924 : CollatzResearch.WordTrace tailWord_4902924 prefixEnd_4902924 2517556624464680521001869 := by
  unfold tailWord_4902924
  simp only [CollatzResearch.WordTrace]
  refine ⟨89412164644775587799625913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119216219526367450399501217 89412164644775587799625913)
  ·
    refine ⟨67059123483581690849719435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89412164644775587799625913 67059123483581690849719435)
    ·
      refine ⟨100588685225372536274579153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67059123483581690849719435 100588685225372536274579153)
      ·
        refine ⟨75441513919029402205934365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100588685225372536274579153 75441513919029402205934365)
        ·
          refine ⟨28290567719636025827225387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75441513919029402205934365 28290567719636025827225387)
          ·
            refine ⟨42435851579454038740838081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28290567719636025827225387 42435851579454038740838081)
            ·
              refine ⟨31826888684590529055628561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42435851579454038740838081 31826888684590529055628561)
              ·
                refine ⟨23870166513442896791721421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31826888684590529055628561 23870166513442896791721421)
                ·
                  refine ⟨8951312442541086296895533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23870166513442896791721421 8951312442541086296895533)
                  ·
                    refine ⟨3356742165952907361335825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8951312442541086296895533 3356742165952907361335825)
                    ·
                      refine ⟨2517556624464680521001869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356742165952907361335825 2517556624464680521001869)
                      ·
                        rfl

theorem cell23_4902924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_4902924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902924 prefixEnd_4902924 := by exact prefixLift 4902924
  have htrace : WordTrace (prefixWord ++ tailWord_4902924) baseStart_4902924 baseEnd_4902924 := by
    simpa [prefixWord, tailWord_4902924, baseEnd_4902924] using wordTrace_append hprefix tailTrace_4902924
  have hstable : (prefixWord ++ tailWord_4902924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902924).length < 2 ^ (prefixWord ++ tailWord_4902924).sum := by decide
  have hdescent : baseEnd_4902924 < baseStart_4902924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902925 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4902925 : Nat := 118140960795 + 4902925 * 2 ^ 59
def prefixEnd_4902925 : Nat := 4983230072969 + 3 ^ 40 * 4902925 * 2
def baseEnd_4902925 : Nat := 839185712648445005696455

theorem tailTrace_4902925 : CollatzResearch.WordTrace tailWord_4902925 prefixEnd_4902925 839185712648445005696455 := by
  unfold tailWord_4902925
  simp only [CollatzResearch.WordTrace]
  refine ⟨178824365762547552770038229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119216243841698368513358819 178824365762547552770038229)
  ·
    refine ⟨4191196072559708268047771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 178824365762547552770038229 4191196072559708268047771)
    ·
      refine ⟨6286794108839562402071657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4191196072559708268047771 6286794108839562402071657)
      ·
        refine ⟨4715095581629671801553743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6286794108839562402071657 4715095581629671801553743)
        ·
          refine ⟨7072643372444507702330615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715095581629671801553743 7072643372444507702330615)
          ·
            refine ⟨10608965058666761553495923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7072643372444507702330615 10608965058666761553495923)
            ·
              refine ⟨15913447588000142330243885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10608965058666761553495923 15913447588000142330243885)
              ·
                refine ⟨5967542845500053373841457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15913447588000142330243885 5967542845500053373841457)
                ·
                  refine ⟨4475657134125040030381093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5967542845500053373841457 4475657134125040030381093)
                  ·
                    refine ⟨839185712648445005696455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4475657134125040030381093 839185712648445005696455)
                    ·
                      rfl

theorem cell23_4902925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4902925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902925 prefixEnd_4902925 := by exact prefixLift 4902925
  have htrace : WordTrace (prefixWord ++ tailWord_4902925) baseStart_4902925 baseEnd_4902925 := by
    simpa [prefixWord, tailWord_4902925, baseEnd_4902925] using wordTrace_append hprefix tailTrace_4902925
  have hstable : (prefixWord ++ tailWord_4902925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902925).length < 2 ^ (prefixWord ++ tailWord_4902925).sum := by decide
  have hdescent : baseEnd_4902925 < baseStart_4902925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902931 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 2, 1, 3]
def baseStart_4902931 : Nat := 118140960795 + 4902931 * 2 ^ 59
def prefixEnd_4902931 : Nat := 4983230072969 + 3 ^ 40 * 4902931 * 2
def baseEnd_4902931 : Nat := 2517560218829261993614337

theorem tailTrace_4902931 : CollatzResearch.WordTrace tailWord_4902931 prefixEnd_4902931 2517560218829261993614337 := by
  unfold tailWord_4902931
  simp only [CollatzResearch.WordTrace]
  refine ⟨178824584600525815794756647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119216389733683877196504431 178824584600525815794756647)
  ·
    refine ⟨268236876900788723692134971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178824584600525815794756647 268236876900788723692134971)
    ·
      refine ⟨402355315351183085538202457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268236876900788723692134971 402355315351183085538202457)
      ·
        refine ⟨301766486513387314153651843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402355315351183085538202457 301766486513387314153651843)
        ·
          refine ⟨452649729770080971230477765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301766486513387314153651843 452649729770080971230477765)
          ·
            refine ⟨84871824331890182105714581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 452649729770080971230477765 84871824331890182105714581)
            ·
              refine ⟨3978366765557352286205371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84871824331890182105714581 3978366765557352286205371)
              ·
                refine ⟨5967550148336028429308057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978366765557352286205371 5967550148336028429308057)
                ·
                  refine ⟨4475662611252021321981043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5967550148336028429308057 4475662611252021321981043)
                  ·
                    refine ⟨6713493916878031982971565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4475662611252021321981043 6713493916878031982971565)
                    ·
                      refine ⟨2517560218829261993614337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713493916878031982971565 2517560218829261993614337)
                      ·
                        rfl

theorem cell23_4902931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 1, 3].length) (baseStart_4902931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902931 prefixEnd_4902931 := by exact prefixLift 4902931
  have htrace : WordTrace (prefixWord ++ tailWord_4902931) baseStart_4902931 baseEnd_4902931 := by
    simpa [prefixWord, tailWord_4902931, baseEnd_4902931] using wordTrace_append hprefix tailTrace_4902931
  have hstable : (prefixWord ++ tailWord_4902931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902931).length < 2 ^ (prefixWord ++ tailWord_4902931).sum := by decide
  have hdescent : baseEnd_4902931 < baseStart_4902931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902941 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_4902941 : Nat := 118140960795 + 4902941 * 2 ^ 59
def prefixEnd_4902941 : Nat := 4983230072969 + 3 ^ 40 * 4902941 * 2
def baseEnd_4902941 : Nat := 2517565353635806954489291

theorem tailTrace_4902941 : CollatzResearch.WordTrace tailWord_4902941 prefixEnd_4902941 2517565353635806954489291 := by
  unfold tailWord_4902941
  simp only [CollatzResearch.WordTrace]
  refine ⟨178824949330489587502620677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119216632886993058335080451 178824949330489587502620677)
  ·
    refine ⟨33529677999466797656741377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178824949330489587502620677 33529677999466797656741377)
    ·
      refine ⟨25147258499600098242556033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33529677999466797656741377 25147258499600098242556033)
      ·
        refine ⟨18860443874700073681917025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25147258499600098242556033 18860443874700073681917025)
        ·
          refine ⟨14145332906025055261437769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18860443874700073681917025 14145332906025055261437769)
          ·
            refine ⟨10608999679518791446078327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14145332906025055261437769 10608999679518791446078327)
            ·
              refine ⟨15913499519278187169117491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10608999679518791446078327 15913499519278187169117491)
              ·
                refine ⟨23870249278917280753676237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15913499519278187169117491 23870249278917280753676237)
                ·
                  refine ⟨8951343479593980282628589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23870249278917280753676237 8951343479593980282628589)
                  ·
                    refine ⟨3356753804847742605985721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8951343479593980282628589 3356753804847742605985721)
                    ·
                      refine ⟨2517565353635806954489291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356753804847742605985721 2517565353635806954489291)
                      ·
                        rfl

theorem cell23_4902941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_4902941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902941 prefixEnd_4902941 := by exact prefixLift 4902941
  have htrace : WordTrace (prefixWord ++ tailWord_4902941) baseStart_4902941 baseEnd_4902941 := by
    simpa [prefixWord, tailWord_4902941, baseEnd_4902941] using wordTrace_append hprefix tailTrace_4902941
  have hstable : (prefixWord ++ tailWord_4902941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902941).length < 2 ^ (prefixWord ++ tailWord_4902941).sum := by decide
  have hdescent : baseEnd_4902941 < baseStart_4902941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902987 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 3]
def baseStart_4902987 : Nat := 118140960795 + 4902987 * 2 ^ 59
def prefixEnd_4902987 : Nat := 4983230072969 + 3 ^ 40 * 4902987 * 2
def baseEnd_4902987 : Nat := 2517588973745913774514079

theorem tailTrace_4902987 : CollatzResearch.WordTrace tailWord_4902987 prefixEnd_4902987 2517588973745913774514079 := by
  unfold tailWord_4902987
  simp only [CollatzResearch.WordTrace]
  refine ⟨178826627088322937358795215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119217751392215291572530143 178826627088322937358795215)
  ·
    refine ⟨268239940632484406038192823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178826627088322937358795215 268239940632484406038192823)
    ·
      refine ⟨402359910948726609057289235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268239940632484406038192823 402359910948726609057289235)
      ·
        refine ⟨603539866423089913585933853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402359910948726609057289235 603539866423089913585933853)
        ·
          refine ⟨226327449908658717594725195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 603539866423089913585933853 226327449908658717594725195)
          ·
            refine ⟨339491174862988076392087793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226327449908658717594725195 339491174862988076392087793)
            ·
              refine ⟨254618381147241057294065845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339491174862988076392087793 254618381147241057294065845)
              ·
                refine ⟨23870473232553849121318673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254618381147241057294065845 23870473232553849121318673)
                ·
                  refine ⟨17902854924415386840989005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23870473232553849121318673 17902854924415386840989005)
                  ·
                    refine ⟨6713570596655770065370877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17902854924415386840989005 6713570596655770065370877)
                    ·
                      refine ⟨2517588973745913774514079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713570596655770065370877 2517588973745913774514079)
                      ·
                        rfl

theorem cell23_4902987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 3].length) (baseStart_4902987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902987 prefixEnd_4902987 := by exact prefixLift 4902987
  have htrace : WordTrace (prefixWord ++ tailWord_4902987) baseStart_4902987 baseEnd_4902987 := by
    simpa [prefixWord, tailWord_4902987, baseEnd_4902987] using wordTrace_append hprefix tailTrace_4902987
  have hstable : (prefixWord ++ tailWord_4902987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902987).length < 2 ^ (prefixWord ++ tailWord_4902987).sum := by decide
  have hdescent : baseEnd_4902987 < baseStart_4902987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4902994 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 7]
def baseStart_4902994 : Nat := 118140960795 + 4902994 * 2 ^ 59
def prefixEnd_4902994 : Nat := 4983230072969 + 3 ^ 40 * 4902994 * 2
def baseEnd_4902994 : Nat := 279732507567832805236283

theorem tailTrace_4902994 : CollatzResearch.WordTrace tailWord_4902994 prefixEnd_4902994 279732507567832805236283 := by
  unfold tailWord_4902994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44706720599824394388575009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119217921599531718369533357 44706720599824394388575009)
  ·
    refine ⟨33530040449868295791431257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44706720599824394388575009 33530040449868295791431257)
    ·
      refine ⟨25147530337401221843573443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33530040449868295791431257 25147530337401221843573443)
      ·
        refine ⟨37721295506101832765360165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25147530337401221843573443 37721295506101832765360165)
        ·
          refine ⟨7072742907394093643505031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37721295506101832765360165 7072742907394093643505031)
          ·
            refine ⟨10609114361091140465257547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7072742907394093643505031 10609114361091140465257547)
            ·
              refine ⟨15913671541636710697886321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10609114361091140465257547 15913671541636710697886321)
              ·
                refine ⟨11935253656227533023414741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15913671541636710697886321 11935253656227533023414741)
                ·
                  refine ⟨279732507567832805236283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11935253656227533023414741 279732507567832805236283)
                  ·
                    rfl

theorem cell23_4902994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_4902994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4902994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4902994 prefixEnd_4902994 := by exact prefixLift 4902994
  have htrace : WordTrace (prefixWord ++ tailWord_4902994) baseStart_4902994 baseEnd_4902994 := by
    simpa [prefixWord, tailWord_4902994, baseEnd_4902994] using wordTrace_append hprefix tailTrace_4902994
  have hstable : (prefixWord ++ tailWord_4902994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4902994).length < 2 ^ (prefixWord ++ tailWord_4902994).sum := by decide
  have hdescent : baseEnd_4902994 < baseStart_4902994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4902994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903007 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 2, 5]
def baseStart_4903007 : Nat := 118140960795 + 4903007 * 2 ^ 59
def prefixEnd_4903007 : Nat := 4983230072969 + 3 ^ 40 * 4903007 * 2
def baseEnd_4903007 : Nat := 839199747786334565421329

theorem tailTrace_4903007 : CollatzResearch.WordTrace tailWord_4903007 prefixEnd_4903007 839199747786334565421329 := by
  unfold tailWord_4903007
  simp only [CollatzResearch.WordTrace]
  refine ⟨178827356548250480774523275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119218237698833653849682183 178827356548250480774523275)
  ·
    refine ⟨268241034822375721161784913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178827356548250480774523275 268241034822375721161784913)
    ·
      refine ⟨201180776116781790871338685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268241034822375721161784913 201180776116781790871338685)
      ·
        refine ⟨75442791043793171576752007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201180776116781790871338685 75442791043793171576752007)
        ·
          refine ⟨113164186565689757365128011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75442791043793171576752007 113164186565689757365128011)
          ·
            refine ⟨169746279848534636047692017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113164186565689757365128011 169746279848534636047692017)
            ·
              refine ⟨127309709886400977035769013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169746279848534636047692017 127309709886400977035769013)
              ·
                refine ⟨11935285301850091597103345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127309709886400977035769013 11935285301850091597103345)
                ·
                  refine ⟨8951463976387568697827509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11935285301850091597103345 8951463976387568697827509)
                  ·
                    refine ⟨839199747786334565421329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8951463976387568697827509 839199747786334565421329)
                    ·
                      rfl

theorem cell23_4903007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_4903007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903007 prefixEnd_4903007 := by exact prefixLift 4903007
  have htrace : WordTrace (prefixWord ++ tailWord_4903007) baseStart_4903007 baseEnd_4903007 := by
    simpa [prefixWord, tailWord_4903007, baseEnd_4903007] using wordTrace_append hprefix tailTrace_4903007
  have hstable : (prefixWord ++ tailWord_4903007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903007).length < 2 ^ (prefixWord ++ tailWord_4903007).sum := by decide
  have hdescent : baseEnd_4903007 < baseStart_4903007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903114 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_4903114 : Nat := 118140960795 + 4903114 * 2 ^ 59
def prefixEnd_4903114 : Nat := 4983230072969 + 3 ^ 40 * 4903114 * 2
def baseEnd_4903114 : Nat := 839218061929678259208665

theorem tailTrace_4903114 : CollatzResearch.WordTrace tailWord_4903114 prefixEnd_4903114 839218061929678259208665 := by
  unfold tailWord_4903114
  simp only [CollatzResearch.WordTrace]
  refine ⟨44707814789715709512167099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119220839439241892032445597 44707814789715709512167099)
  ·
    refine ⟨67061722184573564268250649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44707814789715709512167099 67061722184573564268250649)
    ·
      refine ⟨50296291638430173201187987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67061722184573564268250649 50296291638430173201187987)
      ·
        refine ⟨75444437457645259801781981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50296291638430173201187987 75444437457645259801781981)
        ·
          refine ⟨28291664046616972425668243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75444437457645259801781981 28291664046616972425668243)
          ·
            refine ⟨42437496069925458638502365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28291664046616972425668243 42437496069925458638502365)
            ·
              refine ⟨15914061026222046989438387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42437496069925458638502365 15914061026222046989438387)
              ·
                refine ⟨23871091539333070484157581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15914061026222046989438387 23871091539333070484157581)
                ·
                  refine ⟨8951659327249901431559093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23871091539333070484157581 8951659327249901431559093)
                  ·
                    refine ⟨839218061929678259208665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8951659327249901431559093 839218061929678259208665)
                    ·
                      rfl

theorem cell23_4903114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_4903114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903114 prefixEnd_4903114 := by exact prefixLift 4903114
  have htrace : WordTrace (prefixWord ++ tailWord_4903114) baseStart_4903114 baseEnd_4903114 := by
    simpa [prefixWord, tailWord_4903114, baseEnd_4903114] using wordTrace_append hprefix tailTrace_4903114
  have hstable : (prefixWord ++ tailWord_4903114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903114).length < 2 ^ (prefixWord ++ tailWord_4903114).sum := by decide
  have hdescent : baseEnd_4903114 < baseStart_4903114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903121 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 2, 3, 2]
def baseStart_4903121 : Nat := 118140960795 + 4903121 * 2 ^ 59
def prefixEnd_4903121 : Nat := 4983230072969 + 3 ^ 40 * 4903121 * 2
def baseEnd_4903121 : Nat := 2517657780153616250238463

theorem tailTrace_4903121 : CollatzResearch.WordTrace tailWord_4903121 prefixEnd_4903121 2517657780153616250238463 := by
  unfold tailWord_4903121
  simp only [CollatzResearch.WordTrace]
  refine ⟨178831514469837478244173217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119221009646558318829448811 178831514469837478244173217)
  ·
    refine ⟨134123635852378108683129913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178831514469837478244173217 134123635852378108683129913)
    ·
      refine ⟨100592726889283581512347435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134123635852378108683129913 100592726889283581512347435)
      ·
        refine ⟨150889090333925372268521153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100592726889283581512347435 150889090333925372268521153)
        ·
          refine ⟨113166817750444029201390865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150889090333925372268521153 113166817750444029201390865)
          ·
            refine ⟨84875113312833021901043149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113166817750444029201390865 84875113312833021901043149)
            ·
              refine ⟨31828167492312383212891181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84875113312833021901043149 31828167492312383212891181)
              ·
                refine ⟨11935562809617143704834193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31828167492312383212891181 11935562809617143704834193)
                ·
                  refine ⟨8951672107212857778625645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11935562809617143704834193 8951672107212857778625645)
                  ·
                    refine ⟨3356877040204821666984617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8951672107212857778625645 3356877040204821666984617)
                    ·
                      refine ⟨2517657780153616250238463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356877040204821666984617 2517657780153616250238463)
                      ·
                        rfl

theorem cell23_4903121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_4903121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903121 prefixEnd_4903121 := by exact prefixLift 4903121
  have htrace : WordTrace (prefixWord ++ tailWord_4903121) baseStart_4903121 baseEnd_4903121 := by
    simpa [prefixWord, tailWord_4903121, baseEnd_4903121] using wordTrace_append hprefix tailTrace_4903121
  have hstable : (prefixWord ++ tailWord_4903121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903121).length < 2 ^ (prefixWord ++ tailWord_4903121).sum := by decide
  have hdescent : baseEnd_4903121 < baseStart_4903121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903139 : List Nat := [1, 1, 1, 8, 2, 1, 2, 2, 1, 4]
def baseStart_4903139 : Nat := 118140960795 + 4903139 * 2 ^ 59
def prefixEnd_4903139 : Nat := 4983230072969 + 3 ^ 40 * 4903139 * 2
def baseEnd_4903139 : Nat := 839222340935132393271127

theorem tailTrace_4903139 : CollatzResearch.WordTrace tailWord_4903139 prefixEnd_4903139 839222340935132393271127 := by
  unfold tailWord_4903139
  simp only [CollatzResearch.WordTrace]
  refine ⟨178832170983772267318328471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119221447322514844878885647 178832170983772267318328471)
  ·
    refine ⟨268248256475658400977492707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178832170983772267318328471 268248256475658400977492707)
    ·
      refine ⟨402372384713487601466239061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268248256475658400977492707 402372384713487601466239061)
      ·
        refine ⟨4715301383361182829682489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 402372384713487601466239061 4715301383361182829682489)
        ·
          refine ⟨3536476037520887122261867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4715301383361182829682489 3536476037520887122261867)
          ·
            refine ⟨5304714056281330683392801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536476037520887122261867 5304714056281330683392801)
            ·
              refine ⟨3978535542210998012544601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5304714056281330683392801 3978535542210998012544601)
              ·
                refine ⟨2983901656658248509408451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3978535542210998012544601 2983901656658248509408451)
                ·
                  refine ⟨4475852484987372764112677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983901656658248509408451 4475852484987372764112677)
                  ·
                    refine ⟨839222340935132393271127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4475852484987372764112677 839222340935132393271127)
                    ·
                      rfl

theorem cell23_4903139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 4].length) (baseStart_4903139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903139 prefixEnd_4903139 := by exact prefixLift 4903139
  have htrace : WordTrace (prefixWord ++ tailWord_4903139) baseStart_4903139 baseEnd_4903139 := by
    simpa [prefixWord, tailWord_4903139, baseEnd_4903139] using wordTrace_append hprefix tailTrace_4903139
  have hstable : (prefixWord ++ tailWord_4903139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903139).length < 2 ^ (prefixWord ++ tailWord_4903139).sum := by decide
  have hdescent : baseEnd_4903139 < baseStart_4903139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903171 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 3]
def baseStart_4903171 : Nat := 118140960795 + 4903171 * 2 ^ 59
def prefixEnd_4903171 : Nat := 4983230072969 + 3 ^ 40 * 4903171 * 2
def baseEnd_4903171 : Nat := 2517683454186341054613233

theorem tailTrace_4903171 : CollatzResearch.WordTrace tailWord_4903171 prefixEnd_4903171 2517683454186341054613233 := by
  unfold tailWord_4903171
  simp only [CollatzResearch.WordTrace]
  refine ⟨178833338119656336783493367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119222225413104224522328911 178833338119656336783493367)
  ·
    refine ⟨268250007179484505175240051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178833338119656336783493367 268250007179484505175240051)
    ·
      refine ⟨402375010769226757762860077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268250007179484505175240051 402375010769226757762860077)
      ·
        refine ⟨150890629038460034161072529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 402375010769226757762860077 150890629038460034161072529)
        ·
          refine ⟨113167971778845025620804397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150890629038460034161072529 113167971778845025620804397)
          ·
            refine ⟨42437989417066884607801649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113167971778845025620804397 42437989417066884607801649)
            ·
              refine ⟨31828492062800163455851237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42437989417066884607801649 31828492062800163455851237)
              ·
                refine ⟨5967842261775030647972107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31828492062800163455851237 5967842261775030647972107)
                ·
                  refine ⟨8951763392662545971958161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5967842261775030647972107 8951763392662545971958161)
                  ·
                    refine ⟨6713822544496909478968621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8951763392662545971958161 6713822544496909478968621)
                    ·
                      refine ⟨2517683454186341054613233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6713822544496909478968621 2517683454186341054613233)
                      ·
                        rfl

theorem cell23_4903171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_4903171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903171 prefixEnd_4903171 := by exact prefixLift 4903171
  have htrace : WordTrace (prefixWord ++ tailWord_4903171) baseStart_4903171 baseEnd_4903171 := by
    simpa [prefixWord, tailWord_4903171, baseEnd_4903171] using wordTrace_append hprefix tailTrace_4903171
  have hstable : (prefixWord ++ tailWord_4903171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903171).length < 2 ^ (prefixWord ++ tailWord_4903171).sum := by decide
  have hdescent : baseEnd_4903171 < baseStart_4903171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903172 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_4903172 : Nat := 118140960795 + 4903172 * 2 ^ 59
def prefixEnd_4903172 : Nat := 4983230072969 + 3 ^ 40 * 4903172 * 2
def baseEnd_4903172 : Nat := 2517683967666995550700729

theorem tailTrace_4903172 : CollatzResearch.WordTrace tailWord_4903172 prefixEnd_4903172 2517683967666995550700729 := by
  unfold tailWord_4903172
  simp only [CollatzResearch.WordTrace]
  refine ⟨89416687296326356977139885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119222249728435142636186513 89416687296326356977139885)
  ·
    refine ⟨33531257736122383866427457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89416687296326356977139885 33531257736122383866427457)
    ·
      refine ⟨25148443302091787899820593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33531257736122383866427457 25148443302091787899820593)
      ·
        refine ⟨18861332476568840924865445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25148443302091787899820593 18861332476568840924865445)
        ·
          refine ⟨3536499839356657673412271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18861332476568840924865445 3536499839356657673412271)
          ·
            refine ⟨5304749759034986510118407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536499839356657673412271 5304749759034986510118407)
            ·
              refine ⟨7957124638552479765177611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304749759034986510118407 7957124638552479765177611)
              ·
                refine ⟨11935686957828719647766417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7957124638552479765177611 11935686957828719647766417)
                ·
                  refine ⟨8951765218371539735824813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11935686957828719647766417 8951765218371539735824813)
                  ·
                    refine ⟨3356911956889327400934305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8951765218371539735824813 3356911956889327400934305)
                    ·
                      refine ⟨2517683967666995550700729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356911956889327400934305 2517683967666995550700729)
                      ·
                        rfl

theorem cell23_4903172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_4903172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903172 prefixEnd_4903172 := by exact prefixLift 4903172
  have htrace : WordTrace (prefixWord ++ tailWord_4903172) baseStart_4903172 baseEnd_4903172 := by
    simpa [prefixWord, tailWord_4903172, baseEnd_4903172] using wordTrace_append hprefix tailTrace_4903172
  have hstable : (prefixWord ++ tailWord_4903172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903172).length < 2 ^ (prefixWord ++ tailWord_4903172).sum := by decide
  have hdescent : baseEnd_4903172 < baseStart_4903172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903185 : List Nat := [1, 2, 2, 1, 1, 5, 1, 5, 1, 2, 2]
def baseStart_4903185 : Nat := 118140960795 + 4903185 * 2 ^ 59
def prefixEnd_4903185 : Nat := 4983230072969 + 3 ^ 40 * 4903185 * 2
def baseEnd_4903185 : Nat := 2517690642915503999838169

theorem tailTrace_4903185 : CollatzResearch.WordTrace tailWord_4903185 prefixEnd_4903185 2517690642915503999838169 := by
  unfold tailWord_4903185
  simp only [CollatzResearch.WordTrace]
  refine ⟨178833848741605617174503009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119222565827737078116335339 178833848741605617174503009)
  ·
    refine ⟨134125386556204212880877257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178833848741605617174503009 134125386556204212880877257)
    ·
      refine ⟨100594039917153159660657943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134125386556204212880877257 100594039917153159660657943)
      ·
        refine ⟨150891059875729739490986915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100594039917153159660657943 150891059875729739490986915)
        ·
          refine ⟨226336589813594609236480373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150891059875729739490986915 226336589813594609236480373)
          ·
            refine ⟨21219055295024494615920035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 226336589813594609236480373 21219055295024494615920035)
            ·
              refine ⟨31828582942536741923880053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21219055295024494615920035 31828582942536741923880053)
              ·
                refine ⟨2983929650862819555363755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31828582942536741923880053 2983929650862819555363755)
                ·
                  refine ⟨4475894476294229333045633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983929650862819555363755 4475894476294229333045633)
                  ·
                    refine ⟨3356920857220671999784225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4475894476294229333045633 3356920857220671999784225)
                    ·
                      refine ⟨2517690642915503999838169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356920857220671999784225 2517690642915503999838169)
                      ·
                        rfl

theorem cell23_4903185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_4903185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903185 prefixEnd_4903185 := by exact prefixLift 4903185
  have htrace : WordTrace (prefixWord ++ tailWord_4903185) baseStart_4903185 baseEnd_4903185 := by
    simpa [prefixWord, tailWord_4903185, baseEnd_4903185] using wordTrace_append hprefix tailTrace_4903185
  have hstable : (prefixWord ++ tailWord_4903185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903185).length < 2 ^ (prefixWord ++ tailWord_4903185).sum := by decide
  have hdescent : baseEnd_4903185 < baseStart_4903185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903202 : List Nat := [3, 3, 1, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_4903202 : Nat := 118140960795 + 4903202 * 2 ^ 59
def prefixEnd_4903202 : Nat := 4983230072969 + 3 ^ 40 * 4903202 * 2
def baseEnd_4903202 : Nat := 2517699372086630433325591

theorem tailTrace_4903202 : CollatzResearch.WordTrace tailWord_4903202 prefixEnd_4903202 2517699372086630433325591 := by
  unfold tailWord_4903202
  simp only [CollatzResearch.WordTrace]
  refine ⟨44708617195636007269467965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119222979188362686051914573 44708617195636007269467965)
  ·
    refine ⟨16765731448363502726050487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44708617195636007269467965 16765731448363502726050487)
    ·
      refine ⟨25148597172545254089075731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16765731448363502726050487 25148597172545254089075731)
      ·
        refine ⟨37722895758817881133613597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25148597172545254089075731 37722895758817881133613597)
        ·
          refine ⟨14146085909556705425105099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37722895758817881133613597 14146085909556705425105099)
          ·
            refine ⟨21219128864335058137657649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14146085909556705425105099 21219128864335058137657649)
            ·
              refine ⟨15914346648251293603243237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21219128864335058137657649 15914346648251293603243237)
              ·
                refine ⟨2983939996547117550608107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15914346648251293603243237 2983939996547117550608107)
                ·
                  refine ⟨4475909994820676325912161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983939996547117550608107 4475909994820676325912161)
                  ·
                    refine ⟨3356932496115507244434121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4475909994820676325912161 3356932496115507244434121)
                    ·
                      refine ⟨2517699372086630433325591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356932496115507244434121 2517699372086630433325591)
                      ·
                        rfl

theorem cell23_4903202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_4903202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903202 prefixEnd_4903202 := by exact prefixLift 4903202
  have htrace : WordTrace (prefixWord ++ tailWord_4903202) baseStart_4903202 baseEnd_4903202 := by
    simpa [prefixWord, tailWord_4903202, baseEnd_4903202] using wordTrace_append hprefix tailTrace_4903202
  have hstable : (prefixWord ++ tailWord_4903202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903202).length < 2 ^ (prefixWord ++ tailWord_4903202).sum := by decide
  have hdescent : baseEnd_4903202 < baseStart_4903202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903224 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_4903224 : Nat := 118140960795 + 4903224 * 2 ^ 59
def prefixEnd_4903224 : Nat := 4983230072969 + 3 ^ 40 * 4903224 * 2
def baseEnd_4903224 : Nat := 2517710668661029347250489

theorem tailTrace_4903224 : CollatzResearch.WordTrace tailWord_4903224 prefixEnd_4903224 2517710668661029347250489 := by
  unfold tailWord_4903224
  simp only [CollatzResearch.WordTrace]
  refine ⟨89417635594232163417586363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119223514125642884556781817 89417635594232163417586363)
  ·
    refine ⟨134126453391348245126379545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89417635594232163417586363 134126453391348245126379545)
    ·
      refine ⟨100594840043511183844784659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134126453391348245126379545 100594840043511183844784659)
      ·
        refine ⟨150892260065266775767176989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100594840043511183844784659 150892260065266775767176989)
        ·
          refine ⟨56584597524475040912691371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150892260065266775767176989 56584597524475040912691371)
          ·
            refine ⟨84876896286712561369037057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56584597524475040912691371 84876896286712561369037057)
            ·
              refine ⟨63657672215034421026777793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84876896286712561369037057 63657672215034421026777793)
              ·
                refine ⟨47743254161275815770083345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63657672215034421026777793 47743254161275815770083345)
                ·
                  refine ⟨35807440620956861827562509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47743254161275815770083345 35807440620956861827562509)
                  ·
                    refine ⟨13427790232858823185335941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35807440620956861827562509 13427790232858823185335941)
                    ·
                      refine ⟨2517710668661029347250489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13427790232858823185335941 2517710668661029347250489)
                      ·
                        rfl

theorem cell23_4903224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_4903224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903224 prefixEnd_4903224 := by exact prefixLift 4903224
  have htrace : WordTrace (prefixWord ++ tailWord_4903224) baseStart_4903224 baseEnd_4903224 := by
    simpa [prefixWord, tailWord_4903224, baseEnd_4903224] using wordTrace_append hprefix tailTrace_4903224
  have hstable : (prefixWord ++ tailWord_4903224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903224).length < 2 ^ (prefixWord ++ tailWord_4903224).sum := by decide
  have hdescent : baseEnd_4903224 < baseStart_4903224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903236 : List Nat := [2, 3, 4, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4903236 : Nat := 118140960795 + 4903236 * 2 ^ 59
def prefixEnd_4903236 : Nat := 4983230072969 + 3 ^ 40 * 4903236 * 2
def baseEnd_4903236 : Nat := 2517716830428883300300435

theorem tailTrace_4903236 : CollatzResearch.WordTrace tailWord_4903236 prefixEnd_4903236 2517716830428883300300435 := by
  unfold tailWord_4903236
  simp only [CollatzResearch.WordTrace]
  refine ⟨89417854432210426442304781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119223805909613901923073041 89417854432210426442304781)
  ·
    refine ⟨33531695412078909915864293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89417854432210426442304781 33531695412078909915864293)
    ·
      refine ⟨6287192889764795609224555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33531695412078909915864293 6287192889764795609224555)
      ·
        refine ⟨9430789334647193413836833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287192889764795609224555 9430789334647193413836833)
        ·
          refine ⟨7073092000985395060377625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9430789334647193413836833 7073092000985395060377625)
          ·
            refine ⟨5304819000739046295283219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7073092000985395060377625 5304819000739046295283219)
            ·
              refine ⟨7957228501108569442924829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304819000739046295283219 7957228501108569442924829)
              ·
                refine ⟨2983960687915713541096811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7957228501108569442924829 2983960687915713541096811)
                ·
                  refine ⟨4475941031873570311645217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983960687915713541096811 4475941031873570311645217)
                  ·
                    refine ⟨3356955773905177733733913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4475941031873570311645217 3356955773905177733733913)
                    ·
                      refine ⟨2517716830428883300300435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356955773905177733733913 2517716830428883300300435)
                      ·
                        rfl

theorem cell23_4903236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4903236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903236 prefixEnd_4903236 := by exact prefixLift 4903236
  have htrace : WordTrace (prefixWord ++ tailWord_4903236) baseStart_4903236 baseEnd_4903236 := by
    simpa [prefixWord, tailWord_4903236, baseEnd_4903236] using wordTrace_append hprefix tailTrace_4903236
  have hstable : (prefixWord ++ tailWord_4903236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903236).length < 2 ^ (prefixWord ++ tailWord_4903236).sum := by decide
  have hdescent : baseEnd_4903236 < baseStart_4903236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903241 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 3, 4, 2]
def baseStart_4903241 : Nat := 118140960795 + 4903241 * 2 ^ 59
def prefixEnd_4903241 : Nat := 4983230072969 + 3 ^ 40 * 4903241 * 2
def baseEnd_4903241 : Nat := 2517719397832155780737911

theorem tailTrace_4903241 : CollatzResearch.WordTrace tailWord_4903241 prefixEnd_4903241 2517719397832155780737911 := by
  unfold tailWord_4903241
  simp only [CollatzResearch.WordTrace]
  refine ⟨178835891229402738738541577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119223927486268492492361051 178835891229402738738541577)
  ·
    refine ⟨134126918422052054053906183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178835891229402738738541577 134126918422052054053906183)
    ·
      refine ⟨201190377633078081080859275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134126918422052054053906183 201190377633078081080859275)
      ·
        refine ⟨301785566449617121621288913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201190377633078081080859275 301785566449617121621288913)
        ·
          refine ⟨226339174837212841215966685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301785566449617121621288913 226339174837212841215966685)
          ·
            refine ⟨84877190563954815455987507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226339174837212841215966685 84877190563954815455987507)
            ·
              refine ⟨127315785845932223183981261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84877190563954815455987507 127315785845932223183981261)
              ·
                refine ⟨47743419692224583693992973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127315785845932223183981261 47743419692224583693992973)
                ·
                  refine ⟨17903782384584218885247365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47743419692224583693992973 17903782384584218885247365)
                  ·
                    refine ⟨3356959197109541040983881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17903782384584218885247365 3356959197109541040983881)
                    ·
                      refine ⟨2517719397832155780737911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3356959197109541040983881 2517719397832155780737911)
                      ·
                        rfl

theorem cell23_4903241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 4, 2].length) (baseStart_4903241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903241 prefixEnd_4903241 := by exact prefixLift 4903241
  have htrace : WordTrace (prefixWord ++ tailWord_4903241) baseStart_4903241 baseEnd_4903241 := by
    simpa [prefixWord, tailWord_4903241, baseEnd_4903241] using wordTrace_append hprefix tailTrace_4903241
  have hstable : (prefixWord ++ tailWord_4903241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903241).length < 2 ^ (prefixWord ++ tailWord_4903241).sum := by decide
  have hdescent : baseEnd_4903241 < baseStart_4903241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903408 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 1, 5, 2]
def baseStart_4903408 : Nat := 118140960795 + 4903408 * 2 ^ 59
def prefixEnd_4903408 : Nat := 4983230072969 + 3 ^ 40 * 4903408 * 2
def baseEnd_4903408 : Nat := 2517805149101456627349643

theorem tailTrace_4903408 : CollatzResearch.WordTrace tailWord_4903408 prefixEnd_4903408 2517805149101456627349643 := by
  unfold tailWord_4903408
  simp only [CollatzResearch.WordTrace]
  refine ⟨89420991109898863129935439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119227988146531817506580585 89420991109898863129935439)
  ·
    refine ⟨134131486664848294694903159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89420991109898863129935439 134131486664848294694903159)
    ·
      refine ⟨201197229997272442042354739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134131486664848294694903159 201197229997272442042354739)
      ·
        refine ⟨301795844995908663063532109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201197229997272442042354739 301795844995908663063532109)
        ·
          refine ⟨113173441873465748648824541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301795844995908663063532109 113173441873465748648824541)
          ·
            refine ⟨42440040702549655743309203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113173441873465748648824541 42440040702549655743309203)
            ·
              refine ⟨63660061053824483614963805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42440040702549655743309203 63660061053824483614963805)
              ·
                refine ⟨23872522895184181355611427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63660061053824483614963805 23872522895184181355611427)
                ·
                  refine ⟨35808784342776272033417141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23872522895184181355611427 35808784342776272033417141)
                  ·
                    refine ⟨3357073532135275503132857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35808784342776272033417141 3357073532135275503132857)
                    ·
                      refine ⟨2517805149101456627349643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357073532135275503132857 2517805149101456627349643)
                      ·
                        rfl

theorem cell23_4903408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 5, 2].length) (baseStart_4903408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903408 prefixEnd_4903408 := by exact prefixLift 4903408
  have htrace : WordTrace (prefixWord ++ tailWord_4903408) baseStart_4903408 baseEnd_4903408 := by
    simpa [prefixWord, tailWord_4903408, baseEnd_4903408] using wordTrace_append hprefix tailTrace_4903408
  have hstable : (prefixWord ++ tailWord_4903408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903408).length < 2 ^ (prefixWord ++ tailWord_4903408).sum := by decide
  have hdescent : baseEnd_4903408 < baseStart_4903408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903425 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_4903425 : Nat := 118140960795 + 4903425 * 2 ^ 59
def prefixEnd_4903425 : Nat := 4983230072969 + 3 ^ 40 * 4903425 * 2
def baseEnd_4903425 : Nat := 2517813878272583060837065

theorem tailTrace_4903425 : CollatzResearch.WordTrace tailWord_4903425 prefixEnd_4903425 2517813878272583060837065 := by
  unfold tailWord_4903425
  simp only [CollatzResearch.WordTrace]
  refine ⟨178842602260736138163239729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119228401507157425442159819 178842602260736138163239729)
  ·
    refine ⟨134131951695552103622429797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178842602260736138163239729 134131951695552103622429797)
    ·
      refine ⟨25149740942916019429205587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134131951695552103622429797 25149740942916019429205587)
      ·
        refine ⟨37724611414374029143808381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25149740942916019429205587 37724611414374029143808381)
        ·
          refine ⟨14146729280390260928928143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37724611414374029143808381 14146729280390260928928143)
          ·
            refine ⟨21220093920585391393392215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14146729280390260928928143 21220093920585391393392215)
            ·
              refine ⟨31830140880878087090088323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21220093920585391393392215 31830140880878087090088323)
              ·
                refine ⟨47745211321317130635132485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31830140880878087090088323 47745211321317130635132485)
                ·
                  refine ⟨8952227122746961994087341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47745211321317130635132485 8952227122746961994087341)
                  ·
                    refine ⟨3357085171030110747782753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8952227122746961994087341 3357085171030110747782753)
                    ·
                      refine ⟨2517813878272583060837065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357085171030110747782753 2517813878272583060837065)
                      ·
                        rfl

theorem cell23_4903425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_4903425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903425 prefixEnd_4903425 := by exact prefixLift 4903425
  have htrace : WordTrace (prefixWord ++ tailWord_4903425) baseStart_4903425 baseEnd_4903425 := by
    simpa [prefixWord, tailWord_4903425, baseEnd_4903425] using wordTrace_append hprefix tailTrace_4903425
  have hstable : (prefixWord ++ tailWord_4903425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903425).length < 2 ^ (prefixWord ++ tailWord_4903425).sum := by decide
  have hdescent : baseEnd_4903425 < baseStart_4903425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903426 : List Nat := [3, 4, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_4903426 : Nat := 118140960795 + 4903426 * 2 ^ 59
def prefixEnd_4903426 : Nat := 4983230072969 + 3 ^ 40 * 4903426 * 2
def baseEnd_4903426 : Nat := 839271463917745852308187

theorem tailTrace_4903426 : CollatzResearch.WordTrace tailWord_4903426 prefixEnd_4903426 839271463917745852308187 := by
  unfold tailWord_4903426
  simp only [CollatzResearch.WordTrace]
  refine ⟨44710659683433128833506533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119228425822488343556017421 44710659683433128833506533)
  ·
    refine ⟨8383248690643711656282475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44710659683433128833506533 8383248690643711656282475)
    ·
      refine ⟨12574873035965567484423713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8383248690643711656282475 12574873035965567484423713)
      ·
        refine ⟨9431154776974175613317785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12574873035965567484423713 9431154776974175613317785)
        ·
          refine ⟨7073366082730631709988339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9431154776974175613317785 7073366082730631709988339)
          ·
            refine ⟨10610049124095947564982509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073366082730631709988339 10610049124095947564982509)
            ·
              refine ⟨3978768421535980336868441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10610049124095947564982509 3978768421535980336868441)
              ·
                refine ⟨2984076316151985252651331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3978768421535980336868441 2984076316151985252651331)
                ·
                  refine ⟨4476114474227977878976997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984076316151985252651331 4476114474227977878976997)
                  ·
                    refine ⟨839271463917745852308187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4476114474227977878976997 839271463917745852308187)
                    ·
                      rfl

theorem cell23_4903426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_4903426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903426 prefixEnd_4903426 := by exact prefixLift 4903426
  have htrace : WordTrace (prefixWord ++ tailWord_4903426) baseStart_4903426 baseEnd_4903426 := by
    simpa [prefixWord, tailWord_4903426, baseEnd_4903426] using wordTrace_append hprefix tailTrace_4903426
  have hstable : (prefixWord ++ tailWord_4903426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903426).length < 2 ^ (prefixWord ++ tailWord_4903426).sum := by decide
  have hdescent : baseEnd_4903426 < baseStart_4903426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903441 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_4903441 : Nat := 118140960795 + 4903441 * 2 ^ 59
def prefixEnd_4903441 : Nat := 4983230072969 + 3 ^ 40 * 4903441 * 2
def baseEnd_4903441 : Nat := 2517822093963054998236991

theorem tailTrace_4903441 : CollatzResearch.WordTrace tailWord_4903441 prefixEnd_4903441 2517822093963054998236991 := by
  unfold tailWord_4903441
  simp only [CollatzResearch.WordTrace]
  refine ⟨178843185828678172895822177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119228790552452115263881451 178843185828678172895822177)
  ·
    refine ⟨134132389371508629671866633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178843185828678172895822177 134132389371508629671866633)
    ·
      refine ⟨100599292028631472253899975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134132389371508629671866633 100599292028631472253899975)
      ·
        refine ⟨150898938042947208380849963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100599292028631472253899975 150898938042947208380849963)
        ·
          refine ⟨226348407064420812571274945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150898938042947208380849963 226348407064420812571274945)
          ·
            refine ⟨169761305298315609428456209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226348407064420812571274945 169761305298315609428456209)
            ·
              refine ⟨127320978973736707071342157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169761305298315609428456209 127320978973736707071342157)
              ·
                refine ⟨47745367115151265151753309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127320978973736707071342157 47745367115151265151753309)
                ·
                  refine ⟨17904512668181724431907491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47745367115151265151753309 17904512668181724431907491)
                  ·
                    refine ⟨26856769002272586647861237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17904512668181724431907491 26856769002272586647861237)
                    ·
                      refine ⟨2517822093963054998236991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26856769002272586647861237 2517822093963054998236991)
                      ·
                        rfl

theorem cell23_4903441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_4903441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903441 prefixEnd_4903441 := by exact prefixLift 4903441
  have htrace : WordTrace (prefixWord ++ tailWord_4903441) baseStart_4903441 baseEnd_4903441 := by
    simpa [prefixWord, tailWord_4903441, baseEnd_4903441] using wordTrace_append hprefix tailTrace_4903441
  have hstable : (prefixWord ++ tailWord_4903441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903441).length < 2 ^ (prefixWord ++ tailWord_4903441).sum := by decide
  have hdescent : baseEnd_4903441 < baseStart_4903441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903451 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 4]
def baseStart_4903451 : Nat := 118140960795 + 4903451 * 2 ^ 59
def prefixEnd_4903451 : Nat := 4983230072969 + 3 ^ 40 * 4903451 * 2
def baseEnd_4903451 : Nat := 2517827228769599959111945

theorem tailTrace_4903451 : CollatzResearch.WordTrace tailWord_4903451 prefixEnd_4903451 2517827228769599959111945 := by
  unfold tailWord_4903451
  simp only [CollatzResearch.WordTrace]
  refine ⟨178843550558641944603686207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119229033705761296402457471 178843550558641944603686207)
  ·
    refine ⟨268265325837962916905529311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178843550558641944603686207 268265325837962916905529311)
    ·
      refine ⟨402397988756944375358293967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268265325837962916905529311 402397988756944375358293967)
      ·
        refine ⟨603596983135416563037440951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402397988756944375358293967 603596983135416563037440951)
        ·
          refine ⟨905395474703124844556161427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603596983135416563037440951 905395474703124844556161427)
          ·
            refine ⟨1358093212054687266834242141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905395474703124844556161427 1358093212054687266834242141)
            ·
              refine ⟨509284954520507725062840803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1358093212054687266834242141 509284954520507725062840803)
              ·
                refine ⟨763927431780761587594261205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509284954520507725062840803 763927431780761587594261205)
                ·
                  refine ⟨17904549182361599709240497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 763927431780761587594261205 17904549182361599709240497)
                  ·
                    refine ⟨13428411886771199781930373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17904549182361599709240497 13428411886771199781930373)
                    ·
                      refine ⟨2517827228769599959111945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13428411886771199781930373 2517827228769599959111945)
                      ·
                        rfl

theorem cell23_4903451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 4].length) (baseStart_4903451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903451 prefixEnd_4903451 := by exact prefixLift 4903451
  have htrace : WordTrace (prefixWord ++ tailWord_4903451) baseStart_4903451 baseEnd_4903451 := by
    simpa [prefixWord, tailWord_4903451, baseEnd_4903451] using wordTrace_append hprefix tailTrace_4903451
  have hstable : (prefixWord ++ tailWord_4903451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903451).length < 2 ^ (prefixWord ++ tailWord_4903451).sum := by decide
  have hdescent : baseEnd_4903451 < baseStart_4903451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903455 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 5, 2, 2]
def baseStart_4903455 : Nat := 118140960795 + 4903455 * 2 ^ 59
def prefixEnd_4903455 : Nat := 4983230072969 + 3 ^ 40 * 4903455 * 2
def baseEnd_4903455 : Nat := 2517829282692217943461927

theorem tailTrace_4903455 : CollatzResearch.WordTrace tailWord_4903455 prefixEnd_4903455 2517829282692217943461927 := by
  unfold tailWord_4903455
  simp only [CollatzResearch.WordTrace]
  refine ⟨178843696450627453286831819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119229130967084968857887879 178843696450627453286831819)
  ·
    refine ⟨268265544675941179930247729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178843696450627453286831819 268265544675941179930247729)
    ·
      refine ⟨201199158506955884947685797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268265544675941179930247729 201199158506955884947685797)
      ·
        refine ⟨37724842220054228427691087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201199158506955884947685797 37724842220054228427691087)
        ·
          refine ⟨56587263330081342641536631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37724842220054228427691087 56587263330081342641536631)
          ·
            refine ⟨84880894995122013962304947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56587263330081342641536631 84880894995122013962304947)
            ·
              refine ⟨127321342492683020943457421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84880894995122013962304947 127321342492683020943457421)
              ·
                refine ⟨47745503434756132853796533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127321342492683020943457421 47745503434756132853796533)
                ·
                  refine ⟨4476140947008387455043425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47745503434756132853796533 4476140947008387455043425)
                  ·
                    refine ⟨3357105710256290591282569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4476140947008387455043425 3357105710256290591282569)
                    ·
                      refine ⟨2517829282692217943461927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357105710256290591282569 2517829282692217943461927)
                      ·
                        rfl

theorem cell23_4903455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_4903455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903455 prefixEnd_4903455 := by exact prefixLift 4903455
  have htrace : WordTrace (prefixWord ++ tailWord_4903455) baseStart_4903455 baseEnd_4903455 := by
    simpa [prefixWord, tailWord_4903455, baseEnd_4903455] using wordTrace_append hprefix tailTrace_4903455
  have hstable : (prefixWord ++ tailWord_4903455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903455).length < 2 ^ (prefixWord ++ tailWord_4903455).sum := by decide
  have hdescent : baseEnd_4903455 < baseStart_4903455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903461 : List Nat := [1, 3, 1, 2, 2, 1, 4, 9]
def baseStart_4903461 : Nat := 118140960795 + 4903461 * 2 ^ 59
def prefixEnd_4903461 : Nat := 4983230072969 + 3 ^ 40 * 4903461 * 2
def baseEnd_4903461 : Nat := 93253050502820182221737

theorem tailTrace_4903461 : CollatzResearch.WordTrace tailWord_4903461 prefixEnd_4903461 93253050502820182221737 := by
  unfold tailWord_4903461
  simp only [CollatzResearch.WordTrace]
  refine ⟨178843915288605716311550237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119229276859070477541033491 178843915288605716311550237)
  ·
    refine ⟨67066468233227143616831339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178843915288605716311550237 67066468233227143616831339)
    ·
      refine ⟨100599702349840715425247009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67066468233227143616831339 100599702349840715425247009)
      ·
        refine ⟨75449776762380536568935257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100599702349840715425247009 75449776762380536568935257)
        ·
          refine ⟨56587332571785402426701443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75449776762380536568935257 56587332571785402426701443)
          ·
            refine ⟨84880998857678103640052165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56587332571785402426701443 84880998857678103640052165)
            ·
              refine ⟨15915187285814644432509781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84880998857678103640052165 15915187285814644432509781)
              ·
                refine ⟨93253050502820182221737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15915187285814644432509781 93253050502820182221737)
                ·
                  rfl

theorem cell23_4903461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 9].length) (baseStart_4903461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903461 prefixEnd_4903461 := by exact prefixLift 4903461
  have htrace : WordTrace (prefixWord ++ tailWord_4903461) baseStart_4903461 baseEnd_4903461 := by
    simpa [prefixWord, tailWord_4903461, baseEnd_4903461] using wordTrace_append hprefix tailTrace_4903461
  have hstable : (prefixWord ++ tailWord_4903461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903461).length < 2 ^ (prefixWord ++ tailWord_4903461).sum := by decide
  have hdescent : baseEnd_4903461 < baseStart_4903461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903478 : List Nat := [5, 1, 2, 1, 2, 12]
def baseStart_4903478 : Nat := 118140960795 + 4903478 * 2 ^ 59
def prefixEnd_4903478 : Nat := 4983230072969 + 3 ^ 40 * 4903478 * 2
def baseEnd_4903478 : Nat := 10361485978383832730347

theorem tailTrace_4903478 : CollatzResearch.WordTrace tailWord_4903478 prefixEnd_4903478 10361485978383832730347 := by
  unfold tailWord_4903478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11177783458096508013432443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119229690219696085476612725 11177783458096508013432443)
  ·
    refine ⟨16766675187144762020148665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11177783458096508013432443 16766675187144762020148665)
    ·
      refine ⟨12575006390358571515111499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16766675187144762020148665 12575006390358571515111499)
      ·
        refine ⟨18862509585537857272667249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12575006390358571515111499 18862509585537857272667249)
        ·
          refine ⟨14146882189153392954500437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18862509585537857272667249 14146882189153392954500437)
          ·
            refine ⟨10361485978383832730347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14146882189153392954500437 10361485978383832730347)
            ·
              rfl

theorem cell23_4903478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 12].length) (baseStart_4903478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903478 prefixEnd_4903478 := by exact prefixLift 4903478
  have htrace : WordTrace (prefixWord ++ tailWord_4903478) baseStart_4903478 baseEnd_4903478 := by
    simpa [prefixWord, tailWord_4903478, baseEnd_4903478] using wordTrace_append hprefix tailTrace_4903478
  have hstable : (prefixWord ++ tailWord_4903478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903478).length < 2 ^ (prefixWord ++ tailWord_4903478).sum := by decide
  have hdescent : baseEnd_4903478 < baseStart_4903478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903505 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_4903505 : Nat := 118140960795 + 4903505 * 2 ^ 59
def prefixEnd_4903505 : Nat := 4983230072969 + 3 ^ 40 * 4903505 * 2
def baseEnd_4903505 : Nat := 2517854956724942747836697

theorem tailTrace_4903505 : CollatzResearch.WordTrace tailWord_4903505 prefixEnd_4903505 2517854956724942747836697 := by
  unfold tailWord_4903505
  simp only [CollatzResearch.WordTrace]
  refine ⟨178845520100446311826151969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119230346733630874550767979 178845520100446311826151969)
  ·
    refine ⟨134134140075334733869613977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178845520100446311826151969 134134140075334733869613977)
    ·
      refine ⟨100600605056501050402210483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134134140075334733869613977 100600605056501050402210483)
      ·
        refine ⟨150900907584751575603315725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100600605056501050402210483 150900907584751575603315725)
        ·
          refine ⟨56587840344281840851243397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150900907584751575603315725 56587840344281840851243397)
          ·
            refine ⟨10610220064552845159608137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56587840344281840851243397 10610220064552845159608137)
            ·
              refine ⟨7957665048414633869706103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10610220064552845159608137 7957665048414633869706103)
              ·
                refine ⟨11936497572621950804559155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7957665048414633869706103 11936497572621950804559155)
                ·
                  refine ⟨17904746358932926206838733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11936497572621950804559155 17904746358932926206838733)
                  ·
                    refine ⟨6714279884599847327564525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17904746358932926206838733 6714279884599847327564525)
                    ·
                      refine ⟨2517854956724942747836697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6714279884599847327564525 2517854956724942747836697)
                      ·
                        rfl

theorem cell23_4903505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_4903505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903505 prefixEnd_4903505 := by exact prefixLift 4903505
  have htrace : WordTrace (prefixWord ++ tailWord_4903505) baseStart_4903505 baseEnd_4903505 := by
    simpa [prefixWord, tailWord_4903505, baseEnd_4903505] using wordTrace_append hprefix tailTrace_4903505
  have hstable : (prefixWord ++ tailWord_4903505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903505).length < 2 ^ (prefixWord ++ tailWord_4903505).sum := by decide
  have hdescent : baseEnd_4903505 < baseStart_4903505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903548 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_4903548 : Nat := 118140960795 + 4903548 * 2 ^ 59
def prefixEnd_4903548 : Nat := 4983230072969 + 3 ^ 40 * 4903548 * 2
def baseEnd_4903548 : Nat := 2517877036393086079598999

theorem tailTrace_4903548 : CollatzResearch.WordTrace tailWord_4903548 prefixEnd_4903548 2517877036393086079598999 := by
  unfold tailWord_4903548
  simp only [CollatzResearch.WordTrace]
  refine ⟨89423544219645265084983649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119231392292860353446644865 89423544219645265084983649)
  ·
    refine ⟨67067658164733948813737737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89423544219645265084983649 67067658164733948813737737)
    ·
      refine ⟨50300743623550461610303303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67067658164733948813737737 50300743623550461610303303)
      ·
        refine ⟨75451115435325692415454955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50300743623550461610303303 75451115435325692415454955)
        ·
          refine ⟨113176673152988538623182433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75451115435325692415454955 113176673152988538623182433)
          ·
            refine ⟨84882504864741403967386825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113176673152988538623182433 84882504864741403967386825)
            ·
              refine ⟨63661878648556052975540119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84882504864741403967386825 63661878648556052975540119)
              ·
                refine ⟨95492817972834079463310179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63661878648556052975540119 95492817972834079463310179)
                ·
                  refine ⟨143239226959251119194965269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95492817972834079463310179 143239226959251119194965269)
                  ·
                    refine ⟨6714338763714896212263997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 143239226959251119194965269 6714338763714896212263997)
                    ·
                      refine ⟨2517877036393086079598999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6714338763714896212263997 2517877036393086079598999)
                      ·
                        rfl

theorem cell23_4903548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_4903548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903548 prefixEnd_4903548 := by exact prefixLift 4903548
  have htrace : WordTrace (prefixWord ++ tailWord_4903548) baseStart_4903548 baseEnd_4903548 := by
    simpa [prefixWord, tailWord_4903548, baseEnd_4903548] using wordTrace_append hprefix tailTrace_4903548
  have hstable : (prefixWord ++ tailWord_4903548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903548).length < 2 ^ (prefixWord ++ tailWord_4903548).sum := by decide
  have hdescent : baseEnd_4903548 < baseStart_4903548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903648 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_4903648 : Nat := 118140960795 + 4903648 * 2 ^ 59
def prefixEnd_4903648 : Nat := 4983230072969 + 3 ^ 40 * 4903648 * 2
def baseEnd_4903648 : Nat := 2517928384458535688348539

theorem tailTrace_4903648 : CollatzResearch.WordTrace tailWord_4903648 prefixEnd_4903648 2517928384458535688348539 := by
  unfold tailWord_4903648
  simp only [CollatzResearch.WordTrace]
  refine ⟨89425367869464123624303799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119233823825952164832405065 89425367869464123624303799)
  ·
    refine ⟨134138051804196185436455699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89425367869464123624303799 134138051804196185436455699)
    ·
      refine ⟨201207077706294278154683549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134138051804196185436455699 201207077706294278154683549)
      ·
        refine ⟨75452654139860354308006331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201207077706294278154683549 75452654139860354308006331)
        ·
          refine ⟨113178981209790531462009497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75452654139860354308006331 113178981209790531462009497)
          ·
            refine ⟨84884235907342898596507123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113178981209790531462009497 84884235907342898596507123)
            ·
              refine ⟨127326353861014347894760685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84884235907342898596507123 127326353861014347894760685)
              ·
                refine ⟨47747382697880380460535257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127326353861014347894760685 47747382697880380460535257)
                ·
                  refine ⟨35810537023410285345401443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47747382697880380460535257 35810537023410285345401443)
                  ·
                    refine ⟨53715805535115428018102165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35810537023410285345401443 53715805535115428018102165)
                    ·
                      refine ⟨2517928384458535688348539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53715805535115428018102165 2517928384458535688348539)
                      ·
                        rfl

theorem cell23_4903648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_4903648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903648 prefixEnd_4903648 := by exact prefixLift 4903648
  have htrace : WordTrace (prefixWord ++ tailWord_4903648) baseStart_4903648 baseEnd_4903648 := by
    simpa [prefixWord, tailWord_4903648, baseEnd_4903648] using wordTrace_append hprefix tailTrace_4903648
  have hstable : (prefixWord ++ tailWord_4903648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903648).length < 2 ^ (prefixWord ++ tailWord_4903648).sum := by decide
  have hdescent : baseEnd_4903648 < baseStart_4903648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903762 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_4903762 : Nat := 118140960795 + 4903762 * 2 ^ 59
def prefixEnd_4903762 : Nat := 4983230072969 + 3 ^ 40 * 4903762 * 2
def baseEnd_4903762 : Nat := 2517986921253148242323015

theorem tailTrace_4903762 : CollatzResearch.WordTrace tailWord_4903762 prefixEnd_4903762 2517986921253148242323015 := by
  unfold tailWord_4903762
  simp only [CollatzResearch.WordTrace]
  refine ⟨44713723415128811179564385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119236595773676829812171693 44713723415128811179564385)
  ·
    refine ⟨33535292561346608384673289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44713723415128811179564385 33535292561346608384673289)
    ·
      refine ⟨25151469421009956288504967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33535292561346608384673289 25151469421009956288504967)
      ·
        refine ⟨37727204131514934432757451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25151469421009956288504967 37727204131514934432757451)
        ·
          refine ⟨56590806197272401649136177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37727204131514934432757451 56590806197272401649136177)
          ·
            refine ⟨42443104647954301236852133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56590806197272401649136177 42443104647954301236852133)
            ·
              refine ⟨7958082121491431481909775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42443104647954301236852133 7958082121491431481909775)
              ·
                refine ⟨11937123182237147222864663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7958082121491431481909775 11937123182237147222864663)
                ·
                  refine ⟨17905684773355720834296995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11937123182237147222864663 17905684773355720834296995)
                  ·
                    refine ⟨26858527160033581251445493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17905684773355720834296995 26858527160033581251445493)
                    ·
                      refine ⟨2517986921253148242323015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26858527160033581251445493 2517986921253148242323015)
                      ·
                        rfl

theorem cell23_4903762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_4903762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903762 prefixEnd_4903762 := by exact prefixLift 4903762
  have htrace : WordTrace (prefixWord ++ tailWord_4903762) baseStart_4903762 baseEnd_4903762 := by
    simpa [prefixWord, tailWord_4903762, baseEnd_4903762] using wordTrace_append hprefix tailTrace_4903762
  have hstable : (prefixWord ++ tailWord_4903762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903762).length < 2 ^ (prefixWord ++ tailWord_4903762).sum := by decide
  have hdescent : baseEnd_4903762 < baseStart_4903762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903772 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4903772 : Nat := 118140960795 + 4903772 * 2 ^ 59
def prefixEnd_4903772 : Nat := 4983230072969 + 3 ^ 40 * 4903772 * 2
def baseEnd_4903772 : Nat := 2517992056059693203197969

theorem tailTrace_4903772 : CollatzResearch.WordTrace tailWord_4903772 prefixEnd_4903772 2517992056059693203197969 := by
  unfold tailWord_4903772
  simp only [CollatzResearch.WordTrace]
  refine ⟨89427629195239508213060785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119236838926986010950747713 89427629195239508213060785)
  ·
    refine ⟨67070721896429631159795589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89427629195239508213060785 67070721896429631159795589)
    ·
      refine ⟨12575760355580555842461673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67070721896429631159795589 12575760355580555842461673)
      ·
        refine ⟨9431820266685416881846255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12575760355580555842461673 9431820266685416881846255)
        ·
          refine ⟨14147730400028125322769383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9431820266685416881846255 14147730400028125322769383)
          ·
            refine ⟨21221595600042187984154075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14147730400028125322769383 21221595600042187984154075)
            ·
              refine ⟨31832393400063281976231113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21221595600042187984154075 31832393400063281976231113)
              ·
                refine ⟨23874295050047461482173335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31832393400063281976231113 23874295050047461482173335)
                ·
                  refine ⟨35811442575071192223260003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23874295050047461482173335 35811442575071192223260003)
                  ·
                    refine ⟨53717163862606788334890005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35811442575071192223260003 53717163862606788334890005)
                    ·
                      refine ⟨2517992056059693203197969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53717163862606788334890005 2517992056059693203197969)
                      ·
                        rfl

theorem cell23_4903772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4903772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903772 prefixEnd_4903772 := by exact prefixLift 4903772
  have htrace : WordTrace (prefixWord ++ tailWord_4903772) baseStart_4903772 baseEnd_4903772 := by
    simpa [prefixWord, tailWord_4903772, baseEnd_4903772] using wordTrace_append hprefix tailTrace_4903772
  have hstable : (prefixWord ++ tailWord_4903772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903772).length < 2 ^ (prefixWord ++ tailWord_4903772).sum := by decide
  have hdescent : baseEnd_4903772 < baseStart_4903772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903805 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_4903805 : Nat := 118140960795 + 4903805 * 2 ^ 59
def prefixEnd_4903805 : Nat := 4983230072969 + 3 ^ 40 * 4903805 * 2
def baseEnd_4903805 : Nat := 2518009000921291574085317

theorem tailTrace_4903805 : CollatzResearch.WordTrace tailWord_4903805 prefixEnd_4903805 2518009000921291574085317 := by
  unfold tailWord_4903805
  simp only [CollatzResearch.WordTrace]
  refine ⟨178856461999359463062072869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119237641332906308708048579 178856461999359463062072869)
  ·
    refine ⟨33535586624879899324138663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178856461999359463062072869 33535586624879899324138663)
    ·
      refine ⟨50303379937319848986207995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33535586624879899324138663 50303379937319848986207995)
      ·
        refine ⟨75455069905979773479311993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50303379937319848986207995 75455069905979773479311993)
        ·
          refine ⟨56591302429484830109483995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75455069905979773479311993 56591302429484830109483995)
          ·
            refine ⟨84886953644227245164225993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56591302429484830109483995 84886953644227245164225993)
            ·
              refine ⟨63665215233170433873169495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84886953644227245164225993 63665215233170433873169495)
              ·
                refine ⟨95497822849755650809754243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63665215233170433873169495 95497822849755650809754243)
                ·
                  refine ⟨143246734274633476214631365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95497822849755650809754243 143246734274633476214631365)
                  ·
                    refine ⟨26858762676493776790243381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143246734274633476214631365 26858762676493776790243381)
                    ·
                      refine ⟨2518009000921291574085317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26858762676493776790243381 2518009000921291574085317)
                      ·
                        rfl

theorem cell23_4903805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_4903805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903805 prefixEnd_4903805 := by exact prefixLift 4903805
  have htrace : WordTrace (prefixWord ++ tailWord_4903805) baseStart_4903805 baseEnd_4903805 := by
    simpa [prefixWord, tailWord_4903805, baseEnd_4903805] using wordTrace_append hprefix tailTrace_4903805
  have hstable : (prefixWord ++ tailWord_4903805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903805).length < 2 ^ (prefixWord ++ tailWord_4903805).sum := by decide
  have hdescent : baseEnd_4903805 < baseStart_4903805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903806 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4903806 : Nat := 118140960795 + 4903806 * 2 ^ 59
def prefixEnd_4903806 : Nat := 4983230072969 + 3 ^ 40 * 4903806 * 2
def baseEnd_4903806 : Nat := 2518009514401946070172813

theorem tailTrace_4903806 : CollatzResearch.WordTrace tailWord_4903806 prefixEnd_4903806 2518009514401946070172813 := by
  unfold tailWord_4903806
  simp only [CollatzResearch.WordTrace]
  refine ⟨22357062309044480029107409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119237665648237226821906181 22357062309044480029107409)
  ·
    refine ⟨16767796731783360021830557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22357062309044480029107409 16767796731783360021830557)
    ·
      refine ⟨6287923774418760008186459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16767796731783360021830557 6287923774418760008186459)
      ·
        refine ⟨9431885661628140012279689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287923774418760008186459 9431885661628140012279689)
        ·
          refine ⟨7073914246221105009209767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9431885661628140012279689 7073914246221105009209767)
          ·
            refine ⟨10610871369331657513814651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073914246221105009209767 10610871369331657513814651)
            ·
              refine ⟨15916307053997486270721977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10610871369331657513814651 15916307053997486270721977)
              ·
                refine ⟨11937230290498114703041483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15916307053997486270721977 11937230290498114703041483)
                ·
                  refine ⟨17905845435747172054562225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11937230290498114703041483 17905845435747172054562225)
                  ·
                    refine ⟨13429384076810379040921669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17905845435747172054562225 13429384076810379040921669)
                    ·
                      refine ⟨2518009514401946070172813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13429384076810379040921669 2518009514401946070172813)
                      ·
                        rfl

theorem cell23_4903806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4903806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903806 prefixEnd_4903806 := by exact prefixLift 4903806
  have htrace : WordTrace (prefixWord ++ tailWord_4903806) baseStart_4903806 baseEnd_4903806 := by
    simpa [prefixWord, tailWord_4903806, baseEnd_4903806] using wordTrace_append hprefix tailTrace_4903806
  have hstable : (prefixWord ++ tailWord_4903806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903806).length < 2 ^ (prefixWord ++ tailWord_4903806).sum := by decide
  have hdescent : baseEnd_4903806 < baseStart_4903806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903810 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4903810 : Nat := 118140960795 + 4903810 * 2 ^ 59
def prefixEnd_4903810 : Nat := 4983230072969 + 3 ^ 40 * 4903810 * 2
def baseEnd_4903810 : Nat := 2518011568324564054522795

theorem tailTrace_4903810 : CollatzResearch.WordTrace tailWord_4903810 prefixEnd_4903810 2518011568324564054522795 := by
  unfold tailWord_4903810
  simp only [CollatzResearch.WordTrace]
  refine ⟨44714161091085337229001221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119237762909560899277336589 44714161091085337229001221)
  ·
    refine ⟨8383905204578500730437729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44714161091085337229001221 8383905204578500730437729)
    ·
      refine ⟨6287928903433875547828297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8383905204578500730437729 6287928903433875547828297)
      ·
        refine ⟨4715946677575406660871223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6287928903433875547828297 4715946677575406660871223)
        ·
          refine ⟨7073920016363109991306835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715946677575406660871223 7073920016363109991306835)
          ·
            refine ⟨10610880024544664986960253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073920016363109991306835 10610880024544664986960253)
            ·
              refine ⟨3979080009204249370110095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10610880024544664986960253 3979080009204249370110095)
              ·
                refine ⟨5968620013806374055165143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979080009204249370110095 5968620013806374055165143)
                ·
                  refine ⟨8952930020709561082747715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968620013806374055165143 8952930020709561082747715)
                  ·
                    refine ⟨13429395031064341624121573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8952930020709561082747715 13429395031064341624121573)
                    ·
                      refine ⟨2518011568324564054522795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13429395031064341624121573 2518011568324564054522795)
                      ·
                        rfl

theorem cell23_4903810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4903810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903810 prefixEnd_4903810 := by exact prefixLift 4903810
  have htrace : WordTrace (prefixWord ++ tailWord_4903810) baseStart_4903810 baseEnd_4903810 := by
    simpa [prefixWord, tailWord_4903810, baseEnd_4903810] using wordTrace_append hprefix tailTrace_4903810
  have hstable : (prefixWord ++ tailWord_4903810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903810).length < 2 ^ (prefixWord ++ tailWord_4903810).sum := by decide
  have hdescent : baseEnd_4903810 < baseStart_4903810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903819 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 1, 3, 2]
def baseStart_4903819 : Nat := 118140960795 + 4903819 * 2 ^ 59
def prefixEnd_4903819 : Nat := 4983230072969 + 3 ^ 40 * 4903819 * 2
def baseEnd_4903819 : Nat := 2518016189650454519310253

theorem tailTrace_4903819 : CollatzResearch.WordTrace tailWord_4903819 prefixEnd_4903819 2518016189650454519310253 := by
  unfold tailWord_4903819
  simp only [CollatzResearch.WordTrace]
  refine ⟨178856972621308743453082511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119237981747539162302055007 178856972621308743453082511)
  ·
    refine ⟨268285458931963115179623767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178856972621308743453082511 268285458931963115179623767)
    ·
      refine ⟨402428188397944672769435651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268285458931963115179623767 402428188397944672769435651)
      ·
        refine ⟨603642282596917009154153477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402428188397944672769435651 603642282596917009154153477)
        ·
          refine ⟨113182927986921939216403777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 603642282596917009154153477 113182927986921939216403777)
          ·
            refine ⟨84887195990191454412302833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113182927986921939216403777 84887195990191454412302833)
            ·
              refine ⟨63665396992643590809227125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84887195990191454412302833 63665396992643590809227125)
              ·
                refine ⟨5968630968060336638365043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63665396992643590809227125 5968630968060336638365043)
                ·
                  refine ⟨8952946452090504957547565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968630968060336638365043 8952946452090504957547565)
                  ·
                    refine ⟨3357354919533939359080337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8952946452090504957547565 3357354919533939359080337)
                    ·
                      refine ⟨2518016189650454519310253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357354919533939359080337 2518016189650454519310253)
                      ·
                        rfl

theorem cell23_4903819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 3, 2].length) (baseStart_4903819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903819 prefixEnd_4903819 := by exact prefixLift 4903819
  have htrace : WordTrace (prefixWord ++ tailWord_4903819) baseStart_4903819 baseEnd_4903819 := by
    simpa [prefixWord, tailWord_4903819, baseEnd_4903819] using wordTrace_append hprefix tailTrace_4903819
  have hstable : (prefixWord ++ tailWord_4903819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903819).length < 2 ^ (prefixWord ++ tailWord_4903819).sum := by decide
  have hdescent : baseEnd_4903819 < baseStart_4903819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903825 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 2, 6]
def baseStart_4903825 : Nat := 118140960795 + 4903825 * 2 ^ 59
def prefixEnd_4903825 : Nat := 4983230072969 + 3 ^ 40 * 4903825 * 2
def baseEnd_4903825 : Nat := 839339756844793831945075

theorem tailTrace_4903825 : CollatzResearch.WordTrace tailWord_4903825 prefixEnd_4903825 839339756844793831945075 := by
  unfold tailWord_4903825
  simp only [CollatzResearch.WordTrace]
  refine ⟨178857191459287006477800929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119238127639524670985200619 178857191459287006477800929)
  ·
    refine ⟨134142893594465254858350697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178857191459287006477800929 134142893594465254858350697)
    ·
      refine ⟨100607170195848941143763023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134142893594465254858350697 100607170195848941143763023)
      ·
        refine ⟨150910755293773411715644535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100607170195848941143763023 150910755293773411715644535)
        ·
          refine ⟨226366132940660117573466803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150910755293773411715644535 226366132940660117573466803)
          ·
            refine ⟨339549199410990176360200205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226366132940660117573466803 339549199410990176360200205)
            ·
              refine ⟨127330949779121316135075077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339549199410990176360200205 127330949779121316135075077)
              ·
                refine ⟨23874553083585246775326577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127330949779121316135075077 23874553083585246775326577)
                ·
                  refine ⟨17905914812688935081494933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23874553083585246775326577 17905914812688935081494933)
                  ·
                    refine ⟨839339756844793831945075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17905914812688935081494933 839339756844793831945075)
                    ·
                      rfl

theorem cell23_4903825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_4903825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903825 prefixEnd_4903825 := by exact prefixLift 4903825
  have htrace : WordTrace (prefixWord ++ tailWord_4903825) baseStart_4903825 baseEnd_4903825 := by
    simpa [prefixWord, tailWord_4903825, baseEnd_4903825] using wordTrace_append hprefix tailTrace_4903825
  have hstable : (prefixWord ++ tailWord_4903825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903825).length < 2 ^ (prefixWord ++ tailWord_4903825).sum := by decide
  have hdescent : baseEnd_4903825 < baseStart_4903825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903842 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_4903842 : Nat := 118140960795 + 4903842 * 2 ^ 59
def prefixEnd_4903842 : Nat := 4983230072969 + 3 ^ 40 * 4903842 * 2
def baseEnd_4903842 : Nat := 839342666568502643107549

theorem tailTrace_4903842 : CollatzResearch.WordTrace tailWord_4903842 prefixEnd_4903842 839342666568502643107549 := by
  unfold tailWord_4903842
  simp only [CollatzResearch.WordTrace]
  refine ⟨44714452875056354595292445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119238541000150278920779853 44714452875056354595292445)
  ·
    refine ⟨16767919828146132973234667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44714452875056354595292445 16767919828146132973234667)
    ·
      refine ⟨25151879742219199459852001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16767919828146132973234667 25151879742219199459852001)
      ·
        refine ⟨18863909806664399594889001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25151879742219199459852001 18863909806664399594889001)
        ·
          refine ⟨14147932354998299696166751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18863909806664399594889001 14147932354998299696166751)
          ·
            refine ⟨21221898532497449544250127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14147932354998299696166751 21221898532497449544250127)
            ·
              refine ⟨31832847798746174316375191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21221898532497449544250127 31832847798746174316375191)
              ·
                refine ⟨47749271698119261474562787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31832847798746174316375191 47749271698119261474562787)
                ·
                  refine ⟨71623907547178892211844181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47749271698119261474562787 71623907547178892211844181)
                  ·
                    refine ⟨839342666568502643107549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71623907547178892211844181 839342666568502643107549)
                    ·
                      rfl

theorem cell23_4903842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_4903842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903842 prefixEnd_4903842 := by exact prefixLift 4903842
  have htrace : WordTrace (prefixWord ++ tailWord_4903842) baseStart_4903842 baseEnd_4903842 := by
    simpa [prefixWord, tailWord_4903842, baseEnd_4903842] using wordTrace_append hprefix tailTrace_4903842
  have hstable : (prefixWord ++ tailWord_4903842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903842).length < 2 ^ (prefixWord ++ tailWord_4903842).sum := by decide
  have hdescent : baseEnd_4903842 < baseStart_4903842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903849 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 1, 4, 2]
def baseStart_4903849 : Nat := 118140960795 + 4903849 * 2 ^ 59
def prefixEnd_4903849 : Nat := 4983230072969 + 3 ^ 40 * 4903849 * 2
def baseEnd_4903849 : Nat := 2518031594070089401935115

theorem tailTrace_4903849 : CollatzResearch.WordTrace tailWord_4903849 prefixEnd_4903849 2518031594070089401935115 := by
  unfold tailWord_4903849
  simp only [CollatzResearch.WordTrace]
  refine ⟨178858066811200058576674601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119238711207466705717783067 178858066811200058576674601)
  ·
    refine ⟨134143550108400043932505951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178858066811200058576674601 134143550108400043932505951)
    ·
      refine ⟨201215325162600065898758927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134143550108400043932505951 201215325162600065898758927)
      ·
        refine ⟨301822987743900098848138391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201215325162600065898758927 301822987743900098848138391)
        ·
          refine ⟨452734481615850148272207587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301822987743900098848138391 452734481615850148272207587)
          ·
            refine ⟨679101722423775222408311381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452734481615850148272207587 679101722423775222408311381)
            ·
              refine ⟨7958223309653615887597399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 679101722423775222408311381 7958223309653615887597399)
              ·
                refine ⟨11937334964480423831396099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7958223309653615887597399 11937334964480423831396099)
                ·
                  refine ⟨17906002446720635747094149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11937334964480423831396099 17906002446720635747094149)
                  ·
                    refine ⟨3357375458760119202580153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17906002446720635747094149 3357375458760119202580153)
                    ·
                      refine ⟨2518031594070089401935115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357375458760119202580153 2518031594070089401935115)
                      ·
                        rfl

theorem cell23_4903849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 4, 2].length) (baseStart_4903849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903849 prefixEnd_4903849 := by exact prefixLift 4903849
  have htrace : WordTrace (prefixWord ++ tailWord_4903849) baseStart_4903849 baseEnd_4903849 := by
    simpa [prefixWord, tailWord_4903849, baseEnd_4903849] using wordTrace_append hprefix tailTrace_4903849
  have hstable : (prefixWord ++ tailWord_4903849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903849).length < 2 ^ (prefixWord ++ tailWord_4903849).sum := by decide
  have hdescent : baseEnd_4903849 < baseStart_4903849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903883 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 2, 2, 2]
def baseStart_4903883 : Nat := 118140960795 + 4903883 * 2 ^ 59
def prefixEnd_4903883 : Nat := 4983230072969 + 3 ^ 40 * 4903883 * 2
def baseEnd_4903883 : Nat := 2518049052412342268909959

theorem tailTrace_4903883 : CollatzResearch.WordTrace tailWord_4903883 prefixEnd_4903883 2518049052412342268909959 := by
  unfold tailWord_4903883
  simp only [CollatzResearch.WordTrace]
  refine ⟨178859306893076882383412303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119239537928717921588941535 178859306893076882383412303)
  ·
    refine ⟨268288960339615323575118455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178859306893076882383412303 268288960339615323575118455)
    ·
      refine ⟨402433440509422985362677683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268288960339615323575118455 402433440509422985362677683)
      ·
        refine ⟨603650160764134478044016525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402433440509422985362677683 603650160764134478044016525)
        ·
          refine ⟨226368810286550429266506197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 603650160764134478044016525 226368810286550429266506197)
          ·
            refine ⟨5305518991091025685933739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 226368810286550429266506197 5305518991091025685933739)
            ·
              refine ⟨7958278486636538528900609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5305518991091025685933739 7958278486636538528900609)
              ·
                refine ⟨5968708864977403896675457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7958278486636538528900609 5968708864977403896675457)
                ·
                  refine ⟨4476531648733052922506593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5968708864977403896675457 4476531648733052922506593)
                  ·
                    refine ⟨3357398736549789691879945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4476531648733052922506593 3357398736549789691879945)
                    ·
                      refine ⟨2518049052412342268909959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357398736549789691879945 2518049052412342268909959)
                      ·
                        rfl

theorem cell23_4903883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 2, 2].length) (baseStart_4903883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903883 prefixEnd_4903883 := by exact prefixLift 4903883
  have htrace : WordTrace (prefixWord ++ tailWord_4903883) baseStart_4903883 baseEnd_4903883 := by
    simpa [prefixWord, tailWord_4903883, baseEnd_4903883] using wordTrace_append hprefix tailTrace_4903883
  have hstable : (prefixWord ++ tailWord_4903883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903883).length < 2 ^ (prefixWord ++ tailWord_4903883).sum := by decide
  have hdescent : baseEnd_4903883 < baseStart_4903883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4903999 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 3, 5, 2]
def baseStart_4903999 : Nat := 118140960795 + 4903999 * 2 ^ 59
def prefixEnd_4903999 : Nat := 4983230072969 + 3 ^ 40 * 4903999 * 2
def baseEnd_4903999 : Nat := 2518108616168263815059425

theorem tailTrace_4903999 : CollatzResearch.WordTrace tailWord_4903999 prefixEnd_4903999 2518108616168263815059425 := by
  unfold tailWord_4903999
  simp only [CollatzResearch.WordTrace]
  refine ⟨178863537760656634194635051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119242358507104422796423367 178863537760656634194635051)
  ·
    refine ⟨268295306640984951291952577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178863537760656634194635051 268295306640984951291952577)
    ·
      refine ⟨201221479980738713468964433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268295306640984951291952577 201221479980738713468964433)
      ·
        refine ⟨150916109985554035101723325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201221479980738713468964433 150916109985554035101723325)
        ·
          refine ⟨56593541244582763163146247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150916109985554035101723325 56593541244582763163146247)
          ·
            refine ⟨84890311866874144744719371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56593541244582763163146247 84890311866874144744719371)
            ·
              refine ⟨127335467800311217117079057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84890311866874144744719371 127335467800311217117079057)
              ·
                refine ⟨95501600850233412837809293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127335467800311217117079057 95501600850233412837809293)
                ·
                  refine ⟨35813100318837529814178485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95501600850233412837809293 35813100318837529814178485)
                  ·
                    refine ⟨3357478154891018420079233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35813100318837529814178485 3357478154891018420079233)
                    ·
                      refine ⟨2518108616168263815059425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357478154891018420079233 2518108616168263815059425)
                      ·
                        rfl

theorem cell23_4903999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_4903999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4903999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4903999 prefixEnd_4903999 := by exact prefixLift 4903999
  have htrace : WordTrace (prefixWord ++ tailWord_4903999) baseStart_4903999 baseEnd_4903999 := by
    simpa [prefixWord, tailWord_4903999, baseEnd_4903999] using wordTrace_append hprefix tailTrace_4903999
  have hstable : (prefixWord ++ tailWord_4903999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4903999).length < 2 ^ (prefixWord ++ tailWord_4903999).sum := by decide
  have hdescent : baseEnd_4903999 < baseStart_4903999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4903999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904039 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 1, 6]
def baseStart_4904039 : Nat := 118140960795 + 4904039 * 2 ^ 59
def prefixEnd_4904039 : Nat := 4983230072969 + 3 ^ 40 * 4904039 * 2
def baseEnd_4904039 : Nat := 839376385131481219519747

theorem tailTrace_4904039 : CollatzResearch.WordTrace tailWord_4904039 prefixEnd_4904039 839376385131481219519747 := by
  unfold tailWord_4904039
  simp only [CollatzResearch.WordTrace]
  refine ⟨178864996680511721026091171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119243331120341147350727447 178864996680511721026091171)
  ·
    refine ⟨268297495020767581539136757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178864996680511721026091171 268297495020767581539136757)
    ·
      refine ⟨25152890158196960769294071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 268297495020767581539136757 25152890158196960769294071)
      ·
        refine ⟨37729335237295441153941107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25152890158196960769294071 37729335237295441153941107)
        ·
          refine ⟨56594002855943161730911661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37729335237295441153941107 56594002855943161730911661)
          ·
            refine ⟨21222751070978685649091873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56594002855943161730911661 21222751070978685649091873)
            ·
              refine ⟨15917063303234014236818905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21222751070978685649091873 15917063303234014236818905)
              ·
                refine ⟨11937797477425510677614179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15917063303234014236818905 11937797477425510677614179)
                ·
                  refine ⟨17906696216138266016421269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11937797477425510677614179 17906696216138266016421269)
                  ·
                    refine ⟨839376385131481219519747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17906696216138266016421269 839376385131481219519747)
                    ·
                      rfl

theorem cell23_4904039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_4904039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904039 prefixEnd_4904039 := by exact prefixLift 4904039
  have htrace : WordTrace (prefixWord ++ tailWord_4904039) baseStart_4904039 baseEnd_4904039 := by
    simpa [prefixWord, tailWord_4904039, baseEnd_4904039] using wordTrace_append hprefix tailTrace_4904039
  have hstable : (prefixWord ++ tailWord_4904039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904039).length < 2 ^ (prefixWord ++ tailWord_4904039).sum := by decide
  have hdescent : baseEnd_4904039 < baseStart_4904039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904049 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_4904049 : Nat := 118140960795 + 4904049 * 2 ^ 59
def prefixEnd_4904049 : Nat := 4983230072969 + 3 ^ 40 * 4904049 * 2
def baseEnd_4904049 : Nat := 2518134290200988619434195

theorem tailTrace_4904049 : CollatzResearch.WordTrace tailWord_4904049 prefixEnd_4904049 2518134290200988619434195 := by
  unfold tailWord_4904049
  simp only [CollatzResearch.WordTrace]
  refine ⟨178865361410475492733955201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119243574273650328489303467 178865361410475492733955201)
  ·
    refine ⟨134149021057856619550466401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178865361410475492733955201 134149021057856619550466401)
    ·
      refine ⟨100611765793392464662849801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134149021057856619550466401 100611765793392464662849801)
      ·
        refine ⟨75458824345044348497137351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100611765793392464662849801 75458824345044348497137351)
        ·
          refine ⟨113188236517566522745706027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75458824345044348497137351 113188236517566522745706027)
          ·
            refine ⟨169782354776349784118559041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113188236517566522745706027 169782354776349784118559041)
            ·
              refine ⟨127336766082262338088919281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169782354776349784118559041 127336766082262338088919281)
              ·
                refine ⟨95502574561696753566689461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127336766082262338088919281 95502574561696753566689461)
                ·
                  refine ⟨8953366365159070646877137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95502574561696753566689461 8953366365159070646877137)
                  ·
                    refine ⟨6715024773869302985157853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8953366365159070646877137 6715024773869302985157853)
                    ·
                      refine ⟨2518134290200988619434195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6715024773869302985157853 2518134290200988619434195)
                      ·
                        rfl

theorem cell23_4904049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_4904049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904049 prefixEnd_4904049 := by exact prefixLift 4904049
  have htrace : WordTrace (prefixWord ++ tailWord_4904049) baseStart_4904049 baseEnd_4904049 := by
    simpa [prefixWord, tailWord_4904049, baseEnd_4904049] using wordTrace_append hprefix tailTrace_4904049
  have hstable : (prefixWord ++ tailWord_4904049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904049).length < 2 ^ (prefixWord ++ tailWord_4904049).sum := by decide
  have hdescent : baseEnd_4904049 < baseStart_4904049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904056 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 2, 4]
def baseStart_4904056 : Nat := 118140960795 + 4904056 * 2 ^ 59
def prefixEnd_4904056 : Nat := 4983230072969 + 3 ^ 40 * 4904056 * 2
def baseEnd_4904056 : Nat := 839379294855190030682221

theorem tailTrace_4904056 : CollatzResearch.WordTrace tailWord_4904056 prefixEnd_4904056 839379294855190030682221 := by
  unfold tailWord_4904056
  simp only [CollatzResearch.WordTrace]
  refine ⟨89432808360725066464730011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119243744480966755286306681 89432808360725066464730011)
  ·
    refine ⟨134149212541087599697095017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89432808360725066464730011 134149212541087599697095017)
    ·
      refine ⟨100611909405815699772821263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134149212541087599697095017 100611909405815699772821263)
      ·
        refine ⟨150917864108723549659231895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100611909405815699772821263 150917864108723549659231895)
        ·
          refine ⟨226376796163085324488847843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150917864108723549659231895 226376796163085324488847843)
          ·
            refine ⟨339565194244627986733271765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226376796163085324488847843 339565194244627986733271765)
            ·
              refine ⟨7958559240108468439061057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 339565194244627986733271765 7958559240108468439061057)
              ·
                refine ⟨5968919430081351329295793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7958559240108468439061057 5968919430081351329295793)
                ·
                  refine ⟨4476689572561013496971845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5968919430081351329295793 4476689572561013496971845)
                  ·
                    refine ⟨839379294855190030682221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4476689572561013496971845 839379294855190030682221)
                    ·
                      rfl

theorem cell23_4904056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_4904056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904056 prefixEnd_4904056 := by exact prefixLift 4904056
  have htrace : WordTrace (prefixWord ++ tailWord_4904056) baseStart_4904056 baseEnd_4904056 := by
    simpa [prefixWord, tailWord_4904056, baseEnd_4904056] using wordTrace_append hprefix tailTrace_4904056
  have hstable : (prefixWord ++ tailWord_4904056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904056).length < 2 ^ (prefixWord ++ tailWord_4904056).sum := by decide
  have hdescent : baseEnd_4904056 < baseStart_4904056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904073 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 2, 4]
def baseStart_4904073 : Nat := 118140960795 + 4904073 * 2 ^ 59
def prefixEnd_4904073 : Nat := 4983230072969 + 3 ^ 40 * 4904073 * 2
def baseEnd_4904073 : Nat := 839382204578898841844695

theorem tailTrace_4904073 : CollatzResearch.WordTrace tailWord_4904073 prefixEnd_4904073 839382204578898841844695 := by
  unfold tailWord_4904073
  simp only [CollatzResearch.WordTrace]
  refine ⟨178866236762388544832828873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119244157841592363221885915 178866236762388544832828873)
  ·
    refine ⟨134149677571791408624621655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178866236762388544832828873 134149677571791408624621655)
    ·
      refine ⟨201224516357687112936932483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134149677571791408624621655 201224516357687112936932483)
      ·
        refine ⟨301836774536530669405398725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201224516357687112936932483 301836774536530669405398725)
        ·
          refine ⟨56594395225599500513512261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 301836774536530669405398725 56594395225599500513512261)
          ·
            refine ⟨10611449104799906346283549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56594395225599500513512261 10611449104799906346283549)
            ·
              refine ⟨3979293414299964879856331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10611449104799906346283549 3979293414299964879856331)
              ·
                refine ⟨5968940121449947319784497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979293414299964879856331 5968940121449947319784497)
                ·
                  refine ⟨4476705091087460489838373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5968940121449947319784497 4476705091087460489838373)
                  ·
                    refine ⟨839382204578898841844695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4476705091087460489838373 839382204578898841844695)
                    ·
                      rfl

theorem cell23_4904073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 4].length) (baseStart_4904073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904073 prefixEnd_4904073 := by exact prefixLift 4904073
  have htrace : WordTrace (prefixWord ++ tailWord_4904073) baseStart_4904073 baseEnd_4904073 := by
    simpa [prefixWord, tailWord_4904073, baseEnd_4904073] using wordTrace_append hprefix tailTrace_4904073
  have hstable : (prefixWord ++ tailWord_4904073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904073).length < 2 ^ (prefixWord ++ tailWord_4904073).sum := by decide
  have hdescent : baseEnd_4904073 < baseStart_4904073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904096 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 6, 1, 3]
def baseStart_4904096 : Nat := 118140960795 + 4904096 * 2 ^ 59
def prefixEnd_4904096 : Nat := 4983230072969 + 3 ^ 40 * 4904096 * 2
def baseEnd_4904096 : Nat := 2518158423791749935546479

theorem tailTrace_4904096 : CollatzResearch.WordTrace tailWord_4904096 prefixEnd_4904096 2518158423791749935546479 := by
  unfold tailWord_4904096
  simp only [CollatzResearch.WordTrace]
  refine ⟨89433537820652609880458071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119244717094203479840610761 89433537820652609880458071)
  ·
    refine ⟨134150306730978914820687107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89433537820652609880458071 134150306730978914820687107)
    ·
      refine ⟨201225460096468372231030661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134150306730978914820687107 201225460096468372231030661)
      ·
        refine ⟨37729773768087819793318249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201225460096468372231030661 37729773768087819793318249)
        ·
          refine ⟨28297330326065864844988687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37729773768087819793318249 28297330326065864844988687)
          ·
            refine ⟨42445995489098797267483031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28297330326065864844988687 42445995489098797267483031)
            ·
              refine ⟨63668993233648195901224547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42445995489098797267483031 63668993233648195901224547)
              ·
                refine ⟨95503489850472293851836821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63668993233648195901224547 95503489850472293851836821)
                ·
                  refine ⟨4476726086740888774304851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95503489850472293851836821 4476726086740888774304851)
                  ·
                    refine ⟨6715089130111333161457277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4476726086740888774304851 6715089130111333161457277)
                    ·
                      refine ⟨2518158423791749935546479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6715089130111333161457277 2518158423791749935546479)
                      ·
                        rfl

theorem cell23_4904096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_4904096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904096 prefixEnd_4904096 := by exact prefixLift 4904096
  have htrace : WordTrace (prefixWord ++ tailWord_4904096) baseStart_4904096 baseEnd_4904096 := by
    simpa [prefixWord, tailWord_4904096, baseEnd_4904096] using wordTrace_append hprefix tailTrace_4904096
  have hstable : (prefixWord ++ tailWord_4904096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904096).length < 2 ^ (prefixWord ++ tailWord_4904096).sum := by decide
  have hdescent : baseEnd_4904096 < baseStart_4904096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904113 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4904113 : Nat := 118140960795 + 4904113 * 2 ^ 59
def prefixEnd_4904113 : Nat := 4983230072969 + 3 ^ 40 * 4904113 * 2
def baseEnd_4904113 : Nat := 2518167152962876369033901

theorem tailTrace_4904113 : CollatzResearch.WordTrace tailWord_4904113 prefixEnd_4904113 2518167152962876369033901 := by
  unfold tailWord_4904113
  simp only [CollatzResearch.WordTrace]
  refine ⟨178867695682243631664284993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119245130454829087776189995 178867695682243631664284993)
  ·
    refine ⟨134150771761682723748213745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178867695682243631664284993 134150771761682723748213745)
    ·
      refine ⟨100613078821262042811160309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134150771761682723748213745 100613078821262042811160309)
      ·
        refine ⟨9432476139493316513546279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100613078821262042811160309 9432476139493316513546279)
        ·
          refine ⟨14148714209239974770319419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9432476139493316513546279 14148714209239974770319419)
          ·
            refine ⟨21223071313859962155479129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14148714209239974770319419 21223071313859962155479129)
            ·
              refine ⟨15917303485394971616609347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21223071313859962155479129 15917303485394971616609347)
              ·
                refine ⟨23875955228092457424914021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15917303485394971616609347 23875955228092457424914021)
                ·
                  refine ⟨4476741605267335767171379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23875955228092457424914021 4476741605267335767171379)
                  ·
                    refine ⟨6715112407901003650757069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4476741605267335767171379 6715112407901003650757069)
                    ·
                      refine ⟨2518167152962876369033901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6715112407901003650757069 2518167152962876369033901)
                      ·
                        rfl

theorem cell23_4904113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4904113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904113 prefixEnd_4904113 := by exact prefixLift 4904113
  have htrace : WordTrace (prefixWord ++ tailWord_4904113) baseStart_4904113 baseEnd_4904113 := by
    simpa [prefixWord, tailWord_4904113, baseEnd_4904113] using wordTrace_append hprefix tailTrace_4904113
  have hstable : (prefixWord ++ tailWord_4904113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904113).length < 2 ^ (prefixWord ++ tailWord_4904113).sum := by decide
  have hdescent : baseEnd_4904113 < baseStart_4904113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904119 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_4904119 : Nat := 118140960795 + 4904119 * 2 ^ 59
def prefixEnd_4904119 : Nat := 4983230072969 + 3 ^ 40 * 4904119 * 2
def baseEnd_4904119 : Nat := 2518170233846803345558873

theorem tailTrace_4904119 : CollatzResearch.WordTrace tailWord_4904119 prefixEnd_4904119 2518170233846803345558873 := by
  unfold tailWord_4904119
  simp only [CollatzResearch.WordTrace]
  refine ⟨178867914520221894689003411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119245276346814596459335607 178867914520221894689003411)
  ·
    refine ⟨268301871780332842033505117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178867914520221894689003411 268301871780332842033505117)
    ·
      refine ⟨100613201917624815762564419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268301871780332842033505117 100613201917624815762564419)
      ·
        refine ⟨150919802876437223643846629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100613201917624815762564419 150919802876437223643846629)
        ·
          refine ⟨28297463039331979433221243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150919802876437223643846629 28297463039331979433221243)
          ·
            refine ⟨42446194558997969149831865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28297463039331979433221243 42446194558997969149831865)
            ·
              refine ⟨31834645919248476862373899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42446194558997969149831865 31834645919248476862373899)
              ·
                refine ⟨47751968878872715293560849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31834645919248476862373899 47751968878872715293560849)
                ·
                  refine ⟨35813976659154536470170637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47751968878872715293560849 35813976659154536470170637)
                  ·
                    refine ⟨13430241247182951176313989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35813976659154536470170637 13430241247182951176313989)
                    ·
                      refine ⟨2518170233846803345558873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13430241247182951176313989 2518170233846803345558873)
                      ·
                        rfl

theorem cell23_4904119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_4904119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904119 prefixEnd_4904119 := by exact prefixLift 4904119
  have htrace : WordTrace (prefixWord ++ tailWord_4904119) baseStart_4904119 baseEnd_4904119 := by
    simpa [prefixWord, tailWord_4904119, baseEnd_4904119] using wordTrace_append hprefix tailTrace_4904119
  have hstable : (prefixWord ++ tailWord_4904119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904119).length < 2 ^ (prefixWord ++ tailWord_4904119).sum := by decide
  have hdescent : baseEnd_4904119 < baseStart_4904119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904139 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 3]
def baseStart_4904139 : Nat := 118140960795 + 4904139 * 2 ^ 59
def prefixEnd_4904139 : Nat := 4983230072969 + 3 ^ 40 * 4904139 * 2
def baseEnd_4904139 : Nat := 2518180503459893267308781

theorem tailTrace_4904139 : CollatzResearch.WordTrace tailWord_4904139 prefixEnd_4904139 2518180503459893267308781 := by
  unfold tailWord_4904139
  simp only [CollatzResearch.WordTrace]
  refine ⟨178868643980149438104731471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119245762653432958736487647 178868643980149438104731471)
  ·
    refine ⟨268302965970224157157097207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178868643980149438104731471 268302965970224157157097207)
    ·
      refine ⟨402454448955336235735645811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268302965970224157157097207 402454448955336235735645811)
      ·
        refine ⟨603681673433004353603468717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402454448955336235735645811 603681673433004353603468717)
        ·
          refine ⟨226380627537376632601300769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 603681673433004353603468717 226380627537376632601300769)
          ·
            refine ⟨169785470653032474450975577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226380627537376632601300769 169785470653032474450975577)
            ·
              refine ⟨127339102989774355838231683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169785470653032474450975577 127339102989774355838231683)
              ·
                refine ⟨191008654484661533757347525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127339102989774355838231683 191008654484661533757347525)
                ·
                  refine ⟨35814122715874037579502661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191008654484661533757347525 35814122715874037579502661)
                  ·
                    refine ⟨6715148009226382046156749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35814122715874037579502661 6715148009226382046156749)
                    ·
                      refine ⟨2518180503459893267308781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6715148009226382046156749 2518180503459893267308781)
                      ·
                        rfl

theorem cell23_4904139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 3].length) (baseStart_4904139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904139 prefixEnd_4904139 := by exact prefixLift 4904139
  have htrace : WordTrace (prefixWord ++ tailWord_4904139) baseStart_4904139 baseEnd_4904139 := by
    simpa [prefixWord, tailWord_4904139, baseEnd_4904139] using wordTrace_append hprefix tailTrace_4904139
  have hstable : (prefixWord ++ tailWord_4904139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904139).length < 2 ^ (prefixWord ++ tailWord_4904139).sum := by decide
  have hdescent : baseEnd_4904139 < baseStart_4904139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904170 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_4904170 : Nat := 118140960795 + 4904170 * 2 ^ 59
def prefixEnd_4904170 : Nat := 4983230072969 + 3 ^ 40 * 4904170 * 2
def baseEnd_4904170 : Nat := 2518196421360182646021139

theorem tailTrace_4904170 : CollatzResearch.WordTrace tailWord_4904170 prefixEnd_4904170 2518196421360182646021139 := by
  unfold tailWord_4904170
  simp only [CollatzResearch.WordTrace]
  refine ⟨44717443660759282599777491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119246516428691420266073309 44717443660759282599777491)
  ·
    refine ⟨67076165491138923899666237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44717443660759282599777491 67076165491138923899666237)
    ·
      refine ⟨25153562059177096462374839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67076165491138923899666237 25153562059177096462374839)
      ·
        refine ⟨37730343088765644693562259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25153562059177096462374839 37730343088765644693562259)
        ·
          refine ⟨56595514633148467040343389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37730343088765644693562259 56595514633148467040343389)
          ·
            refine ⟨21223317987430675140128771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56595514633148467040343389 21223317987430675140128771)
            ·
              refine ⟨31834976981146012710193157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21223317987430675140128771 31834976981146012710193157)
              ·
                refine ⟨5969058183964877383161217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31834976981146012710193157 5969058183964877383161217)
                ·
                  refine ⟨4476793637973658037370913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5969058183964877383161217 4476793637973658037370913)
                  ·
                    refine ⟨3357595228480243528028185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4476793637973658037370913 3357595228480243528028185)
                    ·
                      refine ⟨2518196421360182646021139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357595228480243528028185 2518196421360182646021139)
                      ·
                        rfl

theorem cell23_4904170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_4904170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904170 prefixEnd_4904170 := by exact prefixLift 4904170
  have htrace : WordTrace (prefixWord ++ tailWord_4904170) baseStart_4904170 baseEnd_4904170 := by
    simpa [prefixWord, tailWord_4904170, baseEnd_4904170] using wordTrace_append hprefix tailTrace_4904170
  have hstable : (prefixWord ++ tailWord_4904170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904170).length < 2 ^ (prefixWord ++ tailWord_4904170).sum := by decide
  have hdescent : baseEnd_4904170 < baseStart_4904170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904186 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_4904186 : Nat := 118140960795 + 4904186 * 2 ^ 59
def prefixEnd_4904186 : Nat := 4983230072969 + 3 ^ 40 * 4904186 * 2
def baseEnd_4904186 : Nat := 2518204637050654583421065

theorem tailTrace_4904186 : CollatzResearch.WordTrace tailWord_4904186 prefixEnd_4904186 2518204637050654583421065 := by
  unfold tailWord_4904186
  simp only [CollatzResearch.WordTrace]
  refine ⟨44717589552744791282923103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119246905473986110087794941 44717589552744791282923103)
  ·
    refine ⟨67076384329117186924384655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44717589552744791282923103 67076384329117186924384655)
    ·
      refine ⟨100614576493675780386576983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67076384329117186924384655 100614576493675780386576983)
      ·
        refine ⟨150921864740513670579865475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100614576493675780386576983 150921864740513670579865475)
        ·
          refine ⟨226382797110770505869798213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150921864740513670579865475 226382797110770505869798213)
          ·
            refine ⟨42446774458269469850587165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226382797110770505869798213 42446774458269469850587165)
            ·
              refine ⟨15917540421851051193970187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42446774458269469850587165 15917540421851051193970187)
              ·
                refine ⟨23876310632776576790955281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15917540421851051193970187 23876310632776576790955281)
                ·
                  refine ⟨17907232974582432593216461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23876310632776576790955281 17907232974582432593216461)
                  ·
                    refine ⟨6715212365468412222456173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17907232974582432593216461 6715212365468412222456173)
                    ·
                      refine ⟨2518204637050654583421065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6715212365468412222456173 2518204637050654583421065)
                      ·
                        rfl

theorem cell23_4904186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_4904186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904186 prefixEnd_4904186 := by exact prefixLift 4904186
  have htrace : WordTrace (prefixWord ++ tailWord_4904186) baseStart_4904186 baseEnd_4904186 := by
    simpa [prefixWord, tailWord_4904186, baseEnd_4904186] using wordTrace_append hprefix tailTrace_4904186
  have hstable : (prefixWord ++ tailWord_4904186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904186).length < 2 ^ (prefixWord ++ tailWord_4904186).sum := by decide
  have hdescent : baseEnd_4904186 < baseStart_4904186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904206 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_4904206 : Nat := 118140960795 + 4904206 * 2 ^ 59
def prefixEnd_4904206 : Nat := 4983230072969 + 3 ^ 40 * 4904206 * 2
def baseEnd_4904206 : Nat := 839404968887914835056991

theorem tailTrace_4904206 : CollatzResearch.WordTrace tailWord_4904206 prefixEnd_4904206 839404968887914835056991 := by
  unfold tailWord_4904206
  simp only [CollatzResearch.WordTrace]
  refine ⟨22358885958863338568427559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119247391780604472364946981 22358885958863338568427559)
  ·
    refine ⟨33538328938295007852641339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22358885958863338568427559 33538328938295007852641339)
    ·
      refine ⟨50307493407442511778962009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33538328938295007852641339 50307493407442511778962009)
      ·
        refine ⟨37730620055581883834221507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50307493407442511778962009 37730620055581883834221507)
        ·
          refine ⟨56595930083372825751332261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37730620055581883834221507 56595930083372825751332261)
          ·
            refine ⟨10611736890632404828374799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56595930083372825751332261 10611736890632404828374799)
            ·
              refine ⟨15917605335948607242562199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10611736890632404828374799 15917605335948607242562199)
              ·
                refine ⟨23876408003922910863843299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15917605335948607242562199 23876408003922910863843299)
                ·
                  refine ⟨35814612005884366295764949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23876408003922910863843299 35814612005884366295764949)
                  ·
                    refine ⟨839404968887914835056991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35814612005884366295764949 839404968887914835056991)
                    ·
                      rfl

theorem cell23_4904206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_4904206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904206 prefixEnd_4904206 := by exact prefixLift 4904206
  have htrace : WordTrace (prefixWord ++ tailWord_4904206) baseStart_4904206 baseEnd_4904206 := by
    simpa [prefixWord, tailWord_4904206, baseEnd_4904206] using wordTrace_append hprefix tailTrace_4904206
  have hstable : (prefixWord ++ tailWord_4904206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904206).length < 2 ^ (prefixWord ++ tailWord_4904206).sum := by decide
  have hdescent : baseEnd_4904206 < baseStart_4904206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904239 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_4904239 : Nat := 118140960795 + 4904239 * 2 ^ 59
def prefixEnd_4904239 : Nat := 4983230072969 + 3 ^ 40 * 4904239 * 2
def baseEnd_4904239 : Nat := 2518231851525342876058321

theorem tailTrace_4904239 : CollatzResearch.WordTrace tailWord_4904239 prefixEnd_4904239 2518231851525342876058321 := by
  unfold tailWord_4904239
  simp only [CollatzResearch.WordTrace]
  refine ⟨178872291279787155183371771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119248194186524770122247847 178872291279787155183371771)
  ·
    refine ⟨268308436919680732775057657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178872291279787155183371771 268308436919680732775057657)
    ·
      refine ⟨201231327689760549581293243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268308436919680732775057657 201231327689760549581293243)
      ·
        refine ⟨301846991534640824371939865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201231327689760549581293243 301846991534640824371939865)
        ·
          refine ⟨226385243650980618278954899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301846991534640824371939865 226385243650980618278954899)
          ·
            refine ⟨339577865476470927418432349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226385243650980618278954899 339577865476470927418432349)
            ·
              refine ⟨127341699553676597781912131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339577865476470927418432349 127341699553676597781912131)
              ·
                refine ⟨191012549330514896672868197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127341699553676597781912131 191012549330514896672868197)
                ·
                  refine ⟨35814852999471543126162787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191012549330514896672868197 35814852999471543126162787)
                  ·
                    refine ⟨53722279499207314689244181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35814852999471543126162787 53722279499207314689244181)
                    ·
                      refine ⟨2518231851525342876058321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53722279499207314689244181 2518231851525342876058321)
                      ·
                        rfl

theorem cell23_4904239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_4904239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904239 prefixEnd_4904239 := by exact prefixLift 4904239
  have htrace : WordTrace (prefixWord ++ tailWord_4904239) baseStart_4904239 baseEnd_4904239 := by
    simpa [prefixWord, tailWord_4904239, baseEnd_4904239] using wordTrace_append hprefix tailTrace_4904239
  have hstable : (prefixWord ++ tailWord_4904239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904239).length < 2 ^ (prefixWord ++ tailWord_4904239).sum := by decide
  have hdescent : baseEnd_4904239 < baseStart_4904239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904243 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 2, 4, 2]
def baseStart_4904243 : Nat := 118140960795 + 4904243 * 2 ^ 59
def prefixEnd_4904243 : Nat := 4983230072969 + 3 ^ 40 * 4904243 * 2
def baseEnd_4904243 : Nat := 2518233905447960860408303

theorem tailTrace_4904243 : CollatzResearch.WordTrace tailWord_4904243 prefixEnd_4904243 2518233905447960860408303 := by
  unfold tailWord_4904243
  simp only [CollatzResearch.WordTrace]
  refine ⟨178872437171772663866517383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119248291447848442577678255 178872437171772663866517383)
  ·
    refine ⟨268308655757658995799776075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178872437171772663866517383 268308655757658995799776075)
    ·
      refine ⟨402462983636488493699664113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268308655757658995799776075 402462983636488493699664113)
      ·
        refine ⟨301847237727366370274748085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402462983636488493699664113 301847237727366370274748085)
        ·
          refine ⟨28298178536940597213257633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 301847237727366370274748085 28298178536940597213257633)
          ·
            refine ⟨21223633902705447909943225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28298178536940597213257633 21223633902705447909943225)
            ·
              refine ⟨15917725427029085932457419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21223633902705447909943225 15917725427029085932457419)
              ·
                refine ⟨23876588140543628898686129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15917725427029085932457419 23876588140543628898686129)
                ·
                  refine ⟨17907441105407721674014597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23876588140543628898686129 17907441105407721674014597)
                  ·
                    refine ⟨3357645207263947813877737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17907441105407721674014597 3357645207263947813877737)
                    ·
                      refine ⟨2518233905447960860408303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357645207263947813877737 2518233905447960860408303)
                      ·
                        rfl

theorem cell23_4904243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 4, 2].length) (baseStart_4904243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904243 prefixEnd_4904243 := by exact prefixLift 4904243
  have htrace : WordTrace (prefixWord ++ tailWord_4904243) baseStart_4904243 baseEnd_4904243 := by
    simpa [prefixWord, tailWord_4904243, baseEnd_4904243] using wordTrace_append hprefix tailTrace_4904243
  have hstable : (prefixWord ++ tailWord_4904243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904243).length < 2 ^ (prefixWord ++ tailWord_4904243).sum := by decide
  have hdescent : baseEnd_4904243 < baseStart_4904243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904300 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 6]
def baseStart_4904300 : Nat := 118140960795 + 4904300 * 2 ^ 59
def prefixEnd_4904300 : Nat := 4983230072969 + 3 ^ 40 * 4904300 * 2
def baseEnd_4904300 : Nat := 279807019316140793043949

theorem tailTrace_4904300 : CollatzResearch.WordTrace tailWord_4904300 prefixEnd_4904300 279807019316140793043949 := by
  unfold tailWord_4904300
  simp only [CollatzResearch.WordTrace]
  refine ⟨89437258066283081300671177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119249677421710775067561569 89437258066283081300671177)
  ·
    refine ⟨67077943549712310975503383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89437258066283081300671177 67077943549712310975503383)
    ·
      refine ⟨100616915324568466463255075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67077943549712310975503383 100616915324568466463255075)
      ·
        refine ⟨150925372986852699694882613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100616915324568466463255075 150925372986852699694882613)
        ·
          refine ⟨14149253717517440596395245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150925372986852699694882613 14149253717517440596395245)
          ·
            refine ⟨5305970144069040223648217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14149253717517440596395245 5305970144069040223648217)
            ·
              refine ⟨3979477608051780167736163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5305970144069040223648217 3979477608051780167736163)
              ·
                refine ⟨5969216412077670251604245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979477608051780167736163 5969216412077670251604245)
                ·
                  refine ⟨279807019316140793043949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5969216412077670251604245 279807019316140793043949)
                  ·
                    rfl

theorem cell23_4904300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_4904300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904300 prefixEnd_4904300 := by exact prefixLift 4904300
  have htrace : WordTrace (prefixWord ++ tailWord_4904300) baseStart_4904300 baseEnd_4904300 := by
    simpa [prefixWord, tailWord_4904300, baseEnd_4904300] using wordTrace_append hprefix tailTrace_4904300
  have hstable : (prefixWord ++ tailWord_4904300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904300).length < 2 ^ (prefixWord ++ tailWord_4904300).sum := by decide
  have hdescent : baseEnd_4904300 < baseStart_4904300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904303 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 4, 3, 2]
def baseStart_4904303 : Nat := 118140960795 + 4904303 * 2 ^ 59
def prefixEnd_4904303 : Nat := 4983230072969 + 3 ^ 40 * 4904303 * 2
def baseEnd_4904303 : Nat := 2518264714287230625658027

theorem tailTrace_4904303 : CollatzResearch.WordTrace tailWord_4904303 prefixEnd_4904303 2518264714287230625658027 := by
  unfold tailWord_4904303
  simp only [CollatzResearch.WordTrace]
  refine ⟨178874625551555294113701563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119249750367703529409134375 178874625551555294113701563)
  ·
    refine ⟨268311938327332941170552345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178874625551555294113701563 268311938327332941170552345)
    ·
      refine ⟨201233953745499705877914259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268311938327332941170552345 201233953745499705877914259)
      ·
        refine ⟨301850930618249558816871389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201233953745499705877914259 301850930618249558816871389)
        ·
          refine ⟨113194098981843584556326771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301850930618249558816871389 113194098981843584556326771)
          ·
            refine ⟨169791148472765376834490157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113194098981843584556326771 169791148472765376834490157)
            ·
              refine ⟨63671680677287016312933809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169791148472765376834490157 63671680677287016312933809)
              ·
                refine ⟨47753760507965262234700357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63671680677287016312933809 47753760507965262234700357)
                ·
                  refine ⟨8953830095243486669006317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47753760507965262234700357 8953830095243486669006317)
                  ·
                    refine ⟨3357686285716307500877369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8953830095243486669006317 3357686285716307500877369)
                    ·
                      refine ⟨2518264714287230625658027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357686285716307500877369 2518264714287230625658027)
                      ·
                        rfl

theorem cell23_4904303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 3, 2].length) (baseStart_4904303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904303 prefixEnd_4904303 := by exact prefixLift 4904303
  have htrace : WordTrace (prefixWord ++ tailWord_4904303) baseStart_4904303 baseEnd_4904303 := by
    simpa [prefixWord, tailWord_4904303, baseEnd_4904303] using wordTrace_append hprefix tailTrace_4904303
  have hstable : (prefixWord ++ tailWord_4904303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904303).length < 2 ^ (prefixWord ++ tailWord_4904303).sum := by decide
  have hdescent : baseEnd_4904303 < baseStart_4904303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904313 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 1, 5]
def baseStart_4904313 : Nat := 118140960795 + 4904313 * 2 ^ 59
def prefixEnd_4904313 : Nat := 4983230072969 + 3 ^ 40 * 4904313 * 2
def baseEnd_4904313 : Nat := 839423283031258528844327

theorem tailTrace_4904313 : CollatzResearch.WordTrace tailWord_4904313 prefixEnd_4904313 839423283031258528844327 := by
  unfold tailWord_4904313
  simp only [CollatzResearch.WordTrace]
  refine ⟨178874990281519065821565593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119249993521012710547710395 178874990281519065821565593)
  ·
    refine ⟨134156242711139299366174195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178874990281519065821565593 134156242711139299366174195)
    ·
      refine ⟨201234364066708949049261293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134156242711139299366174195 201234364066708949049261293)
      ·
        refine ⟨75462886525015855893472985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201234364066708949049261293 75462886525015855893472985)
        ·
          refine ⟨56597164893761891920104739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75462886525015855893472985 56597164893761891920104739)
          ·
            refine ⟨84895747340642837880157109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56597164893761891920104739 84895747340642837880157109)
            ·
              refine ⟨7958976313185266051264729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84895747340642837880157109 7958976313185266051264729)
              ·
                refine ⟨5969232234888949538448547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7958976313185266051264729 5969232234888949538448547)
                ·
                  refine ⟨8953848352333424307672821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5969232234888949538448547 8953848352333424307672821)
                  ·
                    refine ⟨839423283031258528844327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8953848352333424307672821 839423283031258528844327)
                    ·
                      rfl

theorem cell23_4904313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_4904313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904313 prefixEnd_4904313 := by exact prefixLift 4904313
  have htrace : WordTrace (prefixWord ++ tailWord_4904313) baseStart_4904313 baseEnd_4904313 := by
    simpa [prefixWord, tailWord_4904313, baseEnd_4904313] using wordTrace_append hprefix tailTrace_4904313
  have hstable : (prefixWord ++ tailWord_4904313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904313).length < 2 ^ (prefixWord ++ tailWord_4904313).sum := by decide
  have hdescent : baseEnd_4904313 < baseStart_4904313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904338 : List Nat := [3, 2, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_4904338 : Nat := 118140960795 + 4904338 * 2 ^ 59
def prefixEnd_4904338 : Nat := 4983230072969 + 3 ^ 40 * 4904338 * 2
def baseEnd_4904338 : Nat := 839427562036712662906789

theorem tailTrace_4904338 : CollatzResearch.WordTrace tailWord_4904338 prefixEnd_4904338 839427562036712662906789 := by
  unfold tailWord_4904338
  simp only [CollatzResearch.WordTrace]
  refine ⟨44718975526607123772806417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119250601404285663394150445 44718975526607123772806417)
  ·
    refine ⟨33539231644955342829604813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44718975526607123772806417 33539231644955342829604813)
    ·
      refine ⟨12577211866858253561101805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33539231644955342829604813 12577211866858253561101805)
      ·
        refine ⟨4716454450071845085413177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12577211866858253561101805 4716454450071845085413177)
        ·
          refine ⟨3537340837553883814059883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4716454450071845085413177 3537340837553883814059883)
          ·
            refine ⟨5306011256330825721089825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537340837553883814059883 5306011256330825721089825)
            ·
              refine ⟨3979508442248119290817369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5306011256330825721089825 3979508442248119290817369)
              ·
                refine ⟨2984631331686089468113027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3979508442248119290817369 2984631331686089468113027)
                ·
                  refine ⟨4476946997529134202169541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984631331686089468113027 4476946997529134202169541)
                  ·
                    refine ⟨839427562036712662906789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4476946997529134202169541 839427562036712662906789)
                    ·
                      rfl

theorem cell23_4904338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_4904338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904338 prefixEnd_4904338 := by exact prefixLift 4904338
  have htrace : WordTrace (prefixWord ++ tailWord_4904338) baseStart_4904338 baseEnd_4904338 := by
    simpa [prefixWord, tailWord_4904338, baseEnd_4904338] using wordTrace_append hprefix tailTrace_4904338
  have hstable : (prefixWord ++ tailWord_4904338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904338).length < 2 ^ (prefixWord ++ tailWord_4904338).sum := by decide
  have hdescent : baseEnd_4904338 < baseStart_4904338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904344 : List Nat := [2, 1, 2, 5, 2, 1, 1, 4, 1, 1, 3]
def baseStart_4904344 : Nat := 118140960795 + 4904344 * 2 ^ 59
def prefixEnd_4904344 : Nat := 4983230072969 + 3 ^ 40 * 4904344 * 2
def baseEnd_4904344 : Nat := 2518285766994064965245339

theorem tailTrace_4904344 : CollatzResearch.WordTrace tailWord_4904344 prefixEnd_4904344 2518285766994064965245339 := by
  unfold tailWord_4904344
  simp only [CollatzResearch.WordTrace]
  refine ⟨89438060472203379057972043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119250747296271172077296057 89438060472203379057972043)
  ·
    refine ⟨134157090708305068586958065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89438060472203379057972043 134157090708305068586958065)
    ·
      refine ⟨100617818031228801440218549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134157090708305068586958065 100617818031228801440218549)
      ·
        refine ⟨9432920440427700135020489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100617818031228801440218549 9432920440427700135020489)
        ·
          refine ⟨7074690330320775101265367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9432920440427700135020489 7074690330320775101265367)
          ·
            refine ⟨10612035495481162651898051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7074690330320775101265367 10612035495481162651898051)
            ·
              refine ⟨15918053243221743977847077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10612035495481162651898051 15918053243221743977847077)
              ·
                refine ⟨2984634983104076995846327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15918053243221743977847077 2984634983104076995846327)
                ·
                  refine ⟨4476952474656115493769491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984634983104076995846327 4476952474656115493769491)
                  ·
                    refine ⟨6715428711984173240654237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4476952474656115493769491 6715428711984173240654237)
                    ·
                      refine ⟨2518285766994064965245339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6715428711984173240654237 2518285766994064965245339)
                      ·
                        rfl

theorem cell23_4904344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_4904344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904344 prefixEnd_4904344 := by exact prefixLift 4904344
  have htrace : WordTrace (prefixWord ++ tailWord_4904344) baseStart_4904344 baseEnd_4904344 := by
    simpa [prefixWord, tailWord_4904344, baseEnd_4904344] using wordTrace_append hprefix tailTrace_4904344
  have hstable : (prefixWord ++ tailWord_4904344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904344).length < 2 ^ (prefixWord ++ tailWord_4904344).sum := by decide
  have hdescent : baseEnd_4904344 < baseStart_4904344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904416 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 1, 8]
def baseStart_4904416 : Nat := 118140960795 + 4904416 * 2 ^ 59
def prefixEnd_4904416 : Nat := 4983230072969 + 3 ^ 40 * 4904416 * 2
def baseEnd_4904416 : Nat := 839440912533729561181669

theorem tailTrace_4904416 : CollatzResearch.WordTrace tailWord_4904416 prefixEnd_4904416 839440912533729561181669 := by
  unfold tailWord_4904416
  simp only [CollatzResearch.WordTrace]
  refine ⟨89439373500072957206282551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119252498000097276275043401 89439373500072957206282551)
  ·
    refine ⟨134159060250109435809423827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89439373500072957206282551 134159060250109435809423827)
    ·
      refine ⟨201238590375164153714135741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134159060250109435809423827 201238590375164153714135741)
      ·
        refine ⟨75464471390686557642800903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201238590375164153714135741 75464471390686557642800903)
        ·
          refine ⟨113196707086029836464201355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75464471390686557642800903 113196707086029836464201355)
          ·
            refine ⟨169795060629044754696302033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113196707086029836464201355 169795060629044754696302033)
            ·
              refine ⟨127346295471783566022226525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169795060629044754696302033 127346295471783566022226525)
              ·
                refine ⟨47754860801918837258334947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127346295471783566022226525 47754860801918837258334947)
                ·
                  refine ⟨71632291202878255887502421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47754860801918837258334947 71632291202878255887502421)
                  ·
                    refine ⟨839440912533729561181669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71632291202878255887502421 839440912533729561181669)
                    ·
                      rfl

theorem cell23_4904416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_4904416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904416 prefixEnd_4904416 := by exact prefixLift 4904416
  have htrace : WordTrace (prefixWord ++ tailWord_4904416) baseStart_4904416 baseEnd_4904416 := by
    simpa [prefixWord, tailWord_4904416, baseEnd_4904416] using wordTrace_append hprefix tailTrace_4904416
  have hstable : (prefixWord ++ tailWord_4904416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904416).length < 2 ^ (prefixWord ++ tailWord_4904416).sum := by decide
  have hdescent : baseEnd_4904416 < baseStart_4904416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904457 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 2, 2, 2]
def baseStart_4904457 : Nat := 118140960795 + 4904457 * 2 ^ 59
def prefixEnd_4904457 : Nat := 4983230072969 + 3 ^ 40 * 4904457 * 2
def baseEnd_4904457 : Nat := 2518343790308023023132319

theorem tailTrace_4904457 : CollatzResearch.WordTrace tailWord_4904457 prefixEnd_4904457 2518343790308023023132319 := by
  unfold tailWord_4904457
  simp only [CollatzResearch.WordTrace]
  refine ⟨178880242392997378414807625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119253494928664918943205083 178880242392997378414807625)
  ·
    refine ⟨134160181794748033811105719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178880242392997378414807625 134160181794748033811105719)
    ·
      refine ⟨201240272692122050716658579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134160181794748033811105719 201240272692122050716658579)
      ·
        refine ⟨301860409038183076074987869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201240272692122050716658579 301860409038183076074987869)
        ·
          refine ⟨113197653389318653528120451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301860409038183076074987869 113197653389318653528120451)
          ·
            refine ⟨169796480083977980292180677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113197653389318653528120451 169796480083977980292180677)
            ·
              refine ⟨31836840015745871304783877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169796480083977980292180677 31836840015745871304783877)
              ·
                refine ⟨5969407502952350869646977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31836840015745871304783877 5969407502952350869646977)
                ·
                  refine ⟨4477055627214263152235233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5969407502952350869646977 4477055627214263152235233)
                  ·
                    refine ⟨3357791720410697364176425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4477055627214263152235233 3357791720410697364176425)
                    ·
                      refine ⟨2518343790308023023132319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357791720410697364176425 2518343790308023023132319)
                      ·
                        rfl

theorem cell23_4904457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 2, 2].length) (baseStart_4904457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904457 prefixEnd_4904457 := by exact prefixLift 4904457
  have htrace : WordTrace (prefixWord ++ tailWord_4904457) baseStart_4904457 baseEnd_4904457 := by
    simpa [prefixWord, tailWord_4904457, baseEnd_4904457] using wordTrace_append hprefix tailTrace_4904457
  have hstable : (prefixWord ++ tailWord_4904457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904457).length < 2 ^ (prefixWord ++ tailWord_4904457).sum := by decide
  have hdescent : baseEnd_4904457 < baseStart_4904457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904468 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_4904468 : Nat := 118140960795 + 4904468 * 2 ^ 59
def prefixEnd_4904468 : Nat := 4983230072969 + 3 ^ 40 * 4904468 * 2
def baseEnd_4904468 : Nat := 2518349438595222480094769

theorem tailTrace_4904468 : CollatzResearch.WordTrace tailWord_4904468 prefixEnd_4904468 2518349438595222480094769 := by
  unfold tailWord_4904468
  simp only [CollatzResearch.WordTrace]
  refine ⟨89440321797978763646729029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119253762397305018195638705 89440321797978763646729029)
  ·
    refine ⟨16770060337121018183761693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89440321797978763646729029 16770060337121018183761693)
    ·
      refine ⟨6288772626420381818910635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16770060337121018183761693 6288772626420381818910635)
      ·
        refine ⟨9433158939630572728365953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6288772626420381818910635 9433158939630572728365953)
        ·
          refine ⟨7074869204722929546274465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9433158939630572728365953 7074869204722929546274465)
          ·
            refine ⟨5306151903542197159705849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7074869204722929546274465 5306151903542197159705849)
            ·
              refine ⟨3979613927656647869779387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5306151903542197159705849 3979613927656647869779387)
              ·
                refine ⟨5969420891484971804669081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979613927656647869779387 5969420891484971804669081)
                ·
                  refine ⟨4477065668613728853501811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5969420891484971804669081 4477065668613728853501811)
                  ·
                    refine ⟨6715598502920593280252717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4477065668613728853501811 6715598502920593280252717)
                    ·
                      refine ⟨2518349438595222480094769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6715598502920593280252717 2518349438595222480094769)
                      ·
                        rfl

theorem cell23_4904468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_4904468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904468 prefixEnd_4904468 := by exact prefixLift 4904468
  have htrace : WordTrace (prefixWord ++ tailWord_4904468) baseStart_4904468 baseEnd_4904468 := by
    simpa [prefixWord, tailWord_4904468, baseEnd_4904468] using wordTrace_append hprefix tailTrace_4904468
  have hstable : (prefixWord ++ tailWord_4904468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904468).length < 2 ^ (prefixWord ++ tailWord_4904468).sum := by decide
  have hdescent : baseEnd_4904468 < baseStart_4904468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904478 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4904478 : Nat := 118140960795 + 4904478 * 2 ^ 59
def prefixEnd_4904478 : Nat := 4983230072969 + 3 ^ 40 * 4904478 * 2
def baseEnd_4904478 : Nat := 2518354573401767440969723

theorem tailTrace_4904478 : CollatzResearch.WordTrace tailWord_4904478 prefixEnd_4904478 2518354573401767440969723 := by
  unfold tailWord_4904478
  simp only [CollatzResearch.WordTrace]
  refine ⟨22360126040740162375165261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119254005550614199334214725 22360126040740162375165261)
  ·
    refine ⟨8385047265277560890686973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22360126040740162375165261 8385047265277560890686973)
    ·
      refine ⟨3144392724479085334007615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8385047265277560890686973 3144392724479085334007615)
      ·
        refine ⟨4716589086718628001011423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144392724479085334007615 4716589086718628001011423)
        ·
          refine ⟨7074883630077942001517135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4716589086718628001011423 7074883630077942001517135)
          ·
            refine ⟨10612325445116913002275703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7074883630077942001517135 10612325445116913002275703)
            ·
              refine ⟨15918488167675369503413555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10612325445116913002275703 15918488167675369503413555)
              ·
                refine ⟨23877732251513054255120333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15918488167675369503413555 23877732251513054255120333)
                ·
                  refine ⟨8954149594317395345670125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23877732251513054255120333 8954149594317395345670125)
                  ·
                    refine ⟨3357806097869023254626297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8954149594317395345670125 3357806097869023254626297)
                    ·
                      refine ⟨2518354573401767440969723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357806097869023254626297 2518354573401767440969723)
                      ·
                        rfl

theorem cell23_4904478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4904478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904478 prefixEnd_4904478 := by exact prefixLift 4904478
  have htrace : WordTrace (prefixWord ++ tailWord_4904478) baseStart_4904478 baseEnd_4904478 := by
    simpa [prefixWord, tailWord_4904478, baseEnd_4904478] using wordTrace_append hprefix tailTrace_4904478
  have hstable : (prefixWord ++ tailWord_4904478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904478).length < 2 ^ (prefixWord ++ tailWord_4904478).sum := by decide
  have hdescent : baseEnd_4904478 < baseStart_4904478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904503 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_4904503 : Nat := 118140960795 + 4904503 * 2 ^ 59
def prefixEnd_4904503 : Nat := 4983230072969 + 3 ^ 40 * 4904503 * 2
def baseEnd_4904503 : Nat := 2518367410418129843157107

theorem tailTrace_4904503 : CollatzResearch.WordTrace tailWord_4904503 prefixEnd_4904503 2518367410418129843157107 := by
  unfold tailWord_4904503
  simp only [CollatzResearch.WordTrace]
  refine ⟨178881920150830728270982163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119254613433887152180654775 178881920150830728270982163)
  ·
    refine ⟨268322880226246092406473245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178881920150830728270982163 268322880226246092406473245)
    ·
      refine ⟨100621080084842284652427467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268322880226246092406473245 100621080084842284652427467)
      ·
        refine ⟨150931620127263426978641201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100621080084842284652427467 150931620127263426978641201)
        ·
          refine ⟨113198715095447570233980901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150931620127263426978641201 113198715095447570233980901)
          ·
            refine ⟨21224759080396419418871419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113198715095447570233980901 21224759080396419418871419)
            ·
              refine ⟨31837138620594629128307129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21224759080396419418871419 31837138620594629128307129)
              ·
                refine ⟨23877853965445971846230347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31837138620594629128307129 23877853965445971846230347)
                ·
                  refine ⟨35816780948168957769345521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23877853965445971846230347 35816780948168957769345521)
                  ·
                    refine ⟨26862585711126718327009141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35816780948168957769345521 26862585711126718327009141)
                    ·
                      refine ⟨2518367410418129843157107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26862585711126718327009141 2518367410418129843157107)
                      ·
                        rfl

theorem cell23_4904503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_4904503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904503 prefixEnd_4904503 := by exact prefixLift 4904503
  have htrace : WordTrace (prefixWord ++ tailWord_4904503) baseStart_4904503 baseEnd_4904503 := by
    simpa [prefixWord, tailWord_4904503, baseEnd_4904503] using wordTrace_append hprefix tailTrace_4904503
  have hstable : (prefixWord ++ tailWord_4904503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904503).length < 2 ^ (prefixWord ++ tailWord_4904503).sum := by decide
  have hdescent : baseEnd_4904503 < baseStart_4904503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904547 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 4]
def baseStart_4904547 : Nat := 118140960795 + 4904547 * 2 ^ 59
def prefixEnd_4904547 : Nat := 4983230072969 + 3 ^ 40 * 4904547 * 2
def baseEnd_4904547 : Nat := 2518390003566927671006905

theorem tailTrace_4904547 : CollatzResearch.WordTrace tailWord_4904547 prefixEnd_4904547 2518390003566927671006905 := by
  unfold tailWord_4904547
  simp only [CollatzResearch.WordTrace]
  refine ⟨178883524962671323785583895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119255683308447549190389263 178883524962671323785583895)
  ·
    refine ⟨268325287444006985678375843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178883524962671323785583895 268325287444006985678375843)
    ·
      refine ⟨402487931166010478517563765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268325287444006985678375843 402487931166010478517563765)
      ·
        refine ⟨37733243546813482361021603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 402487931166010478517563765 37733243546813482361021603)
        ·
          refine ⟨56599865320220223541532405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37733243546813482361021603 56599865320220223541532405)
          ·
            refine ⟨5306237373770645957018663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56599865320220223541532405 5306237373770645957018663)
            ·
              refine ⟨7959356060655968935527995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5306237373770645957018663 7959356060655968935527995)
              ·
                refine ⟨11939034090983953403291993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7959356060655968935527995 11939034090983953403291993)
                ·
                  refine ⟨8954275568237965052468995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11939034090983953403291993 8954275568237965052468995)
                  ·
                    refine ⟨13431413352356947578703493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8954275568237965052468995 13431413352356947578703493)
                    ·
                      refine ⟨2518390003566927671006905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13431413352356947578703493 2518390003566927671006905)
                      ·
                        rfl

theorem cell23_4904547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_4904547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904547 prefixEnd_4904547 := by exact prefixLift 4904547
  have htrace : WordTrace (prefixWord ++ tailWord_4904547) baseStart_4904547 baseEnd_4904547 := by
    simpa [prefixWord, tailWord_4904547, baseEnd_4904547] using wordTrace_append hprefix tailTrace_4904547
  have hstable : (prefixWord ++ tailWord_4904547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904547).length < 2 ^ (prefixWord ++ tailWord_4904547).sum := by decide
  have hdescent : baseEnd_4904547 < baseStart_4904547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904640 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_4904640 : Nat := 118140960795 + 4904640 * 2 ^ 59
def prefixEnd_4904640 : Nat := 4983230072969 + 3 ^ 40 * 4904640 * 2
def baseEnd_4904640 : Nat := 2518437757267795807143977

theorem tailTrace_4904640 : CollatzResearch.WordTrace tailWord_4904640 prefixEnd_4904640 2518437757267795807143977 := by
  unfold tailWord_4904640
  simp only [CollatzResearch.WordTrace]
  refine ⟨89443458475667200334359687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119257944634222933779146249 89443458475667200334359687)
  ·
    refine ⟨134165187713500800501539531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89443458475667200334359687 134165187713500800501539531)
    ·
      refine ⟨201247781570251200752309297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134165187713500800501539531 201247781570251200752309297)
      ·
        refine ⟨150935836177688400564231973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201247781570251200752309297 150935836177688400564231973)
        ·
          refine ⟨28300469283316575105793495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150935836177688400564231973 28300469283316575105793495)
          ·
            refine ⟨42450703924974862658690243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28300469283316575105793495 42450703924974862658690243)
            ·
              refine ⟨63676055887462293988035365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42450703924974862658690243 63676055887462293988035365)
              ·
                refine ⟨11939260478899180122756631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63676055887462293988035365 11939260478899180122756631)
                ·
                  refine ⟨17908890718348770184134947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11939260478899180122756631 17908890718348770184134947)
                  ·
                    refine ⟨26863336077523155276202421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17908890718348770184134947 26863336077523155276202421)
                    ·
                      refine ⟨2518437757267795807143977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26863336077523155276202421 2518437757267795807143977)
                      ·
                        rfl

theorem cell23_4904640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_4904640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904640 prefixEnd_4904640 := by exact prefixLift 4904640
  have htrace : WordTrace (prefixWord ++ tailWord_4904640) baseStart_4904640 baseEnd_4904640 := by
    simpa [prefixWord, tailWord_4904640, baseEnd_4904640] using wordTrace_append hprefix tailTrace_4904640
  have hstable : (prefixWord ++ tailWord_4904640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904640).length < 2 ^ (prefixWord ++ tailWord_4904640).sum := by decide
  have hdescent : baseEnd_4904640 < baseStart_4904640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904647 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 2, 4]
def baseStart_4904647 : Nat := 118140960795 + 4904647 * 2 ^ 59
def prefixEnd_4904647 : Nat := 4983230072969 + 3 ^ 40 * 4904647 * 2
def baseEnd_4904647 : Nat := 839480450544125759918815

theorem tailTrace_4904647 : CollatzResearch.WordTrace tailWord_4904647 prefixEnd_4904647 839480450544125759918815 := by
  unfold tailWord_4904647
  simp only [CollatzResearch.WordTrace]
  refine ⟨178887172262309040864224195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119258114841539360576149463 178887172262309040864224195)
  ·
    refine ⟨268330758393463561296336293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178887172262309040864224195 268330758393463561296336293)
    ·
      refine ⟨50312017198774417743063055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268330758393463561296336293 50312017198774417743063055)
      ·
        refine ⟨75468025798161626614594583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50312017198774417743063055 75468025798161626614594583)
        ·
          refine ⟨113202038697242439921891875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75468025798161626614594583 113202038697242439921891875)
          ·
            refine ⟨169803058045863659882837813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113202038697242439921891875 169803058045863659882837813)
            ·
              refine ⟨15919036691799718114016045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169803058045863659882837813 15919036691799718114016045)
              ·
                refine ⟨5969638759424894292756017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15919036691799718114016045 5969638759424894292756017)
                ·
                  refine ⟨4477229069568670719567013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5969638759424894292756017 4477229069568670719567013)
                  ·
                    refine ⟨839480450544125759918815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4477229069568670719567013 839480450544125759918815)
                    ·
                      rfl

theorem cell23_4904647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_4904647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904647 prefixEnd_4904647 := by exact prefixLift 4904647
  have htrace : WordTrace (prefixWord ++ tailWord_4904647) baseStart_4904647 baseEnd_4904647 := by
    simpa [prefixWord, tailWord_4904647, baseEnd_4904647] using wordTrace_append hprefix tailTrace_4904647
  have hstable : (prefixWord ++ tailWord_4904647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904647).length < 2 ^ (prefixWord ++ tailWord_4904647).sum := by decide
  have hdescent : baseEnd_4904647 < baseStart_4904647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
