import V185TrunkScan23Chunk0391

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2316898 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2316898 : Nat := 118140960795 + 2316898 * 2 ^ 59
def prefixEnd_2316898 : Nat := 4983230072969 + 3 ^ 40 * 2316898 * 2
def baseEnd_2316898 : Nat := 1189682301440781359619787

theorem tailTrace_2316898 : CollatzResearch.WordTrace tailWord_2316898 prefixEnd_2316898 1189682301440781359619787 := by
  unfold tailWord_2316898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21126053090070428880161837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56336141573521143680431565 21126053090070428880161837)
  ·
    refine ⟨7922269908776410830060689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21126053090070428880161837 7922269908776410830060689)
    ·
      refine ⟨5941702431582308122545517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7922269908776410830060689 5941702431582308122545517)
      ·
        refine ⟨2228138411843365545954569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5941702431582308122545517 2228138411843365545954569)
        ·
          refine ⟨1671103808882524159465927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2228138411843365545954569 1671103808882524159465927)
          ·
            refine ⟨2506655713323786239198891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671103808882524159465927 2506655713323786239198891)
            ·
              refine ⟨3759983569985679358798337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506655713323786239198891 3759983569985679358798337)
              ·
                refine ⟨2819987677489259519098753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759983569985679358798337 2819987677489259519098753)
                ·
                  refine ⟨2114990758116944639324065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2819987677489259519098753 2114990758116944639324065)
                  ·
                    refine ⟨1586243068587708479493049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2114990758116944639324065 1586243068587708479493049)
                    ·
                      refine ⟨1189682301440781359619787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1586243068587708479493049 1189682301440781359619787)
                      ·
                        rfl

theorem cell23_2316898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2316898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316898 prefixEnd_2316898 := by exact prefixLift 2316898
  have htrace : WordTrace (prefixWord ++ tailWord_2316898) baseStart_2316898 baseEnd_2316898 := by
    simpa [prefixWord, tailWord_2316898, baseEnd_2316898] using wordTrace_append hprefix tailTrace_2316898
  have hstable : (prefixWord ++ tailWord_2316898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316898).length < 2 ^ (prefixWord ++ tailWord_2316898).sum := by decide
  have hdescent : baseEnd_2316898 < baseStart_2316898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316963 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 3, 5, 2]
def baseStart_2316963 : Nat := 118140960795 + 2316963 * 2 ^ 59
def prefixEnd_2316963 : Nat := 4983230072969 + 3 ^ 40 * 2316963 * 2
def baseEnd_2316963 : Nat := 1189715677683323605306987

theorem tailTrace_2316963 : CollatzResearch.WordTrace tailWord_2316963 prefixEnd_2316963 1189715677683323605306987 := by
  unfold tailWord_2316963
  simp only [CollatzResearch.WordTrace]
  refine ⟨84506583105046231621763543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56337722070030821081175695 84506583105046231621763543)
  ·
    refine ⟨126759874657569347432645315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84506583105046231621763543 126759874657569347432645315)
    ·
      refine ⟨190139811986354021148967973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126759874657569347432645315 190139811986354021148967973)
      ·
        refine ⟨35651214747441378965431495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190139811986354021148967973 35651214747441378965431495)
        ·
          refine ⟨53476822121162068448147243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35651214747441378965431495 53476822121162068448147243)
          ·
            refine ⟨80215233181743102672220865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53476822121162068448147243 80215233181743102672220865)
            ·
              refine ⟨60161424886307327004165649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80215233181743102672220865 60161424886307327004165649)
              ·
                refine ⟨45121068664730495253124237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60161424886307327004165649 45121068664730495253124237)
                ·
                  refine ⟨16920400749273935719921589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45121068664730495253124237 16920400749273935719921589)
                  ·
                    refine ⟨1586287570244431473742649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16920400749273935719921589 1586287570244431473742649)
                    ·
                      refine ⟨1189715677683323605306987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1586287570244431473742649 1189715677683323605306987)
                      ·
                        rfl

theorem cell23_2316963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_2316963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316963 prefixEnd_2316963 := by exact prefixLift 2316963
  have htrace : WordTrace (prefixWord ++ tailWord_2316963) baseStart_2316963 baseEnd_2316963 := by
    simpa [prefixWord, tailWord_2316963, baseEnd_2316963] using wordTrace_append hprefix tailTrace_2316963
  have hstable : (prefixWord ++ tailWord_2316963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316963).length < 2 ^ (prefixWord ++ tailWord_2316963).sum := by decide
  have hdescent : baseEnd_2316963 < baseStart_2316963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316976 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_2316976 : Nat := 118140960795 + 2316976 * 2 ^ 59
def prefixEnd_2316976 : Nat := 4983230072969 + 3 ^ 40 * 2316976 * 2
def baseEnd_2316976 : Nat := 1189722352931832054444427

theorem tailTrace_2316976 : CollatzResearch.WordTrace tailWord_2316976 prefixEnd_2316976 1189722352931832054444427 := by
  unfold tailWord_2316976
  simp only [CollatzResearch.WordTrace]
  refine ⟨42253528626999567420993391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56338038169332756561324521 42253528626999567420993391)
  ·
    refine ⟨63380292940499351131490087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42253528626999567420993391 63380292940499351131490087)
    ·
      refine ⟨95070439410749026697235131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63380292940499351131490087 95070439410749026697235131)
      ·
        refine ⟨142605659116123540045852697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95070439410749026697235131 142605659116123540045852697)
        ·
          refine ⟨106954244337092655034389523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142605659116123540045852697 106954244337092655034389523)
          ·
            refine ⟨160431366505638982551584285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106954244337092655034389523 160431366505638982551584285)
            ·
              refine ⟨60161762439614618456844107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160431366505638982551584285 60161762439614618456844107)
              ·
                refine ⟨90242643659421927685266161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60161762439614618456844107 90242643659421927685266161)
                ·
                  refine ⟨67681982744566445763949621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90242643659421927685266161 67681982744566445763949621)
                  ·
                    refine ⟨6345185882303104290370277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67681982744566445763949621 6345185882303104290370277)
                    ·
                      refine ⟨1189722352931832054444427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6345185882303104290370277 1189722352931832054444427)
                      ·
                        rfl

theorem cell23_2316976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_2316976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316976 prefixEnd_2316976 := by exact prefixLift 2316976
  have htrace : WordTrace (prefixWord ++ tailWord_2316976) baseStart_2316976 baseEnd_2316976 := by
    simpa [prefixWord, tailWord_2316976, baseEnd_2316976] using wordTrace_append hprefix tailTrace_2316976
  have hstable : (prefixWord ++ tailWord_2316976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316976).length < 2 ^ (prefixWord ++ tailWord_2316976).sum := by decide
  have hdescent : baseEnd_2316976 < baseStart_2316976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317016 : List Nat := [2, 1, 2, 2, 3, 13]
def baseStart_2317016 : Nat := 118140960795 + 2317016 * 2 ^ 59
def prefixEnd_2317016 : Nat := 4983230072969 + 3 ^ 40 * 2317016 * 2
def baseEnd_2317016 : Nat := 4896061284600872008001

theorem tailTrace_2317016 : CollatzResearch.WordTrace tailWord_2317016 prefixEnd_2317016 4896061284600872008001 := by
  unfold tailWord_2317016
  simp only [CollatzResearch.WordTrace]
  refine ⟨42254258086927110836721451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56339010782569481115628601 42254258086927110836721451)
  ·
    refine ⟨63381387130390666255082177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42254258086927110836721451 63381387130390666255082177)
    ·
      refine ⟨47536040347792999691311633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63381387130390666255082177 47536040347792999691311633)
      ·
        refine ⟨35652030260844749768483725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47536040347792999691311633 35652030260844749768483725)
        ·
          refine ⟨13369511347816781163181397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35652030260844749768483725 13369511347816781163181397)
          ·
            refine ⟨4896061284600872008001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 13369511347816781163181397 4896061284600872008001)
            ·
              rfl

theorem cell23_2317016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 13].length) (baseStart_2317016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317016 prefixEnd_2317016 := by exact prefixLift 2317016
  have htrace : WordTrace (prefixWord ++ tailWord_2317016) baseStart_2317016 baseEnd_2317016 := by
    simpa [prefixWord, tailWord_2317016, baseEnd_2317016] using wordTrace_append hprefix tailTrace_2317016
  have hstable : (prefixWord ++ tailWord_2317016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317016).length < 2 ^ (prefixWord ++ tailWord_2317016).sum := by decide
  have hdescent : baseEnd_2317016 < baseStart_2317016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317060 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2317060 : Nat := 118140960795 + 2317060 * 2 ^ 59
def prefixEnd_2317060 : Nat := 4983230072969 + 3 ^ 40 * 2317060 * 2
def baseEnd_2317060 : Nat := 1189765485306809725794041

theorem tailTrace_2317060 : CollatzResearch.WordTrace tailWord_2317060 prefixEnd_2317060 1189765485306809725794041 := by
  unfold tailWord_2317060
  simp only [CollatzResearch.WordTrace]
  refine ⟨42255060492847408594022317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56340080657129878125363089 42255060492847408594022317)
  ·
    refine ⟨15845647684817778222758369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42255060492847408594022317 15845647684817778222758369)
    ·
      refine ⟨11884235763613333667068777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15845647684817778222758369 11884235763613333667068777)
      ·
        refine ⟨8913176822710000250301583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11884235763613333667068777 8913176822710000250301583)
        ·
          refine ⟨13369765234065000375452375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8913176822710000250301583 13369765234065000375452375)
          ·
            refine ⟨20054647851097500563178563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13369765234065000375452375 20054647851097500563178563)
            ·
              refine ⟨30081971776646250844767845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20054647851097500563178563 30081971776646250844767845)
              ·
                refine ⟨5640369708121172033393971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30081971776646250844767845 5640369708121172033393971)
                ·
                  refine ⟨8460554562181758050090957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640369708121172033393971 8460554562181758050090957)
                  ·
                    refine ⟨3172707960818159268784109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8460554562181758050090957 3172707960818159268784109)
                    ·
                      refine ⟨1189765485306809725794041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3172707960818159268784109 1189765485306809725794041)
                      ·
                        rfl

theorem cell23_2317060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2317060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317060 prefixEnd_2317060 := by exact prefixLift 2317060
  have htrace : WordTrace (prefixWord ++ tailWord_2317060) baseStart_2317060 baseEnd_2317060 := by
    simpa [prefixWord, tailWord_2317060, baseEnd_2317060] using wordTrace_append hprefix tailTrace_2317060
  have hstable : (prefixWord ++ tailWord_2317060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317060).length < 2 ^ (prefixWord ++ tailWord_2317060).sum := by decide
  have hdescent : baseEnd_2317060 < baseStart_2317060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317064 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_2317064 : Nat := 118140960795 + 2317064 * 2 ^ 59
def prefixEnd_2317064 : Nat := 4983230072969 + 3 ^ 40 * 2317064 * 2
def baseEnd_2317064 : Nat := 1189767539229427710144023

theorem tailTrace_2317064 : CollatzResearch.WordTrace tailWord_2317064 prefixEnd_2317064 1189767539229427710144023 := by
  unfold tailWord_2317064
  simp only [CollatzResearch.WordTrace]
  refine ⟨42255133438840162935595123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56340177918453550580793497 42255133438840162935595123)
  ·
    refine ⟨63382700158260244403392685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42255133438840162935595123 63382700158260244403392685)
    ·
      refine ⟨23768512559347591651272257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63382700158260244403392685 23768512559347591651272257)
      ·
        refine ⟨17826384419510693738454193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23768512559347591651272257 17826384419510693738454193)
        ·
          refine ⟨13369788314633020303840645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17826384419510693738454193 13369788314633020303840645)
          ·
            refine ⟨2506835308993691306970121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13369788314633020303840645 2506835308993691306970121)
            ·
              refine ⟨1880126481745268480227591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506835308993691306970121 1880126481745268480227591)
              ·
                refine ⟨2820189722617902720341387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880126481745268480227591 2820189722617902720341387)
                ·
                  refine ⟨4230284583926854080512081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2820189722617902720341387 4230284583926854080512081)
                  ·
                    refine ⟨3172713437945140560384061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4230284583926854080512081 3172713437945140560384061)
                    ·
                      refine ⟨1189767539229427710144023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3172713437945140560384061 1189767539229427710144023)
                      ·
                        rfl

theorem cell23_2317064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_2317064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317064 prefixEnd_2317064 := by exact prefixLift 2317064
  have htrace : WordTrace (prefixWord ++ tailWord_2317064) baseStart_2317064 baseEnd_2317064 := by
    simpa [prefixWord, tailWord_2317064, baseEnd_2317064] using wordTrace_append hprefix tailTrace_2317064
  have hstable : (prefixWord ++ tailWord_2317064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317064).length < 2 ^ (prefixWord ++ tailWord_2317064).sum := by decide
  have hdescent : baseEnd_2317064 < baseStart_2317064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317093 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_2317093 : Nat := 118140960795 + 2317093 * 2 ^ 59
def prefixEnd_2317093 : Nat := 4983230072969 + 3 ^ 40 * 2317093 * 2
def baseEnd_2317093 : Nat := 396594143389469365560463

theorem tailTrace_2317093 : CollatzResearch.WordTrace tailWord_2317093 prefixEnd_2317093 396594143389469365560463 := by
  unfold tailWord_2317093
  simp only [CollatzResearch.WordTrace]
  refine ⟨84511324594575263823995933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56340883063050175882663955 84511324594575263823995933)
  ·
    refine ⟨31691746722965723933998475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84511324594575263823995933 31691746722965723933998475)
    ·
      refine ⟨47537620084448585900997713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31691746722965723933998475 47537620084448585900997713)
      ·
        refine ⟨35653215063336439425748285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47537620084448585900997713 35653215063336439425748285)
        ·
          refine ⟨13369955648751164784655607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35653215063336439425748285 13369955648751164784655607)
          ·
            refine ⟨20054933473126747176983411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13369955648751164784655607 20054933473126747176983411)
            ·
              refine ⟨30082400209690120765475117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20054933473126747176983411 30082400209690120765475117)
              ·
                refine ⟨11280900078633795287053169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30082400209690120765475117 11280900078633795287053169)
                ·
                  refine ⟨8460675058975346465289877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11280900078633795287053169 8460675058975346465289877)
                  ·
                    refine ⟨396594143389469365560463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8460675058975346465289877 396594143389469365560463)
                    ·
                      rfl

theorem cell23_2317093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_2317093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317093 prefixEnd_2317093 := by exact prefixLift 2317093
  have htrace : WordTrace (prefixWord ++ tailWord_2317093) baseStart_2317093 baseEnd_2317093 := by
    simpa [prefixWord, tailWord_2317093, baseEnd_2317093] using wordTrace_append hprefix tailTrace_2317093
  have hstable : (prefixWord ++ tailWord_2317093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317093).length < 2 ^ (prefixWord ++ tailWord_2317093).sum := by decide
  have hdescent : baseEnd_2317093 < baseStart_2317093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317101 : List Nat := [1, 5, 3, 2, 2, 1, 2, 7]
def baseStart_2317101 : Nat := 118140960795 + 2317101 * 2 ^ 59
def prefixEnd_2317101 : Nat := 4983230072969 + 3 ^ 40 * 2317101 * 2
def baseEnd_2317101 : Nat := 44066168074579409828939

theorem tailTrace_2317101 : CollatzResearch.WordTrace tailWord_2317101 prefixEnd_2317101 44066168074579409828939 := by
  unfold tailWord_2317101
  simp only [CollatzResearch.WordTrace]
  refine ⟨84511616378546281190287157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56341077585697520793524771 84511616378546281190287157)
  ·
    refine ⟨7922964035488713861589421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84511616378546281190287157 7922964035488713861589421)
    ·
      refine ⟨2971111513308267698096033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7922964035488713861589421 2971111513308267698096033)
      ·
        refine ⟨2228333634981200773572025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2971111513308267698096033 2228333634981200773572025)
        ·
          refine ⟨1671250226235900580179019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2228333634981200773572025 1671250226235900580179019)
          ·
            refine ⟨2506875339353850870268529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671250226235900580179019 2506875339353850870268529)
            ·
              refine ⟨1880156504515388152701397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506875339353850870268529 1880156504515388152701397)
              ·
                refine ⟨44066168074579409828939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1880156504515388152701397 44066168074579409828939)
                ·
                  rfl

theorem cell23_2317101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 7].length) (baseStart_2317101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317101 prefixEnd_2317101 := by exact prefixLift 2317101
  have htrace : WordTrace (prefixWord ++ tailWord_2317101) baseStart_2317101 baseEnd_2317101 := by
    simpa [prefixWord, tailWord_2317101, baseEnd_2317101] using wordTrace_append hprefix tailTrace_2317101
  have hstable : (prefixWord ++ tailWord_2317101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317101).length < 2 ^ (prefixWord ++ tailWord_2317101).sum := by decide
  have hdescent : baseEnd_2317101 < baseStart_2317101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317153 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 1, 7]
def baseStart_2317153 : Nat := 118140960795 + 2317153 * 2 ^ 59
def prefixEnd_2317153 : Nat := 4983230072969 + 3 ^ 40 * 2317153 * 2
def baseEnd_2317153 : Nat := 396604413002559287310371

theorem tailTrace_2317153 : CollatzResearch.WordTrace tailWord_2317153 prefixEnd_2317153 396604413002559287310371 := by
  unfold tailWord_2317153
  simp only [CollatzResearch.WordTrace]
  refine ⟨84513512974357894071180113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56342341982905262714120075 84513512974357894071180113)
  ·
    refine ⟨63385134730768420553385085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84513512974357894071180113 63385134730768420553385085)
    ·
      refine ⟨23769425524038157707519407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63385134730768420553385085 23769425524038157707519407)
      ·
        refine ⟨35654138286057236561279111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23769425524038157707519407 35654138286057236561279111)
        ·
          refine ⟨53481207429085854841918667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35654138286057236561279111 53481207429085854841918667)
          ·
            refine ⟨80221811143628782262878001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53481207429085854841918667 80221811143628782262878001)
            ·
              refine ⟨60166358357721586697158501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80221811143628782262878001 60166358357721586697158501)
              ·
                refine ⟨11281192192072797505717219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60166358357721586697158501 11281192192072797505717219)
                ·
                  refine ⟨16921788288109196258575829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11281192192072797505717219 16921788288109196258575829)
                  ·
                    refine ⟨396604413002559287310371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16921788288109196258575829 396604413002559287310371)
                    ·
                      rfl

theorem cell23_2317153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_2317153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317153 prefixEnd_2317153 := by exact prefixLift 2317153
  have htrace : WordTrace (prefixWord ++ tailWord_2317153) baseStart_2317153 baseEnd_2317153 := by
    simpa [prefixWord, tailWord_2317153, baseEnd_2317153] using wordTrace_append hprefix tailTrace_2317153
  have hstable : (prefixWord ++ tailWord_2317153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317153).length < 2 ^ (prefixWord ++ tailWord_2317153).sum := by decide
  have hdescent : baseEnd_2317153 < baseStart_2317153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317170 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_2317170 : Nat := 118140960795 + 2317170 * 2 ^ 59
def prefixEnd_2317170 : Nat := 4983230072969 + 3 ^ 40 * 2317170 * 2
def baseEnd_2317170 : Nat := 396607322726268098472845

theorem tailTrace_2317170 : CollatzResearch.WordTrace tailWord_2317170 prefixEnd_2317170 396607322726268098472845 := by
  unfold tailWord_2317170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21128533253824076493637241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56342755343530870649699309 21128533253824076493637241)
  ·
    refine ⟨15846399940368057370227931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21128533253824076493637241 15846399940368057370227931)
    ·
      refine ⟨23769599910552086055341897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15846399940368057370227931 23769599910552086055341897)
      ·
        refine ⟨17827199932914064541506423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23769599910552086055341897 17827199932914064541506423)
        ·
          refine ⟨26740799899371096812259635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17827199932914064541506423 26740799899371096812259635)
          ·
            refine ⟨40111199849056645218389453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26740799899371096812259635 40111199849056645218389453)
            ·
              refine ⟨15041699943396241956896045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40111199849056645218389453 15041699943396241956896045)
              ·
                refine ⟨5640637478773590733836017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15041699943396241956896045 5640637478773590733836017)
                ·
                  refine ⟨4230478109080193050377013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5640637478773590733836017 4230478109080193050377013)
                  ·
                    refine ⟨396607322726268098472845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4230478109080193050377013 396607322726268098472845)
                    ·
                      rfl

theorem cell23_2317170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_2317170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317170 prefixEnd_2317170 := by exact prefixLift 2317170
  have htrace : WordTrace (prefixWord ++ tailWord_2317170) baseStart_2317170 baseEnd_2317170 := by
    simpa [prefixWord, tailWord_2317170, baseEnd_2317170] using wordTrace_append hprefix tailTrace_2317170
  have hstable : (prefixWord ++ tailWord_2317170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317170).length < 2 ^ (prefixWord ++ tailWord_2317170).sum := by decide
  have hdescent : baseEnd_2317170 < baseStart_2317170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317203 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 6]
def baseStart_2317203 : Nat := 118140960795 + 2317203 * 2 ^ 59
def prefixEnd_2317203 : Nat := 4983230072969 + 3 ^ 40 * 2317203 * 2
def baseEnd_2317203 : Nat := 1189838913040402666305883

theorem tailTrace_2317203 : CollatzResearch.WordTrace tailWord_2317203 prefixEnd_2317203 1189838913040402666305883 := by
  unfold tailWord_2317203
  simp only [CollatzResearch.WordTrace]
  refine ⟨84515336624176752610500263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56343557749451168407000175 84515336624176752610500263)
  ·
    refine ⟨126773004936265128915750395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84515336624176752610500263 126773004936265128915750395)
    ·
      refine ⟨190159507404397693373625593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126773004936265128915750395 190159507404397693373625593)
      ·
        refine ⟨142619630553298270030219195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190159507404397693373625593 142619630553298270030219195)
        ·
          refine ⟨213929445829947405045328793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142619630553298270030219195 213929445829947405045328793)
          ·
            refine ⟨160447084372460553783996595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213929445829947405045328793 160447084372460553783996595)
            ·
              refine ⟨240670626558690830675994893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160447084372460553783996595 240670626558690830675994893)
              ·
                refine ⟨90251484959509061503498085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240670626558690830675994893 90251484959509061503498085)
                ·
                  refine ⟨16922153429907949031905891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90251484959509061503498085 16922153429907949031905891)
                  ·
                    refine ⟨25383230144861923547858837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16922153429907949031905891 25383230144861923547858837)
                    ·
                      refine ⟨1189838913040402666305883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25383230144861923547858837 1189838913040402666305883)
                      ·
                        rfl

theorem cell23_2317203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_2317203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317203 prefixEnd_2317203 := by exact prefixLift 2317203
  have htrace : WordTrace (prefixWord ++ tailWord_2317203) baseStart_2317203 baseEnd_2317203 := by
    simpa [prefixWord, tailWord_2317203, baseEnd_2317203] using wordTrace_append hprefix tailTrace_2317203
  have hstable : (prefixWord ++ tailWord_2317203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317203).length < 2 ^ (prefixWord ++ tailWord_2317203).sum := by decide
  have hdescent : baseEnd_2317203 < baseStart_2317203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317207 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 2, 4, 2]
def baseStart_2317207 : Nat := 118140960795 + 2317207 * 2 ^ 59
def prefixEnd_2317207 : Nat := 4983230072969 + 3 ^ 40 * 2317207 * 2
def baseEnd_2317207 : Nat := 1189840966963020650655865

theorem tailTrace_2317207 : CollatzResearch.WordTrace tailWord_2317207 prefixEnd_2317207 1189840966963020650655865 := by
  unfold tailWord_2317207
  simp only [CollatzResearch.WordTrace]
  refine ⟨84515482516162261293645875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56343655010774840862430583 84515482516162261293645875)
  ·
    refine ⟨126773223774243391940468813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84515482516162261293645875 126773223774243391940468813)
    ·
      refine ⟨47539958915341271977675805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126773223774243391940468813 47539958915341271977675805)
      ·
        refine ⟨17827484593252976991628427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47539958915341271977675805 17827484593252976991628427)
        ·
          refine ⟨26741226889879465487442641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17827484593252976991628427 26741226889879465487442641)
          ·
            refine ⟨20055920167409599115581981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26741226889879465487442641 20055920167409599115581981)
            ·
              refine ⟨7520970062778599668343243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20055920167409599115581981 7520970062778599668343243)
              ·
                refine ⟨11281455094167899502514865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7520970062778599668343243 11281455094167899502514865)
                ·
                  refine ⟨8461091320625924626886149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11281455094167899502514865 8461091320625924626886149)
                  ·
                    refine ⟨1586454622617360867541153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8461091320625924626886149 1586454622617360867541153)
                    ·
                      refine ⟨1189840966963020650655865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1586454622617360867541153 1189840966963020650655865)
                      ·
                        rfl

theorem cell23_2317207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_2317207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317207 prefixEnd_2317207 := by exact prefixLift 2317207
  have htrace : WordTrace (prefixWord ++ tailWord_2317207) baseStart_2317207 baseEnd_2317207 := by
    simpa [prefixWord, tailWord_2317207, baseEnd_2317207] using wordTrace_append hprefix tailTrace_2317207
  have hstable : (prefixWord ++ tailWord_2317207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317207).length < 2 ^ (prefixWord ++ tailWord_2317207).sum := by decide
  have hdescent : baseEnd_2317207 < baseStart_2317207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317217 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2317217 : Nat := 118140960795 + 2317217 * 2 ^ 59
def prefixEnd_2317217 : Nat := 4983230072969 + 3 ^ 40 * 2317217 * 2
def baseEnd_2317217 : Nat := 396615367256521870510273

theorem tailTrace_2317217 : CollatzResearch.WordTrace tailWord_2317217 prefixEnd_2317217 396615367256521870510273 := by
  unfold tailWord_2317217
  simp only [CollatzResearch.WordTrace]
  refine ⟨84515847246126033001509905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56343898164084022001006603 84515847246126033001509905)
  ·
    refine ⟨63386885434594524751132429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84515847246126033001509905 63386885434594524751132429)
    ·
      refine ⟨23770082037972946781674661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63386885434594524751132429 23770082037972946781674661)
      ·
        refine ⟨4456890382119927521563999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23770082037972946781674661 4456890382119927521563999)
        ·
          refine ⟨6685335573179891282345999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456890382119927521563999 6685335573179891282345999)
          ·
            refine ⟨10028003359769836923518999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6685335573179891282345999 10028003359769836923518999)
            ·
              refine ⟨15042005039654755385278499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10028003359769836923518999 15042005039654755385278499)
              ·
                refine ⟨22563007559482133077917749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15042005039654755385278499 22563007559482133077917749)
                ·
                  refine ⟨2115281958701449976054789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22563007559482133077917749 2115281958701449976054789)
                  ·
                    refine ⟨396615367256521870510273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2115281958701449976054789 396615367256521870510273)
                    ·
                      rfl

theorem cell23_2317217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2317217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317217 prefixEnd_2317217 := by exact prefixLift 2317217
  have htrace : WordTrace (prefixWord ++ tailWord_2317217) baseStart_2317217 baseEnd_2317217 := by
    simpa [prefixWord, tailWord_2317217, baseEnd_2317217] using wordTrace_append hprefix tailTrace_2317217
  have hstable : (prefixWord ++ tailWord_2317217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317217).length < 2 ^ (prefixWord ++ tailWord_2317217).sum := by decide
  have hdescent : baseEnd_2317217 < baseStart_2317217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317243 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 11]
def baseStart_2317243 : Nat := 118140960795 + 2317243 * 2 ^ 59
def prefixEnd_2317243 : Nat := 4983230072969 + 3 ^ 40 * 2317243 * 2
def baseEnd_2317243 : Nat := 396619817422194169935233

theorem tailTrace_2317243 : CollatzResearch.WordTrace tailWord_2317243 prefixEnd_2317243 396619817422194169935233 := by
  unfold tailWord_2317243
  simp only [CollatzResearch.WordTrace]
  refine ⟨84516795544031839441956383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56344530362687892961304255 84516795544031839441956383)
  ·
    refine ⟨126775193316047759162934575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84516795544031839441956383 126775193316047759162934575)
    ·
      refine ⟨190162789974071638744401863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126775193316047759162934575 190162789974071638744401863)
      ·
        refine ⟨285244184961107458116602795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190162789974071638744401863 285244184961107458116602795)
        ·
          refine ⟨427866277441661187174904193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285244184961107458116602795 427866277441661187174904193)
          ·
            refine ⟨320899708081245890381178145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427866277441661187174904193 320899708081245890381178145)
            ·
              refine ⟨240674781060934417785883609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320899708081245890381178145 240674781060934417785883609)
              ·
                refine ⟨180506085795700813339412707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240674781060934417785883609 180506085795700813339412707)
                ·
                  refine ⟨270759128693551220009119061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180506085795700813339412707 270759128693551220009119061)
                  ·
                    refine ⟨396619817422194169935233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 270759128693551220009119061 396619817422194169935233)
                    ·
                      rfl

theorem cell23_2317243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 11].length) (baseStart_2317243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317243 prefixEnd_2317243 := by exact prefixLift 2317243
  have htrace : WordTrace (prefixWord ++ tailWord_2317243) baseStart_2317243 baseEnd_2317243 := by
    simpa [prefixWord, tailWord_2317243, baseEnd_2317243] using wordTrace_append hprefix tailTrace_2317243
  have hstable : (prefixWord ++ tailWord_2317243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317243).length < 2 ^ (prefixWord ++ tailWord_2317243).sum := by decide
  have hdescent : baseEnd_2317243 < baseStart_2317243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317274 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_2317274 : Nat := 118140960795 + 2317274 * 2 ^ 59
def prefixEnd_2317274 : Nat := 4983230072969 + 3 ^ 40 * 2317274 * 2
def baseEnd_2317274 : Nat := 1189875370166871888518057

theorem tailTrace_2317274 : CollatzResearch.WordTrace tailWord_2317274 prefixEnd_2317274 1189875370166871888518057 := by
  unfold tailWord_2317274
  simp only [CollatzResearch.WordTrace]
  refine ⟨21129481551729882934083719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56345284137946354490889917 21129481551729882934083719)
  ·
    refine ⟨31694222327594824401125579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21129481551729882934083719 31694222327594824401125579)
    ·
      refine ⟨47541333491392236601688369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31694222327594824401125579 47541333491392236601688369)
      ·
        refine ⟨35656000118544177451266277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47541333491392236601688369 35656000118544177451266277)
        ·
          refine ⟨6685500022227033272112427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35656000118544177451266277 6685500022227033272112427)
          ·
            refine ⟨10028250033340549908168641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6685500022227033272112427 10028250033340549908168641)
            ·
              refine ⟨7521187525005412431126481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10028250033340549908168641 7521187525005412431126481)
              ·
                refine ⟨5640890643754059323344861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7521187525005412431126481 5640890643754059323344861)
                ·
                  refine ⟨2115333991407772246254323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5640890643754059323344861 2115333991407772246254323)
                  ·
                    refine ⟨3173000987111658369381485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2115333991407772246254323 3173000987111658369381485)
                    ·
                      refine ⟨1189875370166871888518057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173000987111658369381485 1189875370166871888518057)
                      ·
                        rfl

theorem cell23_2317274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_2317274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317274 prefixEnd_2317274 := by exact prefixLift 2317274
  have htrace : WordTrace (prefixWord ++ tailWord_2317274) baseStart_2317274 baseEnd_2317274 := by
    simpa [prefixWord, tailWord_2317274, baseEnd_2317274] using wordTrace_append hprefix tailTrace_2317274
  have hstable : (prefixWord ++ tailWord_2317274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317274).length < 2 ^ (prefixWord ++ tailWord_2317274).sum := by decide
  have hdescent : baseEnd_2317274 < baseStart_2317274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317285 : List Nat := [1, 3, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_2317285 : Nat := 118140960795 + 2317285 * 2 ^ 59
def prefixEnd_2317285 : Nat := 4983230072969 + 3 ^ 40 * 2317285 * 2
def baseEnd_2317285 : Nat := 396627006151357115160169

theorem tailTrace_2317285 : CollatzResearch.WordTrace tailWord_2317285 prefixEnd_2317285 396627006151357115160169 := by
  unfold tailWord_2317285
  simp only [CollatzResearch.WordTrace]
  refine ⟨84518327409879680614985309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56345551606586453743323539 84518327409879680614985309)
  ·
    refine ⟨31694372778704880230619491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84518327409879680614985309 31694372778704880230619491)
    ·
      refine ⟨47541559168057320345929237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31694372778704880230619491 47541559168057320345929237)
      ·
        refine ⟨2228510586002686891215433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47541559168057320345929237 2228510586002686891215433)
        ·
          refine ⟨1671382939502015168411575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2228510586002686891215433 1671382939502015168411575)
          ·
            refine ⟨2507074409253022752617363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671382939502015168411575 2507074409253022752617363)
            ·
              refine ⟨3760611613879534128926045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507074409253022752617363 3760611613879534128926045)
              ·
                refine ⟨1410229355204825298347267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3760611613879534128926045 1410229355204825298347267)
                ·
                  refine ⟨2115344032807237947520901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410229355204825298347267 2115344032807237947520901)
                  ·
                    refine ⟨396627006151357115160169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2115344032807237947520901 396627006151357115160169)
                    ·
                      rfl

theorem cell23_2317285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_2317285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317285 prefixEnd_2317285 := by exact prefixLift 2317285
  have htrace : WordTrace (prefixWord ++ tailWord_2317285) baseStart_2317285 baseEnd_2317285 := by
    simpa [prefixWord, tailWord_2317285, baseEnd_2317285] using wordTrace_append hprefix tailTrace_2317285
  have hstable : (prefixWord ++ tailWord_2317285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317285).length < 2 ^ (prefixWord ++ tailWord_2317285).sum := by decide
  have hdescent : baseEnd_2317285 < baseStart_2317285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317307 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 2, 4]
def baseStart_2317307 : Nat := 118140960795 + 2317307 * 2 ^ 59
def prefixEnd_2317307 : Nat := 4983230072969 + 3 ^ 40 * 2317307 * 2
def baseEnd_2317307 : Nat := 396630771676156753135135

theorem tailTrace_2317307 : CollatzResearch.WordTrace tailWord_2317307 prefixEnd_2317307 396630771676156753135135 := by
  unfold tailWord_2317307
  simp only [CollatzResearch.WordTrace]
  refine ⟨84519129815799978372286175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56346086543866652248190783 84519129815799978372286175)
  ·
    refine ⟨126778694723699967558429263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84519129815799978372286175 126778694723699967558429263)
    ·
      refine ⟨190168042085549951337643895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126778694723699967558429263 190168042085549951337643895)
      ·
        refine ⟨285252063128324927006465843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190168042085549951337643895 285252063128324927006465843)
        ·
          refine ⟨427878094692487390509698765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285252063128324927006465843 427878094692487390509698765)
          ·
            refine ⟨160454285509682771441137037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427878094692487390509698765 160454285509682771441137037)
            ·
              refine ⟨60170357066131039290426389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160454285509682771441137037 60170357066131039290426389)
              ·
                refine ⟨2820485487474892466738737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60170357066131039290426389 2820485487474892466738737)
                ·
                  refine ⟨2115364115606169350054053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2820485487474892466738737 2115364115606169350054053)
                  ·
                    refine ⟨396630771676156753135135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2115364115606169350054053 396630771676156753135135)
                    ·
                      rfl

theorem cell23_2317307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 4].length) (baseStart_2317307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317307 prefixEnd_2317307 := by exact prefixLift 2317307
  have htrace : WordTrace (prefixWord ++ tailWord_2317307) baseStart_2317307 baseEnd_2317307 := by
    simpa [prefixWord, tailWord_2317307, baseEnd_2317307] using wordTrace_append hprefix tailTrace_2317307
  have hstable : (prefixWord ++ tailWord_2317307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317307).length < 2 ^ (prefixWord ++ tailWord_2317307).sum := by decide
  have hdescent : baseEnd_2317307 < baseStart_2317307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317308 : List Nat := [2, 2, 2, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_2317308 : Nat := 118140960795 + 2317308 * 2 ^ 59
def prefixEnd_2317308 : Nat := 4983230072969 + 3 ^ 40 * 2317308 * 2
def baseEnd_2317308 : Nat := 1189892828509124755492901

theorem tailTrace_2317308 : CollatzResearch.WordTrace tailWord_2317308 prefixEnd_2317308 1189892828509124755492901 := by
  unfold tailWord_2317308
  simp only [CollatzResearch.WordTrace]
  refine ⟨42259583144398177771536289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56346110859197570362048385 42259583144398177771536289)
  ·
    refine ⟨31694687358298633328652217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42259583144398177771536289 31694687358298633328652217)
    ·
      refine ⟨23771015518723974996489163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31694687358298633328652217 23771015518723974996489163)
      ·
        refine ⟨35656523278085962494733745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23771015518723974996489163 35656523278085962494733745)
        ·
          refine ⟨26742392458564471871050309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35656523278085962494733745 26742392458564471871050309)
          ·
            refine ⟨5014198585980838475821933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26742392458564471871050309 5014198585980838475821933)
            ·
              refine ⟨1880324469742814428433225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5014198585980838475821933 1880324469742814428433225)
              ·
                refine ⟨1410243352307110821324919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880324469742814428433225 1410243352307110821324919)
                ·
                  refine ⟨2115365028460666231987379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410243352307110821324919 2115365028460666231987379)
                  ·
                    refine ⟨3173047542690999347981069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2115365028460666231987379 3173047542690999347981069)
                    ·
                      refine ⟨1189892828509124755492901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173047542690999347981069 1189892828509124755492901)
                      ·
                        rfl

theorem cell23_2317308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_2317308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317308 prefixEnd_2317308 := by exact prefixLift 2317308
  have htrace : WordTrace (prefixWord ++ tailWord_2317308) baseStart_2317308 baseEnd_2317308 := by
    simpa [prefixWord, tailWord_2317308, baseEnd_2317308] using wordTrace_append hprefix tailTrace_2317308
  have hstable : (prefixWord ++ tailWord_2317308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317308).length < 2 ^ (prefixWord ++ tailWord_2317308).sum := by decide
  have hdescent : baseEnd_2317308 < baseStart_2317308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317317 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_2317317 : Nat := 118140960795 + 2317317 * 2 ^ 59
def prefixEnd_2317317 : Nat := 4983230072969 + 3 ^ 40 * 2317317 * 2
def baseEnd_2317317 : Nat := 1189897449835015220280359

theorem tailTrace_2317317 : CollatzResearch.WordTrace tailWord_2317317 prefixEnd_2317317 1189897449835015220280359 := by
  unfold tailWord_2317317
  simp only [CollatzResearch.WordTrace]
  refine ⟨84519494545763750080150205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56346329697175833386766803 84519494545763750080150205)
  ·
    refine ⟨31694810454661406280056327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84519494545763750080150205 31694810454661406280056327)
    ·
      refine ⟨47542215681992109420084491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31694810454661406280056327 47542215681992109420084491)
      ·
        refine ⟨71313323522988164130126737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47542215681992109420084491 71313323522988164130126737)
        ·
          refine ⟨53484992642241123097595053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71313323522988164130126737 53484992642241123097595053)
          ·
            refine ⟨20056872240840421161598145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53484992642241123097595053 20056872240840421161598145)
            ·
              refine ⟨15042654180630315871198609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20056872240840421161598145 15042654180630315871198609)
              ·
                refine ⟨11281990635472736903398957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15042654180630315871198609 11281990635472736903398957)
                ·
                  refine ⟨4230746488302276338774609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11281990635472736903398957 4230746488302276338774609)
                  ·
                    refine ⟨3173059866226707254080957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4230746488302276338774609 3173059866226707254080957)
                    ·
                      refine ⟨1189897449835015220280359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173059866226707254080957 1189897449835015220280359)
                      ·
                        rfl

theorem cell23_2317317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_2317317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317317 prefixEnd_2317317 := by exact prefixLift 2317317
  have htrace : WordTrace (prefixWord ++ tailWord_2317317) baseStart_2317317 baseEnd_2317317 := by
    simpa [prefixWord, tailWord_2317317, baseEnd_2317317] using wordTrace_append hprefix tailTrace_2317317
  have hstable : (prefixWord ++ tailWord_2317317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317317).length < 2 ^ (prefixWord ++ tailWord_2317317).sum := by decide
  have hdescent : baseEnd_2317317 < baseStart_2317317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317320 : List Nat := [2, 1, 3, 2, 1, 3, 1, 10]
def baseStart_2317320 : Nat := 118140960795 + 2317320 * 2 ^ 59
def prefixEnd_2317320 : Nat := 4983230072969 + 3 ^ 40 * 2317320 * 2
def baseEnd_2317320 : Nat := 44070332973221433649735

theorem tailTrace_2317320 : CollatzResearch.WordTrace tailWord_2317320 prefixEnd_2317320 44070332973221433649735 := by
  unfold tailWord_2317320
  simp only [CollatzResearch.WordTrace]
  refine ⟨42259801982376440796254707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56346402643168587728339609 42259801982376440796254707)
  ·
    refine ⟨63389702973564661194382061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42259801982376440796254707 63389702973564661194382061)
    ·
      refine ⟨23771138615086747947893273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63389702973564661194382061 23771138615086747947893273)
      ·
        refine ⟨17828353961315060960919955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23771138615086747947893273 17828353961315060960919955)
        ·
          refine ⟨26742530941972591441379933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17828353961315060960919955 26742530941972591441379933)
          ·
            refine ⟨10028449103239721790517475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26742530941972591441379933 10028449103239721790517475)
            ·
              refine ⟨15042673654859582685776213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10028449103239721790517475 15042673654859582685776213)
              ·
                refine ⟨44070332973221433649735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15042673654859582685776213 44070332973221433649735)
                ·
                  rfl

theorem cell23_2317320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 10].length) (baseStart_2317320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317320 prefixEnd_2317320 := by exact prefixLift 2317320
  have htrace : WordTrace (prefixWord ++ tailWord_2317320) baseStart_2317320 baseEnd_2317320 := by
    simpa [prefixWord, tailWord_2317320, baseEnd_2317320] using wordTrace_append hprefix tailTrace_2317320
  have hstable : (prefixWord ++ tailWord_2317320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317320).length < 2 ^ (prefixWord ++ tailWord_2317320).sum := by decide
  have hdescent : baseEnd_2317320 < baseStart_2317320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317324 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_2317324 : Nat := 118140960795 + 2317324 * 2 ^ 59
def prefixEnd_2317324 : Nat := 4983230072969 + 3 ^ 40 * 2317324 * 2
def baseEnd_2317324 : Nat := 396633681399865564297609

theorem tailTrace_2317324 : CollatzResearch.WordTrace tailWord_2317324 prefixEnd_2317324 396633681399865564297609 := by
  unfold tailWord_2317324
  simp only [CollatzResearch.WordTrace]
  refine ⟨42259874928369195137827513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56346499904492260183770017 42259874928369195137827513)
  ·
    refine ⟨31694906196276896353370635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42259874928369195137827513 31694906196276896353370635)
    ·
      refine ⟨47542359294415344530055953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31694906196276896353370635 47542359294415344530055953)
      ·
        refine ⟨35656769470811508397541965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47542359294415344530055953 35656769470811508397541965)
        ·
          refine ⟨13371288551554315649078237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35656769470811508397541965 13371288551554315649078237)
          ·
            refine ⟨5014233206832868368404339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13371288551554315649078237 5014233206832868368404339)
            ·
              refine ⟨7521349810249302552606509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5014233206832868368404339 7521349810249302552606509)
              ·
                refine ⟨2820506178843488457227441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7521349810249302552606509 2820506178843488457227441)
                ·
                  refine ⟨2115379634132616342920581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2820506178843488457227441 2115379634132616342920581)
                  ·
                    refine ⟨396633681399865564297609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2115379634132616342920581 396633681399865564297609)
                    ·
                      rfl

theorem cell23_2317324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_2317324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317324 prefixEnd_2317324 := by exact prefixLift 2317324
  have htrace : WordTrace (prefixWord ++ tailWord_2317324) baseStart_2317324 baseEnd_2317324 := by
    simpa [prefixWord, tailWord_2317324, baseEnd_2317324] using wordTrace_append hprefix tailTrace_2317324
  have hstable : (prefixWord ++ tailWord_2317324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317324).length < 2 ^ (prefixWord ++ tailWord_2317324).sum := by decide
  have hdescent : baseEnd_2317324 < baseStart_2317324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317347 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 3]
def baseStart_2317347 : Nat := 118140960795 + 2317347 * 2 ^ 59
def prefixEnd_2317347 : Nat := 4983230072969 + 3 ^ 40 * 2317347 * 2
def baseEnd_2317347 : Nat := 1189912854254650102905221

theorem tailTrace_2317347 : CollatzResearch.WordTrace tailWord_2317347 prefixEnd_2317347 1189912854254650102905221 := by
  unfold tailWord_2317347
  simp only [CollatzResearch.WordTrace]
  refine ⟨84520588735655065203742295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56347059157103376802494863 84520588735655065203742295)
  ·
    refine ⟨126780883103482597805613443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84520588735655065203742295 126780883103482597805613443)
    ·
      refine ⟨190171324655223896708420165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126780883103482597805613443 190171324655223896708420165)
      ·
        refine ⟨35657123372854480632828781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190171324655223896708420165 35657123372854480632828781)
        ·
          refine ⟨13371421264820430237310793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35657123372854480632828781 13371421264820430237310793)
          ·
            refine ⟨10028565948615322677983095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13371421264820430237310793 10028565948615322677983095)
            ·
              refine ⟨15042848922922984016974643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10028565948615322677983095 15042848922922984016974643)
              ·
                refine ⟨22564273384384476025461965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15042848922922984016974643 22564273384384476025461965)
                ·
                  refine ⟨8461602519144178509548237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22564273384384476025461965 8461602519144178509548237)
                  ·
                    refine ⟨3173100944679066941080589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8461602519144178509548237 3173100944679066941080589)
                    ·
                      refine ⟨1189912854254650102905221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173100944679066941080589 1189912854254650102905221)
                      ·
                        rfl

theorem cell23_2317347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_2317347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317347 prefixEnd_2317347 := by exact prefixLift 2317347
  have htrace : WordTrace (prefixWord ++ tailWord_2317347) baseStart_2317347 baseEnd_2317347 := by
    simpa [prefixWord, tailWord_2317347, baseEnd_2317347] using wordTrace_append hprefix tailTrace_2317347
  have hstable : (prefixWord ++ tailWord_2317347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317347).length < 2 ^ (prefixWord ++ tailWord_2317347).sum := by decide
  have hdescent : baseEnd_2317347 < baseStart_2317347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317351 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2317351 : Nat := 118140960795 + 2317351 * 2 ^ 59
def prefixEnd_2317351 : Nat := 4983230072969 + 3 ^ 40 * 2317351 * 2
def baseEnd_2317351 : Nat := 1189914908177268087255203

theorem tailTrace_2317351 : CollatzResearch.WordTrace tailWord_2317351 prefixEnd_2317351 1189914908177268087255203 := by
  unfold tailWord_2317351
  simp only [CollatzResearch.WordTrace]
  refine ⟨84520734627640573886887907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56347156418427049257925271 84520734627640573886887907)
  ·
    refine ⟨126781101941460860830331861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84520734627640573886887907 126781101941460860830331861)
    ·
      refine ⟨2971432076752988925710903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 126781101941460860830331861 2971432076752988925710903)
      ·
        refine ⟨4457148115129483388566355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2971432076752988925710903 4457148115129483388566355)
        ·
          refine ⟨6685722172694225082849533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4457148115129483388566355 6685722172694225082849533)
          ·
            refine ⟨2507145814760334406068575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6685722172694225082849533 2507145814760334406068575)
            ·
              refine ⟨3760718722140501609102863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507145814760334406068575 3760718722140501609102863)
              ·
                refine ⟨5641078083210752413654295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760718722140501609102863 5641078083210752413654295)
                ·
                  refine ⟨8461617124816128620481443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5641078083210752413654295 8461617124816128620481443)
                  ·
                    refine ⟨12692425687224192930722165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8461617124816128620481443 12692425687224192930722165)
                    ·
                      refine ⟨1189914908177268087255203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12692425687224192930722165 1189914908177268087255203)
                      ·
                        rfl

theorem cell23_2317351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2317351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317351 prefixEnd_2317351 := by exact prefixLift 2317351
  have htrace : WordTrace (prefixWord ++ tailWord_2317351) baseStart_2317351 baseEnd_2317351 := by
    simpa [prefixWord, tailWord_2317351, baseEnd_2317351] using wordTrace_append hprefix tailTrace_2317351
  have hstable : (prefixWord ++ tailWord_2317351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317351).length < 2 ^ (prefixWord ++ tailWord_2317351).sum := by decide
  have hdescent : baseEnd_2317351 < baseStart_2317351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317417 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_2317417 : Nat := 118140960795 + 2317417 * 2 ^ 59
def prefixEnd_2317417 : Nat := 4983230072969 + 3 ^ 40 * 2317417 * 2
def baseEnd_2317417 : Nat := 1189948797900464829029899

theorem tailTrace_2317417 : CollatzResearch.WordTrace tailWord_2317417 prefixEnd_2317417 1189948797900464829029899 := by
  unfold tailWord_2317417
  simp only [CollatzResearch.WordTrace]
  refine ⟨84523141845401467158790505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56348761230267644772527003 84523141845401467158790505)
  ·
    refine ⟨63392356384051100369092879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84523141845401467158790505 63392356384051100369092879)
    ·
      refine ⟨95088534576076650553639319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63392356384051100369092879 95088534576076650553639319)
      ·
        refine ⟨142632801864114975830458979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95088534576076650553639319 142632801864114975830458979)
        ·
          refine ⟨213949202796172463745688469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142632801864114975830458979 213949202796172463745688469)
          ·
            refine ⟨10028868881070584238079147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213949202796172463745688469 10028868881070584238079147)
            ·
              refine ⟨15043303321605876357118721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10028868881070584238079147 15043303321605876357118721)
              ·
                refine ⟨11282477491204407267839041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15043303321605876357118721 11282477491204407267839041)
                ·
                  refine ⟨8461858118403305450879281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11282477491204407267839041 8461858118403305450879281)
                  ·
                    refine ⟨6346393588802479088159461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8461858118403305450879281 6346393588802479088159461)
                    ·
                      refine ⟨1189948797900464829029899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6346393588802479088159461 1189948797900464829029899)
                      ·
                        rfl

theorem cell23_2317417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_2317417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317417 prefixEnd_2317417 := by exact prefixLift 2317417
  have htrace : WordTrace (prefixWord ++ tailWord_2317417) baseStart_2317417 baseEnd_2317417 := by
    simpa [prefixWord, tailWord_2317417, baseEnd_2317417] using wordTrace_append hprefix tailTrace_2317417
  have hstable : (prefixWord ++ tailWord_2317417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317417).length < 2 ^ (prefixWord ++ tailWord_2317417).sum := by decide
  have hdescent : baseEnd_2317417 < baseStart_2317417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317521 : List Nat := [1, 2, 2, 1, 2, 2, 1, 7, 1, 4]
def baseStart_2317521 : Nat := 118140960795 + 2317521 * 2 ^ 59
def prefixEnd_2317521 : Nat := 4983230072969 + 3 ^ 40 * 2317521 * 2
def baseEnd_2317521 : Nat := 396667399962844140709807

theorem tailTrace_2317521 : CollatzResearch.WordTrace tailWord_2317521 prefixEnd_2317521 396667399962844140709807 := by
  unfold tailWord_2317521
  simp only [CollatzResearch.WordTrace]
  refine ⟨84526935037024692920576417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56351290024683128613717611 84526935037024692920576417)
  ·
    refine ⟨63395201277768519690432313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84526935037024692920576417 63395201277768519690432313)
    ·
      refine ⟨47546400958326389767824235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63395201277768519690432313 47546400958326389767824235)
      ·
        refine ⟨71319601437489584651736353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47546400958326389767824235 71319601437489584651736353)
        ·
          refine ⟨53489701078117188488802265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71319601437489584651736353 53489701078117188488802265)
          ·
            refine ⟨40117275808587891366601699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53489701078117188488802265 40117275808587891366601699)
            ·
              refine ⟨60175913712881837049902549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40117275808587891366601699 60175913712881837049902549)
              ·
                refine ⟨1410372977645668055857091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60175913712881837049902549 1410372977645668055857091)
                ·
                  refine ⟨2115559466468502083785637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410372977645668055857091 2115559466468502083785637)
                  ·
                    refine ⟨396667399962844140709807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2115559466468502083785637 396667399962844140709807)
                    ·
                      rfl

theorem cell23_2317521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_2317521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317521 prefixEnd_2317521 := by exact prefixLift 2317521
  have htrace : WordTrace (prefixWord ++ tailWord_2317521) baseStart_2317521 baseEnd_2317521 := by
    simpa [prefixWord, tailWord_2317521, baseEnd_2317521] using wordTrace_append hprefix tailTrace_2317521
  have hstable : (prefixWord ++ tailWord_2317521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317521).length < 2 ^ (prefixWord ++ tailWord_2317521).sum := by decide
  have hdescent : baseEnd_2317521 < baseStart_2317521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317561 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 3]
def baseStart_2317561 : Nat := 118140960795 + 2317561 * 2 ^ 59
def prefixEnd_2317561 : Nat := 4983230072969 + 3 ^ 40 * 2317561 * 2
def baseEnd_2317561 : Nat := 1190022739114712265629237

theorem tailTrace_2317561 : CollatzResearch.WordTrace tailWord_2317561 prefixEnd_2317561 1190022739114712265629237 := by
  unfold tailWord_2317561
  simp only [CollatzResearch.WordTrace]
  refine ⟨84528393956879779752032537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56352262637919853168021691 84528393956879779752032537)
  ·
    refine ⟨63396295467659834814024403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84528393956879779752032537 63396295467659834814024403)
    ·
      refine ⟨95094443201489752221036605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63396295467659834814024403 95094443201489752221036605)
      ·
        refine ⟨35660416200558657082888727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95094443201489752221036605 35660416200558657082888727)
        ·
          refine ⟨53490624300837985624333091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35660416200558657082888727 53490624300837985624333091)
          ·
            refine ⟨80235936451256978436499637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53490624300837985624333091 80235936451256978436499637)
            ·
              refine ⟨7522119042305341728421841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80235936451256978436499637 7522119042305341728421841)
              ·
                refine ⟨5641589281729006296316381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7522119042305341728421841 5641589281729006296316381)
                ·
                  refine ⟨2115595980648377361118643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5641589281729006296316381 2115595980648377361118643)
                  ·
                    refine ⟨3173393970972566041677965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2115595980648377361118643 3173393970972566041677965)
                    ·
                      refine ⟨1190022739114712265629237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173393970972566041677965 1190022739114712265629237)
                      ·
                        rfl

theorem cell23_2317561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_2317561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317561 prefixEnd_2317561 := by exact prefixLift 2317561
  have htrace : WordTrace (prefixWord ++ tailWord_2317561) baseStart_2317561 baseEnd_2317561 := by
    simpa [prefixWord, tailWord_2317561, baseEnd_2317561] using wordTrace_append hprefix tailTrace_2317561
  have hstable : (prefixWord ++ tailWord_2317561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317561).length < 2 ^ (prefixWord ++ tailWord_2317561).sum := by decide
  have hdescent : baseEnd_2317561 < baseStart_2317561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317571 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 1, 5, 2]
def baseStart_2317571 : Nat := 118140960795 + 2317571 * 2 ^ 59
def prefixEnd_2317571 : Nat := 4983230072969 + 3 ^ 40 * 2317571 * 2
def baseEnd_2317571 : Nat := 1190027873921257226504191

theorem tailTrace_2317571 : CollatzResearch.WordTrace tailWord_2317571 prefixEnd_2317571 1190027873921257226504191 := by
  unfold tailWord_2317571
  simp only [CollatzResearch.WordTrace]
  refine ⟨84528758686843551459896567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56352505791229034306597711 84528758686843551459896567)
  ·
    refine ⟨126793138030265327189844851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84528758686843551459896567 126793138030265327189844851)
    ·
      refine ⟨190189707045397990784767277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126793138030265327189844851 190189707045397990784767277)
      ·
        refine ⟨71321140142024246544287729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190189707045397990784767277 71321140142024246544287729)
        ·
          refine ⟨53490855106518184908215797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71321140142024246544287729 53490855106518184908215797)
          ·
            refine ⟨5014767666236079835145231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53490855106518184908215797 5014767666236079835145231)
            ·
              refine ⟨7522151499354119752717847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5014767666236079835145231 7522151499354119752717847)
              ·
                refine ⟨11283227249031179629076771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522151499354119752717847 11283227249031179629076771)
                ·
                  refine ⟨16924840873546769443615157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11283227249031179629076771 16924840873546769443615157)
                  ·
                    refine ⟨1586703831895009635338921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16924840873546769443615157 1586703831895009635338921)
                    ·
                      refine ⟨1190027873921257226504191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1586703831895009635338921 1190027873921257226504191)
                      ·
                        rfl

theorem cell23_2317571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_2317571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317571 prefixEnd_2317571 := by exact prefixLift 2317571
  have htrace : WordTrace (prefixWord ++ tailWord_2317571) baseStart_2317571 baseEnd_2317571 := by
    simpa [prefixWord, tailWord_2317571, baseEnd_2317571] using wordTrace_append hprefix tailTrace_2317571
  have hstable : (prefixWord ++ tailWord_2317571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317571).length < 2 ^ (prefixWord ++ tailWord_2317571).sum := by decide
  have hdescent : baseEnd_2317571 < baseStart_2317571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317618 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_2317618 : Nat := 118140960795 + 2317618 * 2 ^ 59
def prefixEnd_2317618 : Nat := 4983230072969 + 3 ^ 40 * 2317618 * 2
def baseEnd_2317618 : Nat := 1190052007512018542616475

theorem tailTrace_2317618 : CollatzResearch.WordTrace tailWord_2317618 prefixEnd_2317618 1190052007512018542616475 := by
  unfold tailWord_2317618
  simp only [CollatzResearch.WordTrace]
  refine ⟨21132618229418319621714377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56353648611782185657905005 21132618229418319621714377)
  ·
    refine ⟨15849463672063739716285783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21132618229418319621714377 15849463672063739716285783)
    ·
      refine ⟨23774195508095609574428675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15849463672063739716285783 23774195508095609574428675)
      ·
        refine ⟨35661293262143414361643013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23774195508095609574428675 35661293262143414361643013)
        ·
          refine ⟨6686492486651890192808065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35661293262143414361643013 6686492486651890192808065)
          ·
            refine ⟨5014869364988917644606049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6686492486651890192808065 5014869364988917644606049)
            ·
              refine ⟨3761152023741688233454537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5014869364988917644606049 3761152023741688233454537)
              ·
                refine ⟨2820864017806266175090903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3761152023741688233454537 2820864017806266175090903)
                ·
                  refine ⟨4231296026709399262636355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2820864017806266175090903 4231296026709399262636355)
                  ·
                    refine ⟨6346944040064098893954533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4231296026709399262636355 6346944040064098893954533)
                    ·
                      refine ⟨1190052007512018542616475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6346944040064098893954533 1190052007512018542616475)
                      ·
                        rfl

theorem cell23_2317618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_2317618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317618 prefixEnd_2317618 := by exact prefixLift 2317618
  have htrace : WordTrace (prefixWord ++ tailWord_2317618) baseStart_2317618 baseEnd_2317618 := by
    simpa [prefixWord, tailWord_2317618, baseEnd_2317618] using wordTrace_append hprefix tailTrace_2317618
  have hstable : (prefixWord ++ tailWord_2317618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317618).length < 2 ^ (prefixWord ++ tailWord_2317618).sum := by decide
  have hdescent : baseEnd_2317618 < baseStart_2317618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317629 : List Nat := [1, 4, 1, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2317629 : Nat := 118140960795 + 2317629 * 2 ^ 59
def prefixEnd_2317629 : Nat := 4983230072969 + 3 ^ 40 * 2317629 * 2
def baseEnd_2317629 : Nat := 1190057655799217999578925

theorem tailTrace_2317629 : CollatzResearch.WordTrace tailWord_2317629 prefixEnd_2317629 1190057655799217999578925 := by
  unfold tailWord_2317629
  simp only [CollatzResearch.WordTrace]
  refine ⟨84530874120633427365507941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56353916080422284910338627 84530874120633427365507941)
  ·
    refine ⟨15849538897618767631032739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84530874120633427365507941 15849538897618767631032739)
    ·
      refine ⟨23774308346428151446549109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15849538897618767631032739 23774308346428151446549109)
      ·
        refine ⟨2228841407477639198113979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23774308346428151446549109 2228841407477639198113979)
        ·
          refine ⟨3343262111216458797170969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228841407477639198113979 3343262111216458797170969)
          ·
            refine ⟨2507446583412344097878227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3343262111216458797170969 2507446583412344097878227)
            ·
              refine ⟨3761169875118516146817341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507446583412344097878227 3761169875118516146817341)
              ·
                refine ⟨1410438703169443555056503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3761169875118516146817341 1410438703169443555056503)
                ·
                  refine ⟨2115658054754165332584755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410438703169443555056503 2115658054754165332584755)
                  ·
                    refine ⟨3173487082131247998877133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2115658054754165332584755 3173487082131247998877133)
                    ·
                      refine ⟨1190057655799217999578925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173487082131247998877133 1190057655799217999578925)
                      ·
                        rfl

theorem cell23_2317629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2317629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317629 prefixEnd_2317629 := by exact prefixLift 2317629
  have htrace : WordTrace (prefixWord ++ tailWord_2317629) baseStart_2317629 baseEnd_2317629 := by
    simpa [prefixWord, tailWord_2317629, baseEnd_2317629] using wordTrace_append hprefix tailTrace_2317629
  have hstable : (prefixWord ++ tailWord_2317629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317629).length < 2 ^ (prefixWord ++ tailWord_2317629).sum := by decide
  have hdescent : baseEnd_2317629 < baseStart_2317629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317651 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 3]
def baseStart_2317651 : Nat := 118140960795 + 2317651 * 2 ^ 59
def prefixEnd_2317651 : Nat := 4983230072969 + 3 ^ 40 * 2317651 * 2
def baseEnd_2317651 : Nat := 1190068952373616913503823

theorem tailTrace_2317651 : CollatzResearch.WordTrace tailWord_2317651 prefixEnd_2317651 1190068952373616913503823 := by
  unfold tailWord_2317651
  simp only [CollatzResearch.WordTrace]
  refine ⟨84531676526553725122808807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56354451017702483415205871 84531676526553725122808807)
  ·
    refine ⟨126797514789830587684213211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84531676526553725122808807 126797514789830587684213211)
    ·
      refine ⟨190196272184745881526319817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126797514789830587684213211 190196272184745881526319817)
      ·
        refine ⟨142647204138559411144739863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190196272184745881526319817 142647204138559411144739863)
        ·
          refine ⟨213970806207839116717109795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142647204138559411144739863 213970806207839116717109795)
          ·
            refine ⟨320956209311758675075664693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213970806207839116717109795 320956209311758675075664693)
            ·
              refine ⟨30089644622977375788343565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 320956209311758675075664693 30089644622977375788343565)
              ·
                refine ⟨11283616733616515920628837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30089644622977375788343565 11283616733616515920628837)
                ·
                  refine ⟨2115678137553096735117907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11283616733616515920628837 2115678137553096735117907)
                  ·
                    refine ⟨3173517206329645102676861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2115678137553096735117907 3173517206329645102676861)
                    ·
                      refine ⟨1190068952373616913503823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173517206329645102676861 1190068952373616913503823)
                      ·
                        rfl

theorem cell23_2317651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 3].length) (baseStart_2317651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317651 prefixEnd_2317651 := by exact prefixLift 2317651
  have htrace : WordTrace (prefixWord ++ tailWord_2317651) baseStart_2317651 baseEnd_2317651 := by
    simpa [prefixWord, tailWord_2317651, baseEnd_2317651] using wordTrace_append hprefix tailTrace_2317651
  have hstable : (prefixWord ++ tailWord_2317651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317651).length < 2 ^ (prefixWord ++ tailWord_2317651).sum := by decide
  have hdescent : baseEnd_2317651 < baseStart_2317651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317672 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_2317672 : Nat := 118140960795 + 2317672 * 2 ^ 59
def prefixEnd_2317672 : Nat := 4983230072969 + 3 ^ 40 * 2317672 * 2
def baseEnd_2317672 : Nat := 1190079735467361331341227

theorem tailTrace_2317672 : CollatzResearch.WordTrace tailWord_2317672 prefixEnd_2317672 1190079735467361331341227 := by
  unfold tailWord_2317672
  simp only [CollatzResearch.WordTrace]
  refine ⟨42266221229738822854661635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56354961639651763806215513 42266221229738822854661635)
  ·
    refine ⟨63399331844608234281992453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42266221229738822854661635 63399331844608234281992453)
    ·
      refine ⟨11887374720864043927873585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63399331844608234281992453 11887374720864043927873585)
      ·
        refine ⟨8915531040648032945905189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11887374720864043927873585 8915531040648032945905189)
        ·
          refine ⟨1671662070121506177357223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8915531040648032945905189 1671662070121506177357223)
          ·
            refine ⟨2507493105182259266035835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671662070121506177357223 2507493105182259266035835)
            ·
              refine ⟨3761239657773388899053753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507493105182259266035835 3761239657773388899053753)
              ·
                refine ⟨2820929743330041674290315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3761239657773388899053753 2820929743330041674290315)
                ·
                  refine ⟨4231394614995062511435473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2820929743330041674290315 4231394614995062511435473)
                  ·
                    refine ⟨3173545961246296883576605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4231394614995062511435473 3173545961246296883576605)
                    ·
                      refine ⟨1190079735467361331341227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173545961246296883576605 1190079735467361331341227)
                      ·
                        rfl

theorem cell23_2317672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_2317672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317672 prefixEnd_2317672 := by exact prefixLift 2317672
  have htrace : WordTrace (prefixWord ++ tailWord_2317672) baseStart_2317672 baseEnd_2317672 := by
    simpa [prefixWord, tailWord_2317672, baseEnd_2317672] using wordTrace_append hprefix tailTrace_2317672
  have hstable : (prefixWord ++ tailWord_2317672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317672).length < 2 ^ (prefixWord ++ tailWord_2317672).sum := by decide
  have hdescent : baseEnd_2317672 < baseStart_2317672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317721 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_2317721 : Nat := 118140960795 + 2317721 * 2 ^ 59
def prefixEnd_2317721 : Nat := 4983230072969 + 3 ^ 40 * 2317721 * 2
def baseEnd_2317721 : Nat := 1190104896019431639628501

theorem tailTrace_2317721 : CollatzResearch.WordTrace tailWord_2317721 prefixEnd_2317721 1190104896019431639628501 := by
  unfold tailWord_2317721
  simp only [CollatzResearch.WordTrace]
  refine ⟨84534229636300127077857017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56356153090866751385238011 84534229636300127077857017)
  ·
    refine ⟨63400672227225095308392763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84534229636300127077857017 63400672227225095308392763)
    ·
      refine ⟨95101008340837642962589145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63400672227225095308392763 95101008340837642962589145)
      ·
        refine ⟨71325756255628232221941859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95101008340837642962589145 71325756255628232221941859)
        ·
          refine ⟨106988634383442348332912789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71325756255628232221941859 106988634383442348332912789)
          ·
            refine ⟨5015092236723860078105287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106988634383442348332912789 5015092236723860078105287)
            ·
              refine ⟨7522638355085790117157931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015092236723860078105287 7522638355085790117157931)
              ·
                refine ⟨11283957532628685175736897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522638355085790117157931 11283957532628685175736897)
                ·
                  refine ⟨8462968149471513881802673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11283957532628685175736897 8462968149471513881802673)
                  ·
                    refine ⟨6347226112103635411352005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8462968149471513881802673 6347226112103635411352005)
                    ·
                      refine ⟨1190104896019431639628501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6347226112103635411352005 1190104896019431639628501)
                      ·
                        rfl

theorem cell23_2317721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_2317721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317721 prefixEnd_2317721 := by exact prefixLift 2317721
  have htrace : WordTrace (prefixWord ++ tailWord_2317721) baseStart_2317721 baseEnd_2317721 := by
    simpa [prefixWord, tailWord_2317721, baseEnd_2317721] using wordTrace_append hprefix tailTrace_2317721
  have hstable : (prefixWord ++ tailWord_2317721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317721).length < 2 ^ (prefixWord ++ tailWord_2317721).sum := by decide
  have hdescent : baseEnd_2317721 < baseStart_2317721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317725 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_2317725 : Nat := 118140960795 + 2317725 * 2 ^ 59
def prefixEnd_2317725 : Nat := 4983230072969 + 3 ^ 40 * 2317725 * 2
def baseEnd_2317725 : Nat := 1190106949942049623978483

theorem tailTrace_2317725 : CollatzResearch.WordTrace tailWord_2317725 prefixEnd_2317725 1190106949942049623978483 := by
  unfold tailWord_2317725
  simp only [CollatzResearch.WordTrace]
  refine ⟨84534375528285635761002629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56356250352190423840668419 84534375528285635761002629)
  ·
    refine ⟨15850195411553556705187993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84534375528285635761002629 15850195411553556705187993)
    ·
      refine ⟨11887646558665167528890995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15850195411553556705187993 11887646558665167528890995)
      ·
        refine ⟨17831469837997751293336493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11887646558665167528890995 17831469837997751293336493)
        ·
          refine ⟨6686801189249156735001185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17831469837997751293336493 6686801189249156735001185)
          ·
            refine ⟨5015100891936867551250889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6686801189249156735001185 5015100891936867551250889)
            ·
              refine ⟨3761325668952650663438167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5015100891936867551250889 3761325668952650663438167)
              ·
                refine ⟨5641988503428975995157251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3761325668952650663438167 5641988503428975995157251)
                ·
                  refine ⟨8462982755143463992735877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5641988503428975995157251 8462982755143463992735877)
                  ·
                    refine ⟨1586809266589399498637977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8462982755143463992735877 1586809266589399498637977)
                    ·
                      refine ⟨1190106949942049623978483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1586809266589399498637977 1190106949942049623978483)
                      ·
                        rfl

theorem cell23_2317725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_2317725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317725 prefixEnd_2317725 := by exact prefixLift 2317725
  have htrace : WordTrace (prefixWord ++ tailWord_2317725) baseStart_2317725 baseEnd_2317725 := by
    simpa [prefixWord, tailWord_2317725, baseEnd_2317725] using wordTrace_append hprefix tailTrace_2317725
  have hstable : (prefixWord ++ tailWord_2317725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317725).length < 2 ^ (prefixWord ++ tailWord_2317725).sum := by decide
  have hdescent : baseEnd_2317725 < baseStart_2317725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317781 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2317781 : Nat := 118140960795 + 2317781 * 2 ^ 59
def prefixEnd_2317781 : Nat := 4983230072969 + 3 ^ 40 * 2317781 * 2
def baseEnd_2317781 : Nat := 1190135704858701404878225

theorem tailTrace_2317781 : CollatzResearch.WordTrace tailWord_2317781 prefixEnd_2317781 1190135704858701404878225 := by
  unfold tailWord_2317781
  simp only [CollatzResearch.WordTrace]
  refine ⟨84536418016082757325041197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56357612010721838216694131 84536418016082757325041197)
  ·
    refine ⟨31701156756031033996890449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84536418016082757325041197 31701156756031033996890449)
    ·
      refine ⟨23775867567023275497667837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31701156756031033996890449 23775867567023275497667837)
      ·
        refine ⟨8915950337633728311625439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23775867567023275497667837 8915950337633728311625439)
        ·
          refine ⟨13373925506450592467438159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8915950337633728311625439 13373925506450592467438159)
          ·
            refine ⟨20060888259675888701157239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13373925506450592467438159 20060888259675888701157239)
            ·
              refine ⟨30091332389513833051735859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20060888259675888701157239 30091332389513833051735859)
              ·
                refine ⟨45136998584270749577603789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30091332389513833051735859 45136998584270749577603789)
                ·
                  refine ⟨16926374469101531091601421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45136998584270749577603789 16926374469101531091601421)
                  ·
                    refine ⟨6347390425913074159350533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16926374469101531091601421 6347390425913074159350533)
                    ·
                      refine ⟨1190135704858701404878225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6347390425913074159350533 1190135704858701404878225)
                      ·
                        rfl

theorem cell23_2317781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2317781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317781 prefixEnd_2317781 := by exact prefixLift 2317781
  have htrace : WordTrace (prefixWord ++ tailWord_2317781) baseStart_2317781 baseEnd_2317781 := by
    simpa [prefixWord, tailWord_2317781, baseEnd_2317781] using wordTrace_append hprefix tailTrace_2317781
  have hstable : (prefixWord ++ tailWord_2317781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317781).length < 2 ^ (prefixWord ++ tailWord_2317781).sum := by decide
  have hdescent : baseEnd_2317781 < baseStart_2317781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317818 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_2317818 : Nat := 118140960795 + 2317818 * 2 ^ 59
def prefixEnd_2317818 : Nat := 4983230072969 + 3 ^ 40 * 2317818 * 2
def baseEnd_2317818 : Nat := 1190154703642917760115555

theorem tailTrace_2317818 : CollatzResearch.WordTrace tailWord_2317818 prefixEnd_2317818 1190154703642917760115555 := by
  unfold tailWord_2317818
  simp only [CollatzResearch.WordTrace]
  refine ⟨21134441879237178161034527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56358511677965808429425405 21134441879237178161034527)
  ·
    refine ⟨31701662818855767241551791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21134441879237178161034527 31701662818855767241551791)
    ·
      refine ⟨47552494228283650862327687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31701662818855767241551791 47552494228283650862327687)
      ·
        refine ⟨71328741342425476293491531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47552494228283650862327687 71328741342425476293491531)
        ·
          refine ⟨106993112013638214440237297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71328741342425476293491531 106993112013638214440237297)
          ·
            refine ⟨80244834010228660830177973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106993112013638214440237297 80244834010228660830177973)
            ·
              refine ⟨7522953188458936952829185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80244834010228660830177973 7522953188458936952829185)
              ·
                refine ⟨5642214891344202714621889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7522953188458936952829185 5642214891344202714621889)
                ·
                  refine ⟨4231661168508152035966417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5642214891344202714621889 4231661168508152035966417)
                  ·
                    refine ⟨3173745876381114026974813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4231661168508152035966417 3173745876381114026974813)
                    ·
                      refine ⟨1190154703642917760115555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173745876381114026974813 1190154703642917760115555)
                      ·
                        rfl

theorem cell23_2317818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_2317818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317818 prefixEnd_2317818 := by exact prefixLift 2317818
  have htrace : WordTrace (prefixWord ++ tailWord_2317818) baseStart_2317818 baseEnd_2317818 := by
    simpa [prefixWord, tailWord_2317818, baseEnd_2317818] using wordTrace_append hprefix tailTrace_2317818
  have hstable : (prefixWord ++ tailWord_2317818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317818).length < 2 ^ (prefixWord ++ tailWord_2317818).sum := by decide
  have hdescent : baseEnd_2317818 < baseStart_2317818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317821 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 8]
def baseStart_2317821 : Nat := 118140960795 + 2317821 * 2 ^ 59
def prefixEnd_2317821 : Nat := 4983230072969 + 3 ^ 40 * 2317821 * 2
def baseEnd_2317821 : Nat := 132239582676097916486449

theorem tailTrace_2317821 : CollatzResearch.WordTrace tailWord_2317821 prefixEnd_2317821 132239582676097916486449 := by
  unfold tailWord_2317821
  simp only [CollatzResearch.WordTrace]
  refine ⟨84537876935937844156497317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56358584623958562770998211 84537876935937844156497317)
  ·
    refine ⟨15850851925488345779343247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84537876935937844156497317 15850851925488345779343247)
    ·
      refine ⟨23776277888232518669014871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15850851925488345779343247 23776277888232518669014871)
      ·
        refine ⟨35664416832348778003522307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23776277888232518669014871 35664416832348778003522307)
        ·
          refine ⟨53496625248523167005283461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35664416832348778003522307 53496625248523167005283461)
          ·
            refine ⟨10030617234098093813490649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53496625248523167005283461 10030617234098093813490649)
            ·
              refine ⟨7522962925573570360117987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10030617234098093813490649 7522962925573570360117987)
              ·
                refine ⟨11284444388360355540176981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522962925573570360117987 11284444388360355540176981)
                ·
                  refine ⟨132239582676097916486449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11284444388360355540176981 132239582676097916486449)
                  ·
                    rfl

theorem cell23_2317821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_2317821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317821 prefixEnd_2317821 := by exact prefixLift 2317821
  have htrace : WordTrace (prefixWord ++ tailWord_2317821) baseStart_2317821 baseEnd_2317821 := by
    simpa [prefixWord, tailWord_2317821, baseEnd_2317821] using wordTrace_append hprefix tailTrace_2317821
  have hstable : (prefixWord ++ tailWord_2317821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317821).length < 2 ^ (prefixWord ++ tailWord_2317821).sum := by decide
  have hdescent : baseEnd_2317821 < baseStart_2317821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317875 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 2, 3, 2]
def baseStart_2317875 : Nat := 118140960795 + 2317875 * 2 ^ 59
def prefixEnd_2317875 : Nat := 4983230072969 + 3 ^ 40 * 2317875 * 2
def baseEnd_2317875 : Nat := 1190183972040224037102793

theorem tailTrace_2317875 : CollatzResearch.WordTrace tailWord_2317875 prefixEnd_2317875 1190183972040224037102793 := by
  unfold tailWord_2317875
  simp only [CollatzResearch.WordTrace]
  refine ⟨84539846477742211378963079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56359897651828140919308719 84539846477742211378963079)
  ·
    refine ⟨126809769716613317068444619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84539846477742211378963079 126809769716613317068444619)
    ·
      refine ⟨190214654574919975602666929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126809769716613317068444619 190214654574919975602666929)
      ·
        refine ⟨142660990931189981702000197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190214654574919975602666929 142660990931189981702000197)
        ·
          refine ⟨26748935799598121569125037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142660990931189981702000197 26748935799598121569125037)
          ·
            refine ⟨10030850924849295588421889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26748935799598121569125037 10030850924849295588421889)
            ·
              refine ⟨7523138193636971691316417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10030850924849295588421889 7523138193636971691316417)
              ·
                refine ⟨5642353645227728768487313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7523138193636971691316417 5642353645227728768487313)
                ·
                  refine ⟨4231765233920796576365485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5642353645227728768487313 4231765233920796576365485)
                  ·
                    refine ⟨1586911962720298716137057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4231765233920796576365485 1586911962720298716137057)
                    ·
                      refine ⟨1190183972040224037102793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1586911962720298716137057 1190183972040224037102793)
                      ·
                        rfl

theorem cell23_2317875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 3, 2].length) (baseStart_2317875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317875 prefixEnd_2317875 := by exact prefixLift 2317875
  have htrace : WordTrace (prefixWord ++ tailWord_2317875) baseStart_2317875 baseEnd_2317875 := by
    simpa [prefixWord, tailWord_2317875, baseEnd_2317875] using wordTrace_append hprefix tailTrace_2317875
  have hstable : (prefixWord ++ tailWord_2317875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317875).length < 2 ^ (prefixWord ++ tailWord_2317875).sum := by decide
  have hdescent : baseEnd_2317875 < baseStart_2317875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317882 : List Nat := [3, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3]
def baseStart_2317882 : Nat := 118140960795 + 2317882 * 2 ^ 59
def prefixEnd_2317882 : Nat := 4983230072969 + 3 ^ 40 * 2317882 * 2
def baseEnd_2317882 : Nat := 1190187566404805509715261

theorem tailTrace_2317882 : CollatzResearch.WordTrace tailWord_2317882 prefixEnd_2317882 1190187566404805509715261 := by
  unfold tailWord_2317882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21135025447179212893616975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56360067859144567716311933 21135025447179212893616975)
  ·
    refine ⟨31702538170768819340425463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21135025447179212893616975 31702538170768819340425463)
    ·
      refine ⟨47553807256153229010638195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31702538170768819340425463 47553807256153229010638195)
      ·
        refine ⟨71330710884229843515957293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47553807256153229010638195 71330710884229843515957293)
        ·
          refine ⟨26749016581586191318483985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71330710884229843515957293 26749016581586191318483985)
          ·
            refine ⟨20061762436189643488862989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26749016581586191318483985 20061762436189643488862989)
            ·
              refine ⟨7523160913571116308323621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20061762436189643488862989 7523160913571116308323621)
              ·
                refine ⟨1410592671294584307810679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7523160913571116308323621 1410592671294584307810679)
                ·
                  refine ⟨2115889006941876461716019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410592671294584307810679 2115889006941876461716019)
                  ·
                    refine ⟨3173833510412814692574029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2115889006941876461716019 3173833510412814692574029)
                    ·
                      refine ⟨1190187566404805509715261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3173833510412814692574029 1190187566404805509715261)
                      ·
                        rfl

theorem cell23_2317882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_2317882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317882 prefixEnd_2317882 := by exact prefixLift 2317882
  have htrace : WordTrace (prefixWord ++ tailWord_2317882) baseStart_2317882 baseEnd_2317882 := by
    simpa [prefixWord, tailWord_2317882, baseEnd_2317882] using wordTrace_append hprefix tailTrace_2317882
  have hstable : (prefixWord ++ tailWord_2317882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317882).length < 2 ^ (prefixWord ++ tailWord_2317882).sum := by decide
  have hdescent : baseEnd_2317882 < baseStart_2317882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317888 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 2, 6, 2]
def baseStart_2317888 : Nat := 118140960795 + 2317888 * 2 ^ 59
def prefixEnd_2317888 : Nat := 4983230072969 + 3 ^ 40 * 2317888 * 2
def baseEnd_2317888 : Nat := 1190190647288732486240233

theorem tailTrace_2317888 : CollatzResearch.WordTrace tailWord_2317888 prefixEnd_2317888 1190190647288732486240233 := by
  unfold tailWord_2317888
  simp only [CollatzResearch.WordTrace]
  refine ⟨42270160313347557299593159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56360213751130076399457545 42270160313347557299593159)
  ·
    refine ⟨63405240470021335949389739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42270160313347557299593159 63405240470021335949389739)
    ·
      refine ⟨95107860705032003924084609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63405240470021335949389739 95107860705032003924084609)
      ·
        refine ⟨71330895528774002943063457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95107860705032003924084609 71330895528774002943063457)
        ·
          refine ⟨53498171646580502207297593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71330895528774002943063457 53498171646580502207297593)
          ·
            refine ⟨40123628734935376655473195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53498171646580502207297593 40123628734935376655473195)
            ·
              refine ⟨60185443102403064983209793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40123628734935376655473195 60185443102403064983209793)
              ·
                refine ⟨45139082326802298737407345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60185443102403064983209793 45139082326802298737407345)
                ·
                  refine ⟨33854311745101724053055509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45139082326802298737407345 33854311745101724053055509)
                  ·
                    refine ⟨1586920863051643314986977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33854311745101724053055509 1586920863051643314986977)
                    ·
                      refine ⟨1190190647288732486240233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1586920863051643314986977 1190190647288732486240233)
                      ·
                        rfl

theorem cell23_2317888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_2317888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317888 prefixEnd_2317888 := by exact prefixLift 2317888
  have htrace : WordTrace (prefixWord ++ tailWord_2317888) baseStart_2317888 baseEnd_2317888 := by
    simpa [prefixWord, tailWord_2317888, baseEnd_2317888] using wordTrace_append hprefix tailTrace_2317888
  have hstable : (prefixWord ++ tailWord_2317888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317888).length < 2 ^ (prefixWord ++ tailWord_2317888).sum := by decide
  have hdescent : baseEnd_2317888 < baseStart_2317888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317898 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_2317898 : Nat := 118140960795 + 2317898 * 2 ^ 59
def prefixEnd_2317898 : Nat := 4983230072969 + 3 ^ 40 * 2317898 * 2
def baseEnd_2317898 : Nat := 396731927365092482371729

theorem tailTrace_2317898 : CollatzResearch.WordTrace tailWord_2317898 prefixEnd_2317898 396731927365092482371729 := by
  unfold tailWord_2317898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21135171339164721576762587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56360456904439257538033565 21135171339164721576762587)
  ·
    refine ⟨31702757008747082365143881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21135171339164721576762587 31702757008747082365143881)
    ·
      refine ⟨23777067756560311773857911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31702757008747082365143881 23777067756560311773857911)
      ·
        refine ⟨35665601634840467660786867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23777067756560311773857911 35665601634840467660786867)
        ·
          refine ⟨53498402452260701491180301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35665601634840467660786867 53498402452260701491180301)
          ·
            refine ⟨20061900919597763059192613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53498402452260701491180301 20061900919597763059192613)
            ·
              refine ⟨3761606422424580573598615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20061900919597763059192613 3761606422424580573598615)
              ·
                refine ⟨5642409633636870860397923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3761606422424580573598615 5642409633636870860397923)
                ·
                  refine ⟨8463614450455306290596885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5642409633636870860397923 8463614450455306290596885)
                  ·
                    refine ⟨396731927365092482371729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8463614450455306290596885 396731927365092482371729)
                    ·
                      rfl

theorem cell23_2317898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_2317898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317898 prefixEnd_2317898 := by exact prefixLift 2317898
  have htrace : WordTrace (prefixWord ++ tailWord_2317898) baseStart_2317898 baseEnd_2317898 := by
    simpa [prefixWord, tailWord_2317898, baseEnd_2317898] using wordTrace_append hprefix tailTrace_2317898
  have hstable : (prefixWord ++ tailWord_2317898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317898).length < 2 ^ (prefixWord ++ tailWord_2317898).sum := by decide
  have hdescent : baseEnd_2317898 < baseStart_2317898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317928 : List Nat := [2, 1, 4, 3, 1, 2, 10]
def baseStart_2317928 : Nat := 118140960795 + 2317928 * 2 ^ 59
def prefixEnd_2317928 : Nat := 4983230072969 + 3 ^ 40 * 2317928 * 2
def baseEnd_2317928 : Nat := 14693965265616201601729

theorem tailTrace_2317928 : CollatzResearch.WordTrace tailWord_2317928 prefixEnd_2317928 14693965265616201601729 := by
  unfold tailWord_2317928
  simp only [CollatzResearch.WordTrace]
  refine ⟨42270889773275100715321219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56361186364366800953761625 42270889773275100715321219)
  ·
    refine ⟨63406334659912651072981829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42270889773275100715321219 63406334659912651072981829)
    ·
      refine ⟨11888687748733622076184093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63406334659912651072981829 11888687748733622076184093)
      ·
        refine ⟨4458257905775108278569035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11888687748733622076184093 4458257905775108278569035)
        ·
          refine ⟨6687386858662662417853553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458257905775108278569035 6687386858662662417853553)
          ·
            refine ⟨5015540143996996813390165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6687386858662662417853553 5015540143996996813390165)
            ·
              refine ⟨14693965265616201601729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5015540143996996813390165 14693965265616201601729)
              ·
                rfl

theorem cell23_2317928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 10].length) (baseStart_2317928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2317928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2317928 prefixEnd_2317928 := by exact prefixLift 2317928
  have htrace : WordTrace (prefixWord ++ tailWord_2317928) baseStart_2317928 baseEnd_2317928 := by
    simpa [prefixWord, tailWord_2317928, baseEnd_2317928] using wordTrace_append hprefix tailTrace_2317928
  have hstable : (prefixWord ++ tailWord_2317928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317928).length < 2 ^ (prefixWord ++ tailWord_2317928).sum := by decide
  have hdescent : baseEnd_2317928 < baseStart_2317928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318006 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2318006 : Nat := 118140960795 + 2318006 * 2 ^ 59
def prefixEnd_2318006 : Nat := 4983230072969 + 3 ^ 40 * 2318006 * 2
def baseEnd_2318006 : Nat := 1190251238005963024564691

theorem tailTrace_2318006 : CollatzResearch.WordTrace tailWord_2318006 prefixEnd_2318006 1190251238005963024564691 := by
  unfold tailWord_2318006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284039027516726296998867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56363082960178413834654581 5284039027516726296998867)
  ·
    refine ⟨7926058541275089445498301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5284039027516726296998867 7926058541275089445498301)
    ·
      refine ⟨2972271952978158542061863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7926058541275089445498301 2972271952978158542061863)
      ·
        refine ⟨4458407929467237813092795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972271952978158542061863 4458407929467237813092795)
        ·
          refine ⟨6687611894200856719639193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458407929467237813092795 6687611894200856719639193)
          ·
            refine ⟨5015708920650642539729395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6687611894200856719639193 5015708920650642539729395)
            ·
              refine ⟨7523563380975963809594093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015708920650642539729395 7523563380975963809594093)
              ·
                refine ⟨2821336267865986428597785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7523563380975963809594093 2821336267865986428597785)
                ·
                  refine ⟨2116002200899489821448339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2821336267865986428597785 2116002200899489821448339)
                  ·
                    refine ⟨3174003301349234732172509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2116002200899489821448339 3174003301349234732172509)
                    ·
                      refine ⟨1190251238005963024564691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3174003301349234732172509 1190251238005963024564691)
                      ·
                        rfl

theorem cell23_2318006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2318006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318006 prefixEnd_2318006 := by exact prefixLift 2318006
  have htrace : WordTrace (prefixWord ++ tailWord_2318006) baseStart_2318006 baseEnd_2318006 := by
    simpa [prefixWord, tailWord_2318006, baseEnd_2318006] using wordTrace_append hprefix tailTrace_2318006
  have hstable : (prefixWord ++ tailWord_2318006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318006).length < 2 ^ (prefixWord ++ tailWord_2318006).sum := by decide
  have hdescent : baseEnd_2318006 < baseStart_2318006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318008 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_2318008 : Nat := 118140960795 + 2318008 * 2 ^ 59
def prefixEnd_2318008 : Nat := 4983230072969 + 3 ^ 40 * 2318008 * 2
def baseEnd_2318008 : Nat := 1190252264967272016739681

theorem tailTrace_2318008 : CollatzResearch.WordTrace tailWord_2318008 prefixEnd_2318008 1190252264967272016739681 := by
  unfold tailWord_2318008
  simp only [CollatzResearch.WordTrace]
  refine ⟨42272348693130187546777339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56363131590840250062369785 42272348693130187546777339)
  ·
    refine ⟨63408523039695281320166009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42272348693130187546777339 63408523039695281320166009)
    ·
      refine ⟨47556392279771460990124507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63408523039695281320166009 47556392279771460990124507)
      ·
        refine ⟨71334588419657191485186761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47556392279771460990124507 71334588419657191485186761)
        ·
          refine ⟨53500941314742893613890071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71334588419657191485186761 53500941314742893613890071)
          ·
            refine ⟨80251411972114340420835107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53500941314742893613890071 80251411972114340420835107)
            ·
              refine ⟨120377117958171510631252661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80251411972114340420835107 120377117958171510631252661)
              ·
                refine ⟨11285354808578579121679937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120377117958171510631252661 11285354808578579121679937)
                ·
                  refine ⟨8464016106433934341259953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11285354808578579121679937 8464016106433934341259953)
                  ·
                    refine ⟨6348012079825450755944965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8464016106433934341259953 6348012079825450755944965)
                    ·
                      refine ⟨1190252264967272016739681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6348012079825450755944965 1190252264967272016739681)
                      ·
                        rfl

theorem cell23_2318008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_2318008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318008 prefixEnd_2318008 := by exact prefixLift 2318008
  have htrace : WordTrace (prefixWord ++ tailWord_2318008) baseStart_2318008 baseEnd_2318008 := by
    simpa [prefixWord, tailWord_2318008, baseEnd_2318008] using wordTrace_append hprefix tailTrace_2318008
  have hstable : (prefixWord ++ tailWord_2318008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318008).length < 2 ^ (prefixWord ++ tailWord_2318008).sum := by decide
  have hdescent : baseEnd_2318008 < baseStart_2318008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318029 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_2318029 : Nat := 118140960795 + 2318029 * 2 ^ 59
def prefixEnd_2318029 : Nat := 4983230072969 + 3 ^ 40 * 2318029 * 2
def baseEnd_2318029 : Nat := 1190263048061016434577085

theorem tailTrace_2318029 : CollatzResearch.WordTrace tailWord_2318029 prefixEnd_2318029 1190263048061016434577085 := by
  unfold tailWord_2318029
  simp only [CollatzResearch.WordTrace]
  refine ⟨84545463319184295680069141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56363642212789530453379427 84545463319184295680069141)
  ·
    refine ⟨3963068593086763860003241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84545463319184295680069141 3963068593086763860003241)
    ·
      refine ⟨2972301444815072895002431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3963068593086763860003241 2972301444815072895002431)
      ·
        refine ⟨4458452167222609342503647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972301444815072895002431 4458452167222609342503647)
        ·
          refine ⟨6687678250833914013755471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458452167222609342503647 6687678250833914013755471)
          ·
            refine ⟨10031517376250871020633207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6687678250833914013755471 10031517376250871020633207)
            ·
              refine ⟨15047276064376306530949811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10031517376250871020633207 15047276064376306530949811)
              ·
                refine ⟨22570914096564459796424717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15047276064376306530949811 22570914096564459796424717)
                ·
                  refine ⟨8464092786211672423659269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22570914096564459796424717 8464092786211672423659269)
                  ·
                    refine ⟨1587017397414688579436113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8464092786211672423659269 1587017397414688579436113)
                    ·
                      refine ⟨1190263048061016434577085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1587017397414688579436113 1190263048061016434577085)
                      ·
                        rfl

theorem cell23_2318029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_2318029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318029 prefixEnd_2318029 := by exact prefixLift 2318029
  have htrace : WordTrace (prefixWord ++ tailWord_2318029) baseStart_2318029 baseEnd_2318029 := by
    simpa [prefixWord, tailWord_2318029, baseEnd_2318029] using wordTrace_append hprefix tailTrace_2318029
  have hstable : (prefixWord ++ tailWord_2318029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318029).length < 2 ^ (prefixWord ++ tailWord_2318029).sum := by decide
  have hdescent : baseEnd_2318029 < baseStart_2318029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318112 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 3, 4]
def baseStart_2318112 : Nat := 118140960795 + 2318112 * 2 ^ 59
def prefixEnd_2318112 : Nat := 4983230072969 + 3 ^ 40 * 2318112 * 2
def baseEnd_2318112 : Nat := 396768555651779869946401

theorem tailTrace_2318112 : CollatzResearch.WordTrace tailWord_2318112 prefixEnd_2318112 396768555651779869946401 := by
  unfold tailWord_2318112
  simp only [CollatzResearch.WordTrace]
  refine ⟨42274245288941800427670295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56365660385255733903560393 42274245288941800427670295)
  ·
    refine ⟨63411367933412700641505443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42274245288941800427670295 63411367933412700641505443)
    ·
      refine ⟨95117051900119050962258165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63411367933412700641505443 95117051900119050962258165)
      ·
        refine ⟨8917223615636161027711703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95117051900119050962258165 8917223615636161027711703)
        ·
          refine ⟨13375835423454241541567555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8917223615636161027711703 13375835423454241541567555)
          ·
            refine ⟨20063753135181362312351333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13375835423454241541567555 20063753135181362312351333)
            ·
              refine ⟨3761953712846505433565875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20063753135181362312351333 3761953712846505433565875)
              ·
                refine ⟨5642930569269758150348813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3761953712846505433565875 5642930569269758150348813)
                ·
                  refine ⟨2116098963476159306380805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5642930569269758150348813 2116098963476159306380805)
                  ·
                    refine ⟨396768555651779869946401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2116098963476159306380805 396768555651779869946401)
                    ·
                      rfl

theorem cell23_2318112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 4].length) (baseStart_2318112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318112 prefixEnd_2318112 := by exact prefixLift 2318112
  have htrace : WordTrace (prefixWord ++ tailWord_2318112) baseStart_2318112 baseEnd_2318112 := by
    simpa [prefixWord, tailWord_2318112, baseEnd_2318112] using wordTrace_append hprefix tailTrace_2318112
  have hstable : (prefixWord ++ tailWord_2318112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318112).length < 2 ^ (prefixWord ++ tailWord_2318112).sum := by decide
  have hdescent : baseEnd_2318112 < baseStart_2318112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318212 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_2318212 : Nat := 118140960795 + 2318212 * 2 ^ 59
def prefixEnd_2318212 : Nat := 4983230072969 + 3 ^ 40 * 2318212 * 2
def baseEnd_2318212 : Nat := 1190357015020789218588743

theorem tailTrace_2318212 : CollatzResearch.WordTrace tailWord_2318212 prefixEnd_2318212 1190357015020789218588743 := by
  unfold tailWord_2318212
  simp only [CollatzResearch.WordTrace]
  refine ⟨42276068938760658966990445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56368091918347545289320593 42276068938760658966990445)
  ·
    refine ⟨15853525852035247112621417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42276068938760658966990445 15853525852035247112621417)
    ·
      refine ⟨11890144389026435334466063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15853525852035247112621417 11890144389026435334466063)
      ·
        refine ⟨17835216583539653001699095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11890144389026435334466063 17835216583539653001699095)
        ·
          refine ⟨26752824875309479502548643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17835216583539653001699095 26752824875309479502548643)
          ·
            refine ⟨40129237312964219253822965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26752824875309479502548643 40129237312964219253822965)
            ·
              refine ⟨3762115998090395555045903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40129237312964219253822965 3762115998090395555045903)
              ·
                refine ⟨5643173997135593332568855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3762115998090395555045903 5643173997135593332568855)
                ·
                  refine ⟨8464760995703389998853283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5643173997135593332568855 8464760995703389998853283)
                  ·
                    refine ⟨12697141493555084998279925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8464760995703389998853283 12697141493555084998279925)
                    ·
                      refine ⟨1190357015020789218588743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12697141493555084998279925 1190357015020789218588743)
                      ·
                        rfl

theorem cell23_2318212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_2318212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318212 prefixEnd_2318212 := by exact prefixLift 2318212
  have htrace : WordTrace (prefixWord ++ tailWord_2318212) baseStart_2318212 baseEnd_2318212 := by
    simpa [prefixWord, tailWord_2318212, baseEnd_2318212] using wordTrace_append hprefix tailTrace_2318212
  have hstable : (prefixWord ++ tailWord_2318212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318212).length < 2 ^ (prefixWord ++ tailWord_2318212).sum := by decide
  have hdescent : baseEnd_2318212 < baseStart_2318212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318215 : List Nat := [1, 1, 4, 2, 4, 11]
def baseStart_2318215 : Nat := 118140960795 + 2318215 * 2 ^ 59
def prefixEnd_2318215 : Nat := 4983230072969 + 3 ^ 40 * 2318215 * 2
def baseEnd_2318215 : Nat := 4898594878447542003503

theorem tailTrace_2318215 : CollatzResearch.WordTrace tailWord_2318215 prefixEnd_2318215 4898594878447542003503 := by
  unfold tailWord_2318215
  simp only [CollatzResearch.WordTrace]
  refine ⟨84552247296510449446340099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56368164864340299630893399 84552247296510449446340099)
  ·
    refine ⟨126828370944765674169510149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84552247296510449446340099 126828370944765674169510149)
    ·
      refine ⟨23780319552143563906783153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126828370944765674169510149 23780319552143563906783153)
      ·
        refine ⟨17835239664107672930087365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23780319552143563906783153 17835239664107672930087365)
        ·
          refine ⟨3344107437020188674391381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17835239664107672930087365 3344107437020188674391381)
          ·
            refine ⟨4898594878447542003503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3344107437020188674391381 4898594878447542003503)
            ·
              rfl

theorem cell23_2318215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 11].length) (baseStart_2318215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318215 prefixEnd_2318215 := by exact prefixLift 2318215
  have htrace : WordTrace (prefixWord ++ tailWord_2318215) baseStart_2318215 baseEnd_2318215 := by
    simpa [prefixWord, tailWord_2318215, baseEnd_2318215] using wordTrace_append hprefix tailTrace_2318215
  have hstable : (prefixWord ++ tailWord_2318215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318215).length < 2 ^ (prefixWord ++ tailWord_2318215).sum := by decide
  have hdescent : baseEnd_2318215 < baseStart_2318215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318239 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2318239 : Nat := 118140960795 + 2318239 * 2 ^ 59
def prefixEnd_2318239 : Nat := 4983230072969 + 3 ^ 40 * 2318239 * 2
def baseEnd_2318239 : Nat := 1190370878998460612951119

theorem tailTrace_2318239 : CollatzResearch.WordTrace tailWord_2318239 prefixEnd_2318239 1190370878998460612951119 := by
  unfold tailWord_2318239
  simp only [CollatzResearch.WordTrace]
  refine ⟨84553122648423501545213771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56368748432282334363475847 84553122648423501545213771)
  ·
    refine ⟨126829683972635252317820657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84553122648423501545213771 126829683972635252317820657)
    ·
      refine ⟨95122262979476439238365493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126829683972635252317820657 95122262979476439238365493)
      ·
        refine ⟨8917712154325916178596765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95122262979476439238365493 8917712154325916178596765)
        ·
          refine ⟨3344142057872218566973787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8917712154325916178596765 3344142057872218566973787)
          ·
            refine ⟨5016213086808327850460681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344142057872218566973787 5016213086808327850460681)
            ·
              refine ⟨3762159815106245887845511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5016213086808327850460681 3762159815106245887845511)
              ·
                refine ⟨5643239722659368831768267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3762159815106245887845511 5643239722659368831768267)
                ·
                  refine ⟨8464859583989053247652401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5643239722659368831768267 8464859583989053247652401)
                  ·
                    refine ⟨6348644687991789935739301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8464859583989053247652401 6348644687991789935739301)
                    ·
                      refine ⟨1190370878998460612951119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6348644687991789935739301 1190370878998460612951119)
                      ·
                        rfl

theorem cell23_2318239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2318239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318239 prefixEnd_2318239 := by exact prefixLift 2318239
  have htrace : WordTrace (prefixWord ++ tailWord_2318239) baseStart_2318239 baseEnd_2318239 := by
    simpa [prefixWord, tailWord_2318239, baseEnd_2318239] using wordTrace_append hprefix tailTrace_2318239
  have hstable : (prefixWord ++ tailWord_2318239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318239).length < 2 ^ (prefixWord ++ tailWord_2318239).sum := by decide
  have hdescent : baseEnd_2318239 < baseStart_2318239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318255 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_2318255 : Nat := 118140960795 + 2318255 * 2 ^ 59
def prefixEnd_2318255 : Nat := 4983230072969 + 3 ^ 40 * 2318255 * 2
def baseEnd_2318255 : Nat := 1190379094688932550351045

theorem tailTrace_2318255 : CollatzResearch.WordTrace tailWord_2318255 prefixEnd_2318255 1190379094688932550351045 := by
  unfold tailWord_2318255
  simp only [CollatzResearch.WordTrace]
  refine ⟨84553706216365536277796219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56369137477577024185197479 84553706216365536277796219)
  ·
    refine ⟨126830559324548304416694329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84553706216365536277796219 126830559324548304416694329)
    ·
      refine ⟨95122919493411228312520747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126830559324548304416694329 95122919493411228312520747)
      ·
        refine ⟨142684379240116842468781121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95122919493411228312520747 142684379240116842468781121)
        ·
          refine ⟨107013284430087631851585841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142684379240116842468781121 107013284430087631851585841)
          ·
            refine ⟨80259963322565723888689381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107013284430087631851585841 80259963322565723888689381)
            ·
              refine ⟨15048743122981073229129259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80259963322565723888689381 15048743122981073229129259)
              ·
                refine ⟨22573114684471609843693889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15048743122981073229129259 22573114684471609843693889)
                ·
                  refine ⟨16929836013353707382770417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22573114684471609843693889 16929836013353707382770417)
                  ·
                    refine ⟨12697377010015280537077813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16929836013353707382770417 12697377010015280537077813)
                    ·
                      refine ⟨1190379094688932550351045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12697377010015280537077813 1190379094688932550351045)
                      ·
                        rfl

theorem cell23_2318255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_2318255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318255 prefixEnd_2318255 := by exact prefixLift 2318255
  have htrace : WordTrace (prefixWord ++ tailWord_2318255) baseStart_2318255 baseEnd_2318255 := by
    simpa [prefixWord, tailWord_2318255, baseEnd_2318255] using wordTrace_append hprefix tailTrace_2318255
  have hstable : (prefixWord ++ tailWord_2318255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318255).length < 2 ^ (prefixWord ++ tailWord_2318255).sum := by decide
  have hdescent : baseEnd_2318255 < baseStart_2318255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318260 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_2318260 : Nat := 118140960795 + 2318260 * 2 ^ 59
def prefixEnd_2318260 : Nat := 4983230072969 + 3 ^ 40 * 2318260 * 2
def baseEnd_2318260 : Nat := 1190381662092205030788523

theorem tailTrace_2318260 : CollatzResearch.WordTrace tailWord_2318260 prefixEnd_2318260 1190381662092205030788523 := by
  unfold tailWord_2318260
  simp only [CollatzResearch.WordTrace]
  refine ⟨42276944290673711065864117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56369259054231614754485489 42276944290673711065864117)
  ·
    refine ⟨3963463527250660412424761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42276944290673711065864117 3963463527250660412424761)
    ·
      refine ⟨2972597645437995309318571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3963463527250660412424761 2972597645437995309318571)
      ·
        refine ⟨4458896468156992963977857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972597645437995309318571 4458896468156992963977857)
        ·
          refine ⟨3344172351117744722983393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4458896468156992963977857 3344172351117744722983393)
          ·
            refine ⟨2508129263338308542237545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3344172351117744722983393 2508129263338308542237545)
            ·
              refine ⟨1881096947503731406678159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2508129263338308542237545 1881096947503731406678159)
              ·
                refine ⟨2821645421255597110017239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881096947503731406678159 2821645421255597110017239)
                ·
                  refine ⟨4232468131883395665025859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2821645421255597110017239 4232468131883395665025859)
                  ·
                    refine ⟨6348702197825093497538789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4232468131883395665025859 6348702197825093497538789)
                    ·
                      refine ⟨1190381662092205030788523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6348702197825093497538789 1190381662092205030788523)
                      ·
                        rfl

theorem cell23_2318260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_2318260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318260 prefixEnd_2318260 := by exact prefixLift 2318260
  have htrace : WordTrace (prefixWord ++ tailWord_2318260) baseStart_2318260 baseEnd_2318260 := by
    simpa [prefixWord, tailWord_2318260, baseEnd_2318260] using wordTrace_append hprefix tailTrace_2318260
  have hstable : (prefixWord ++ tailWord_2318260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318260).length < 2 ^ (prefixWord ++ tailWord_2318260).sum := by decide
  have hdescent : baseEnd_2318260 < baseStart_2318260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318292 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_2318292 : Nat := 118140960795 + 2318292 * 2 ^ 59
def prefixEnd_2318292 : Nat := 4983230072969 + 3 ^ 40 * 2318292 * 2
def baseEnd_2318292 : Nat := 396799364491049635196125

theorem tailTrace_2318292 : CollatzResearch.WordTrace tailWord_2318292 prefixEnd_2318292 396799364491049635196125 := by
  unfold tailWord_2318292
  simp only [CollatzResearch.WordTrace]
  refine ⟨42277527858615745798446565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56370037144820994397928753 42277527858615745798446565)
  ·
    refine ⟨7927036473490452337208731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42277527858615745798446565 7927036473490452337208731)
    ·
      refine ⟨11890554710235678505813097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7927036473490452337208731 11890554710235678505813097)
      ·
        refine ⟨8917916032676758879359823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11890554710235678505813097 8917916032676758879359823)
        ·
          refine ⟨13376874049015138319039735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8917916032676758879359823 13376874049015138319039735)
          ·
            refine ⟨20065311073522707478559603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13376874049015138319039735 20065311073522707478559603)
            ·
              refine ⟨30097966610284061217839405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20065311073522707478559603 30097966610284061217839405)
              ·
                refine ⟨11286737478856522956689777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30097966610284061217839405 11286737478856522956689777)
                ·
                  refine ⟨8465053109142392217517333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11286737478856522956689777 8465053109142392217517333)
                  ·
                    refine ⟨396799364491049635196125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8465053109142392217517333 396799364491049635196125)
                    ·
                      rfl

theorem cell23_2318292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_2318292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318292 prefixEnd_2318292 := by exact prefixLift 2318292
  have htrace : WordTrace (prefixWord ++ tailWord_2318292) baseStart_2318292 baseEnd_2318292 := by
    simpa [prefixWord, tailWord_2318292, baseEnd_2318292] using wordTrace_append hprefix tailTrace_2318292
  have hstable : (prefixWord ++ tailWord_2318292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318292).length < 2 ^ (prefixWord ++ tailWord_2318292).sum := by decide
  have hdescent : baseEnd_2318292 < baseStart_2318292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318293 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_2318293 : Nat := 118140960795 + 2318293 * 2 ^ 59
def prefixEnd_2318293 : Nat := 4983230072969 + 3 ^ 40 * 2318293 * 2
def baseEnd_2318293 : Nat := 1190398606953803401675871

theorem tailTrace_2318293 : CollatzResearch.WordTrace tailWord_2318293 prefixEnd_2318293 1190398606953803401675871 := by
  unfold tailWord_2318293
  simp only [CollatzResearch.WordTrace]
  refine ⟨84555092190227868767679533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56370061460151912511786355 84555092190227868767679533)
  ·
    refine ⟨31708159571335450787879825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84555092190227868767679533 31708159571335450787879825)
    ·
      refine ⟨23781119678501588090909869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31708159571335450787879825 23781119678501588090909869)
      ·
        refine ⟨8917919879438095534091201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23781119678501588090909869 8917919879438095534091201)
        ·
          refine ⟨6688439909578571650568401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8917919879438095534091201 6688439909578571650568401)
          ·
            refine ⟨5016329932183928737926301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6688439909578571650568401 5016329932183928737926301)
            ·
              refine ⟨1881123724568973276722363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5016329932183928737926301 1881123724568973276722363)
              ·
                refine ⟨2821685586853459915083545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881123724568973276722363 2821685586853459915083545)
                ·
                  refine ⟨2116264190140094936312659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2821685586853459915083545 2116264190140094936312659)
                  ·
                    refine ⟨3174396285210142404468989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2116264190140094936312659 3174396285210142404468989)
                    ·
                      refine ⟨1190398606953803401675871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3174396285210142404468989 1190398606953803401675871)
                      ·
                        rfl

theorem cell23_2318293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_2318293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318293 prefixEnd_2318293 := by exact prefixLift 2318293
  have htrace : WordTrace (prefixWord ++ tailWord_2318293) baseStart_2318293 baseEnd_2318293 := by
    simpa [prefixWord, tailWord_2318293, baseEnd_2318293] using wordTrace_append hprefix tailTrace_2318293
  have hstable : (prefixWord ++ tailWord_2318293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318293).length < 2 ^ (prefixWord ++ tailWord_2318293).sum := by decide
  have hdescent : baseEnd_2318293 < baseStart_2318293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318300 : List Nat := [2, 2, 6, 1, 2, 1, 2, 7]
def baseStart_2318300 : Nat := 118140960795 + 2318300 * 2 ^ 59
def prefixEnd_2318300 : Nat := 4983230072969 + 3 ^ 40 * 2318300 * 2
def baseEnd_2318300 : Nat := 44088970419199439788457

theorem tailTrace_2318300 : CollatzResearch.WordTrace tailWord_2318300 prefixEnd_2318300 44088970419199439788457 := by
  unfold tailWord_2318300
  simp only [CollatzResearch.WordTrace]
  refine ⟨42277673750601254481592177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56370231667468339308789569 42277673750601254481592177)
  ·
    refine ⟨31708255312950940861194133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42277673750601254481592177 31708255312950940861194133)
    ·
      refine ⟨1486324467794575352868475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31708255312950940861194133 1486324467794575352868475)
      ·
        refine ⟨2229486701691863029302713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486324467794575352868475 2229486701691863029302713)
        ·
          refine ⟨1672115026268897271977035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229486701691863029302713 1672115026268897271977035)
          ·
            refine ⟨2508172539403345907965553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672115026268897271977035 2508172539403345907965553)
            ·
              refine ⟨1881129404552509430974165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2508172539403345907965553 1881129404552509430974165)
              ·
                refine ⟨44088970419199439788457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1881129404552509430974165 44088970419199439788457)
                ·
                  rfl

theorem cell23_2318300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 7].length) (baseStart_2318300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318300 prefixEnd_2318300 := by exact prefixLift 2318300
  have htrace : WordTrace (prefixWord ++ tailWord_2318300) baseStart_2318300 baseEnd_2318300 := by
    simpa [prefixWord, tailWord_2318300, baseEnd_2318300] using wordTrace_append hprefix tailTrace_2318300
  have hstable : (prefixWord ++ tailWord_2318300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318300).length < 2 ^ (prefixWord ++ tailWord_2318300).sum := by decide
  have hdescent : baseEnd_2318300 < baseStart_2318300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318389 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2318389 : Nat := 118140960795 + 2318389 * 2 ^ 59
def prefixEnd_2318389 : Nat := 4983230072969 + 3 ^ 40 * 2318389 * 2
def baseEnd_2318389 : Nat := 1190447901096635026075429

theorem tailTrace_2318389 : CollatzResearch.WordTrace tailWord_2318389 prefixEnd_2318389 1190447901096635026075429 := by
  unfold tailWord_2318389
  simp only [CollatzResearch.WordTrace]
  refine ⟨84558593597880077163174221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56372395731920051442116147 84558593597880077163174221)
  ·
    refine ⟨31709472599205028936190333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84558593597880077163174221 31709472599205028936190333)
    ·
      refine ⟨11891052224701885851071375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31709472599205028936190333 11891052224701885851071375)
      ·
        refine ⟨17836578337052828776607063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11891052224701885851071375 17836578337052828776607063)
        ·
          refine ⟨26754867505579243164910595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17836578337052828776607063 26754867505579243164910595)
          ·
            refine ⟨40132301258368864747365893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26754867505579243164910595 40132301258368864747365893)
            ·
              refine ⟨7524806485944162140131105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40132301258368864747365893 7524806485944162140131105)
              ·
                refine ⟨5643604864458121605098329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7524806485944162140131105 5643604864458121605098329)
                ·
                  refine ⟨4232703648343591203823747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5643604864458121605098329 4232703648343591203823747)
                  ·
                    refine ⟨6349055472515386805735621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4232703648343591203823747 6349055472515386805735621)
                    ·
                      refine ⟨1190447901096635026075429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6349055472515386805735621 1190447901096635026075429)
                      ·
                        rfl

theorem cell23_2318389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2318389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318389 prefixEnd_2318389 := by exact prefixLift 2318389
  have htrace : WordTrace (prefixWord ++ tailWord_2318389) baseStart_2318389 baseEnd_2318389 := by
    simpa [prefixWord, tailWord_2318389, baseEnd_2318389] using wordTrace_append hprefix tailTrace_2318389
  have hstable : (prefixWord ++ tailWord_2318389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318389).length < 2 ^ (prefixWord ++ tailWord_2318389).sum := by decide
  have hdescent : baseEnd_2318389 < baseStart_2318389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318406 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2318406 : Nat := 118140960795 + 2318406 * 2 ^ 59
def prefixEnd_2318406 : Nat := 4983230072969 + 3 ^ 40 * 2318406 * 2
def baseEnd_2318406 : Nat := 1190456630267761459562851

theorem tailTrace_2318406 : CollatzResearch.WordTrace tailWord_2318406 prefixEnd_2318406 1190456630267761459562851 := by
  unfold tailWord_2318406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642475426213077783329471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56372809092545659377695381 2642475426213077783329471)
  ·
    refine ⟨3963713139319616674994207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2642475426213077783329471 3963713139319616674994207)
    ·
      refine ⟨5945569708979425012491311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3963713139319616674994207 5945569708979425012491311)
      ·
        refine ⟨8918354563469137518736967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5945569708979425012491311 8918354563469137518736967)
        ·
          refine ⟨13377531845203706278105451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8918354563469137518736967 13377531845203706278105451)
          ·
            refine ⟨20066297767805559417158177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13377531845203706278105451 20066297767805559417158177)
            ·
              refine ⟨15049723325854169562868633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20066297767805559417158177 15049723325854169562868633)
              ·
                refine ⟨11287292494390627172151475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15049723325854169562868633 11287292494390627172151475)
                ·
                  refine ⟨16930938741585940758227213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11287292494390627172151475 16930938741585940758227213)
                  ·
                    refine ⟨6349102028094727784335205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16930938741585940758227213 6349102028094727784335205)
                    ·
                      refine ⟨1190456630267761459562851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6349102028094727784335205 1190456630267761459562851)
                      ·
                        rfl

theorem cell23_2318406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2318406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318406 prefixEnd_2318406 := by exact prefixLift 2318406
  have htrace : WordTrace (prefixWord ++ tailWord_2318406) baseStart_2318406 baseEnd_2318406 := by
    simpa [prefixWord, tailWord_2318406, baseEnd_2318406] using wordTrace_append hprefix tailTrace_2318406
  have hstable : (prefixWord ++ tailWord_2318406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318406).length < 2 ^ (prefixWord ++ tailWord_2318406).sum := by decide
  have hdescent : baseEnd_2318406 < baseStart_2318406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318484 : List Nat := [2, 4, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2318484 : Nat := 118140960795 + 2318484 * 2 ^ 59
def prefixEnd_2318484 : Nat := 4983230072969 + 3 ^ 40 * 2318484 * 2
def baseEnd_2318484 : Nat := 396832227252937384795831

theorem tailTrace_2318484 : CollatzResearch.WordTrace tailWord_2318484 prefixEnd_2318484 396832227252937384795831 := by
  unfold tailWord_2318484
  simp only [CollatzResearch.WordTrace]
  refine ⟨42281029266267954193941253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56374705688357272258588337 42281029266267954193941253)
  ·
    refine ⟨7927692987425241411363985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42281029266267954193941253 7927692987425241411363985)
    ·
      refine ⟨5945769740568931058522989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7927692987425241411363985 5945769740568931058522989)
      ·
        refine ⟨2229663652713349146946121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5945769740568931058522989 2229663652713349146946121)
        ·
          refine ⟨1672247739535011860209591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229663652713349146946121 1672247739535011860209591)
          ·
            refine ⟨2508371609302517790314387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672247739535011860209591 2508371609302517790314387)
            ·
              refine ⟨3762557413953776685471581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508371609302517790314387 3762557413953776685471581)
              ·
                refine ⟨1410959030232666257051843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3762557413953776685471581 1410959030232666257051843)
                ·
                  refine ⟨2116438545348999385577765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410959030232666257051843 2116438545348999385577765)
                  ·
                    refine ⟨396832227252937384795831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2116438545348999385577765 396832227252937384795831)
                    ·
                      rfl

theorem cell23_2318484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2318484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318484 prefixEnd_2318484 := by exact prefixLift 2318484
  have htrace : WordTrace (prefixWord ++ tailWord_2318484) baseStart_2318484 baseEnd_2318484 := by
    simpa [prefixWord, tailWord_2318484, baseEnd_2318484] using wordTrace_append hprefix tailTrace_2318484
  have hstable : (prefixWord ++ tailWord_2318484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318484).length < 2 ^ (prefixWord ++ tailWord_2318484).sum := by decide
  have hdescent : baseEnd_2318484 < baseStart_2318484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318496 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2318496 : Nat := 118140960795 + 2318496 * 2 ^ 59
def prefixEnd_2318496 : Nat := 4983230072969 + 3 ^ 40 * 2318496 * 2
def baseEnd_2318496 : Nat := 1190502843526666107437437

theorem tailTrace_2318496 : CollatzResearch.WordTrace tailWord_2318496 prefixEnd_2318496 1190502843526666107437437 := by
  unfold tailWord_2318496
  simp only [CollatzResearch.WordTrace]
  refine ⟨42281248104246217218659671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56374997472328289624879561 42281248104246217218659671)
  ·
    refine ⟨63421872156369325827989507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42281248104246217218659671 63421872156369325827989507)
    ·
      refine ⟨95132808234553988741984261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63421872156369325827989507 95132808234553988741984261)
      ·
        refine ⟨17837401543978872889122049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95132808234553988741984261 17837401543978872889122049)
        ·
          refine ⟨13378051157984154666841537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17837401543978872889122049 13378051157984154666841537)
          ·
            refine ⟨10033538368488116000131153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13378051157984154666841537 10033538368488116000131153)
            ·
              refine ⟨7525153776366087000098365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10033538368488116000131153 7525153776366087000098365)
              ·
                refine ⟨2821932666137282625036887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7525153776366087000098365 2821932666137282625036887)
                ·
                  refine ⟨4232898999205923937555331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2821932666137282625036887 4232898999205923937555331)
                  ·
                    refine ⟨6349348498808885906332997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4232898999205923937555331 6349348498808885906332997)
                    ·
                      refine ⟨1190502843526666107437437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6349348498808885906332997 1190502843526666107437437)
                      ·
                        rfl

theorem cell23_2318496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2318496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318496 prefixEnd_2318496 := by exact prefixLift 2318496
  have htrace : WordTrace (prefixWord ++ tailWord_2318496) baseStart_2318496 baseEnd_2318496 := by
    simpa [prefixWord, tailWord_2318496, baseEnd_2318496] using wordTrace_append hprefix tailTrace_2318496
  have hstable : (prefixWord ++ tailWord_2318496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318496).length < 2 ^ (prefixWord ++ tailWord_2318496).sum := by decide
  have hdescent : baseEnd_2318496 < baseStart_2318496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318499 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 3]
def baseStart_2318499 : Nat := 118140960795 + 2318499 * 2 ^ 59
def prefixEnd_2318499 : Nat := 4983230072969 + 3 ^ 40 * 2318499 * 2
def baseEnd_2318499 : Nat := 1190504383968629595699923

theorem tailTrace_2318499 : CollatzResearch.WordTrace tailWord_2318499 prefixEnd_2318499 1190504383968629595699923 := by
  unfold tailWord_2318499
  simp only [CollatzResearch.WordTrace]
  refine ⟨84562605627481565949678551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56375070418321043966452367 84562605627481565949678551)
  ·
    refine ⟨126843908441222348924517827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84562605627481565949678551 126843908441222348924517827)
    ·
      refine ⟨190265862661833523386776741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126843908441222348924517827 190265862661833523386776741)
      ·
        refine ⟨35674849249093785635020639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190265862661833523386776741 35674849249093785635020639)
        ·
          refine ⟨53512273873640678452530959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35674849249093785635020639 53512273873640678452530959)
          ·
            refine ⟨80268410810461017678796439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53512273873640678452530959 80268410810461017678796439)
            ·
              refine ⟨120402616215691526518194659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80268410810461017678796439 120402616215691526518194659)
              ·
                refine ⟨180603924323537289777291989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120402616215691526518194659 180603924323537289777291989)
                ·
                  refine ⟨4232904476332905229155281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 180603924323537289777291989 4232904476332905229155281)
                  ·
                    refine ⟨3174678357249678921866461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4232904476332905229155281 3174678357249678921866461)
                    ·
                      refine ⟨1190504383968629595699923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3174678357249678921866461 1190504383968629595699923)
                      ·
                        rfl

theorem cell23_2318499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_2318499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318499 prefixEnd_2318499 := by exact prefixLift 2318499
  have htrace : WordTrace (prefixWord ++ tailWord_2318499) baseStart_2318499 baseEnd_2318499 := by
    simpa [prefixWord, tailWord_2318499, baseEnd_2318499] using wordTrace_append hprefix tailTrace_2318499
  have hstable : (prefixWord ++ tailWord_2318499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318499).length < 2 ^ (prefixWord ++ tailWord_2318499).sum := by decide
  have hdescent : baseEnd_2318499 < baseStart_2318499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318512 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_2318512 : Nat := 118140960795 + 2318512 * 2 ^ 59
def prefixEnd_2318512 : Nat := 4983230072969 + 3 ^ 40 * 2318512 * 2
def baseEnd_2318512 : Nat := 1190511059217138044837363

theorem tailTrace_2318512 : CollatzResearch.WordTrace tailWord_2318512 prefixEnd_2318512 1190511059217138044837363 := by
  unfold tailWord_2318512
  simp only [CollatzResearch.WordTrace]
  refine ⟨42281539888217234584950895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56375386517622979446601193 42281539888217234584950895)
  ·
    refine ⟨63422309832325851877426343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42281539888217234584950895 63422309832325851877426343)
    ·
      refine ⟨95133464748488777816139515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63422309832325851877426343 95133464748488777816139515)
      ·
        refine ⟨142700197122733166724209273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95133464748488777816139515 142700197122733166724209273)
        ·
          refine ⟨107025147842049875043156955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142700197122733166724209273 107025147842049875043156955)
          ·
            refine ⟨160537721763074812564735433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107025147842049875043156955 160537721763074812564735433)
            ·
              refine ⟨120403291322306109423551575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160537721763074812564735433 120403291322306109423551575)
              ·
                refine ⟨180604936983459164135327363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120403291322306109423551575 180604936983459164135327363)
                ·
                  refine ⟨270907405475188746202991045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180604936983459164135327363 270907405475188746202991045)
                  ·
                    refine ⟨50795138526597889913060821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270907405475188746202991045 50795138526597889913060821)
                    ·
                      refine ⟨1190511059217138044837363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50795138526597889913060821 1190511059217138044837363)
                      ·
                        rfl

theorem cell23_2318512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_2318512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318512 prefixEnd_2318512 := by exact prefixLift 2318512
  have htrace : WordTrace (prefixWord ++ tailWord_2318512) baseStart_2318512 baseEnd_2318512 := by
    simpa [prefixWord, tailWord_2318512, baseEnd_2318512] using wordTrace_append hprefix tailTrace_2318512
  have hstable : (prefixWord ++ tailWord_2318512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318512).length < 2 ^ (prefixWord ++ tailWord_2318512).sum := by decide
  have hdescent : baseEnd_2318512 < baseStart_2318512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318519 : List Nat := [1, 1, 3, 1, 4, 3, 2, 8]
def baseStart_2318519 : Nat := 118140960795 + 2318519 * 2 ^ 59
def prefixEnd_2318519 : Nat := 4983230072969 + 3 ^ 40 * 2318519 * 2
def baseEnd_2318519 : Nat := 44093135317841463609253

theorem tailTrace_2318519 : CollatzResearch.WordTrace tailWord_2318519 prefixEnd_2318519 44093135317841463609253 := by
  unfold tailWord_2318519
  simp only [CollatzResearch.WordTrace]
  refine ⟨84563335087409109365406611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56375556724939406243604407 84563335087409109365406611)
  ·
    refine ⟨126845002631113664048109917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84563335087409109365406611 126845002631113664048109917)
    ·
      refine ⟨47566875986667624018041219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126845002631113664048109917 47566875986667624018041219)
      ·
        refine ⟨71350313980001436027061829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47566875986667624018041219 71350313980001436027061829)
        ·
          refine ⟨13378183871250269255074093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71350313980001436027061829 13378183871250269255074093)
          ·
            refine ⟨5016818951718850970652785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13378183871250269255074093 5016818951718850970652785)
            ·
              refine ⟨3762614213789138227989589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5016818951718850970652785 3762614213789138227989589)
              ·
                refine ⟨44093135317841463609253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3762614213789138227989589 44093135317841463609253)
                ·
                  rfl

theorem cell23_2318519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 8].length) (baseStart_2318519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318519 prefixEnd_2318519 := by exact prefixLift 2318519
  have htrace : WordTrace (prefixWord ++ tailWord_2318519) baseStart_2318519 baseEnd_2318519 := by
    simpa [prefixWord, tailWord_2318519, baseEnd_2318519] using wordTrace_append hprefix tailTrace_2318519
  have hstable : (prefixWord ++ tailWord_2318519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318519).length < 2 ^ (prefixWord ++ tailWord_2318519).sum := by decide
  have hdescent : baseEnd_2318519 < baseStart_2318519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318530 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2318530 : Nat := 118140960795 + 2318530 * 2 ^ 59
def prefixEnd_2318530 : Nat := 4983230072969 + 3 ^ 40 * 2318530 * 2
def baseEnd_2318530 : Nat := 1190520301868918974412281

theorem tailTrace_2318530 : CollatzResearch.WordTrace tailWord_2318530 prefixEnd_2318530 1190520301868918974412281 := by
  unfold tailWord_2318530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21140934072592314561014261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56375824193579505496038029 21140934072592314561014261)
  ·
    refine ⟨1981962569305529490095087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21140934072592314561014261 1981962569305529490095087)
    ·
      refine ⟨2972943853958294235142631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981962569305529490095087 2972943853958294235142631)
      ·
        refine ⟨4459415780937441352713947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972943853958294235142631 4459415780937441352713947)
        ·
          refine ⟨6689123671406162029070921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459415780937441352713947 6689123671406162029070921)
          ·
            refine ⟨5016842753554621521803191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6689123671406162029070921 5016842753554621521803191)
            ·
              refine ⟨7525264130331932282704787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5016842753554621521803191 7525264130331932282704787)
              ·
                refine ⟨11287896195497898424057181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7525264130331932282704787 11287896195497898424057181)
                ·
                  refine ⟨4232961073311711909021443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11287896195497898424057181 4232961073311711909021443)
                  ·
                    refine ⟨6349441609967567863532165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4232961073311711909021443 6349441609967567863532165)
                    ·
                      refine ⟨1190520301868918974412281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6349441609967567863532165 1190520301868918974412281)
                      ·
                        rfl

theorem cell23_2318530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2318530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318530 prefixEnd_2318530 := by exact prefixLift 2318530
  have htrace : WordTrace (prefixWord ++ tailWord_2318530) baseStart_2318530 baseEnd_2318530 := by
    simpa [prefixWord, tailWord_2318530, baseEnd_2318530] using wordTrace_append hprefix tailTrace_2318530
  have hstable : (prefixWord ++ tailWord_2318530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318530).length < 2 ^ (prefixWord ++ tailWord_2318530).sum := by decide
  have hdescent : baseEnd_2318530 < baseStart_2318530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318546 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2318546 : Nat := 118140960795 + 2318546 * 2 ^ 59
def prefixEnd_2318546 : Nat := 4983230072969 + 3 ^ 40 * 2318546 * 2
def baseEnd_2318546 : Nat := 1190528517559390911812207

theorem tailTrace_2318546 : CollatzResearch.WordTrace tailWord_2318546 prefixEnd_2318546 1190528517559390911812207 := by
  unfold tailWord_2318546
  simp only [CollatzResearch.WordTrace]
  refine ⟨21141079964577823244159873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56376213238874195317759661 21141079964577823244159873)
  ·
    refine ⟨15855809973433367433119905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21141079964577823244159873 15855809973433367433119905)
    ·
      refine ⟨11891857480075025574839929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15855809973433367433119905 11891857480075025574839929)
      ·
        refine ⟨8918893110056269181129947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11891857480075025574839929 8918893110056269181129947)
        ·
          refine ⟨13378339665084403771694921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8918893110056269181129947 13378339665084403771694921)
          ·
            refine ⟨10033754748813302828771191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13378339665084403771694921 10033754748813302828771191)
            ·
              refine ⟨15050632123219954243156787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10033754748813302828771191 15050632123219954243156787)
              ·
                refine ⟨22575948184829931364735181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15050632123219954243156787 22575948184829931364735181)
                ·
                  refine ⟨8465980569311224261775693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22575948184829931364735181 8465980569311224261775693)
                  ·
                    refine ⟨3174742713491709098165885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8465980569311224261775693 3174742713491709098165885)
                    ·
                      refine ⟨1190528517559390911812207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3174742713491709098165885 1190528517559390911812207)
                      ·
                        rfl

theorem cell23_2318546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2318546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318546 prefixEnd_2318546 := by exact prefixLift 2318546
  have htrace : WordTrace (prefixWord ++ tailWord_2318546) baseStart_2318546 baseEnd_2318546 := by
    simpa [prefixWord, tailWord_2318546, baseEnd_2318546] using wordTrace_append hprefix tailTrace_2318546
  have hstable : (prefixWord ++ tailWord_2318546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318546).length < 2 ^ (prefixWord ++ tailWord_2318546).sum := by decide
  have hdescent : baseEnd_2318546 < baseStart_2318546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318550 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2318550 : Nat := 118140960795 + 2318550 * 2 ^ 59
def prefixEnd_2318550 : Nat := 4983230072969 + 3 ^ 40 * 2318550 * 2
def baseEnd_2318550 : Nat := 1190530571482008896162189

theorem tailTrace_2318550 : CollatzResearch.WordTrace tailWord_2318550 prefixEnd_2318550 1190530571482008896162189 := by
  unfold tailWord_2318550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5285279109393550103736569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56376310500197867773190069 5285279109393550103736569)
  ·
    refine ⟨3963959332045162577802427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5285279109393550103736569 3963959332045162577802427)
    ·
      refine ⟨5945938998067743866703641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3963959332045162577802427 5945938998067743866703641)
      ·
        refine ⟨4459454248550807900027731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5945938998067743866703641 4459454248550807900027731)
        ·
          refine ⟨6689181372826211850041597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459454248550807900027731 6689181372826211850041597)
          ·
            refine ⟨2508443014809829443765599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6689181372826211850041597 2508443014809829443765599)
            ·
              refine ⟨3762664522214744165648399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508443014809829443765599 3762664522214744165648399)
              ·
                refine ⟨5643996783322116248472599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3762664522214744165648399 5643996783322116248472599)
                ·
                  refine ⟨8465995174983174372708899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5643996783322116248472599 8465995174983174372708899)
                  ·
                    refine ⟨12698992762474761559063349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8465995174983174372708899 12698992762474761559063349)
                    ·
                      refine ⟨1190530571482008896162189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12698992762474761559063349 1190530571482008896162189)
                      ·
                        rfl

theorem cell23_2318550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2318550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318550 prefixEnd_2318550 := by exact prefixLift 2318550
  have htrace : WordTrace (prefixWord ++ tailWord_2318550) baseStart_2318550 baseEnd_2318550 := by
    simpa [prefixWord, tailWord_2318550, baseEnd_2318550] using wordTrace_append hprefix tailTrace_2318550
  have hstable : (prefixWord ++ tailWord_2318550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318550).length < 2 ^ (prefixWord ++ tailWord_2318550).sum := by decide
  have hdescent : baseEnd_2318550 < baseStart_2318550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318579 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 2, 6]
def baseStart_2318579 : Nat := 118140960795 + 2318579 * 2 ^ 59
def prefixEnd_2318579 : Nat := 4983230072969 + 3 ^ 40 * 2318579 * 2
def baseEnd_2318579 : Nat := 396848487473663094233185

theorem tailTrace_2318579 : CollatzResearch.WordTrace tailWord_2318579 prefixEnd_2318579 396848487473663094233185 := by
  unfold tailWord_2318579
  simp only [CollatzResearch.WordTrace]
  refine ⟨84565523467191739612590791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56377015644794493075060527 84565523467191739612590791)
  ·
    refine ⟨126848285200787609418886187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84565523467191739612590791 126848285200787609418886187)
    ·
      refine ⟨190272427801181414128329281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126848285200787609418886187 190272427801181414128329281)
      ·
        refine ⟨142704320850886060596246961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190272427801181414128329281 142704320850886060596246961)
        ·
          refine ⟨107028240638164545447185221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142704320850886060596246961 107028240638164545447185221)
          ·
            refine ⟨20067795119655852271347229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107028240638164545447185221 20067795119655852271347229)
            ·
              refine ⟨7525423169870944601755211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20067795119655852271347229 7525423169870944601755211)
              ·
                refine ⟨11288134754806416902632817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7525423169870944601755211 11288134754806416902632817)
                ·
                  refine ⟨8466101066104812676974613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11288134754806416902632817 8466101066104812676974613)
                  ·
                    refine ⟨396848487473663094233185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8466101066104812676974613 396848487473663094233185)
                    ·
                      rfl

theorem cell23_2318579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 6].length) (baseStart_2318579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318579 prefixEnd_2318579 := by exact prefixLift 2318579
  have htrace : WordTrace (prefixWord ++ tailWord_2318579) baseStart_2318579 baseEnd_2318579 := by
    simpa [prefixWord, tailWord_2318579, baseEnd_2318579] using wordTrace_append hprefix tailTrace_2318579
  have hstable : (prefixWord ++ tailWord_2318579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318579).length < 2 ^ (prefixWord ++ tailWord_2318579).sum := by decide
  have hdescent : baseEnd_2318579 < baseStart_2318579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318589 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_2318589 : Nat := 118140960795 + 2318589 * 2 ^ 59
def prefixEnd_2318589 : Nat := 4983230072969 + 3 ^ 40 * 2318589 * 2
def baseEnd_2318589 : Nat := 1190550597227534243574509

theorem tailTrace_2318589 : CollatzResearch.WordTrace tailWord_2318589 prefixEnd_2318589 1190550597227534243574509 := by
  unfold tailWord_2318589
  simp only [CollatzResearch.WordTrace]
  refine ⟨84565888197155511320454821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56377258798103674213636547 84565888197155511320454821)
  ·
    refine ⟨15856104036966658372585279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84565888197155511320454821 15856104036966658372585279)
    ·
      refine ⟨23784156055449987558877919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15856104036966658372585279 23784156055449987558877919)
      ·
        refine ⟨35676234083174981338316879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23784156055449987558877919 35676234083174981338316879)
        ·
          refine ⟨53514351124762472007475319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35676234083174981338316879 53514351124762472007475319)
          ·
            refine ⟨80271526687143708011212979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53514351124762472007475319 80271526687143708011212979)
            ·
              refine ⟨120407290030715562016819469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80271526687143708011212979 120407290030715562016819469)
              ·
                refine ⟨45152733761518335756307301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120407290030715562016819469 45152733761518335756307301)
                ·
                  refine ⟨8466137580284687954307619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45152733761518335756307301 8466137580284687954307619)
                  ·
                    refine ⟨12699206370427031931461429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8466137580284687954307619 12699206370427031931461429)
                    ·
                      refine ⟨1190550597227534243574509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12699206370427031931461429 1190550597227534243574509)
                      ·
                        rfl

theorem cell23_2318589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_2318589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318589 prefixEnd_2318589 := by exact prefixLift 2318589
  have htrace : WordTrace (prefixWord ++ tailWord_2318589) baseStart_2318589 baseEnd_2318589 := by
    simpa [prefixWord, tailWord_2318589, baseEnd_2318589] using wordTrace_append hprefix tailTrace_2318589
  have hstable : (prefixWord ++ tailWord_2318589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318589).length < 2 ^ (prefixWord ++ tailWord_2318589).sum := by decide
  have hdescent : baseEnd_2318589 < baseStart_2318589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318590 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_2318590 : Nat := 118140960795 + 2318590 * 2 ^ 59
def prefixEnd_2318590 : Nat := 4983230072969 + 3 ^ 40 * 2318590 * 2
def baseEnd_2318590 : Nat := 1190551110708188739662005

theorem tailTrace_2318590 : CollatzResearch.WordTrace tailWord_2318590 prefixEnd_2318590 1190551110708188739662005 := by
  unfold tailWord_2318590
  simp only [CollatzResearch.WordTrace]
  refine ⟨10570740583768986061405153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56377283113434592327494149 10570740583768986061405153)
  ·
    refine ⟨7928055437826739546053865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10570740583768986061405153 7928055437826739546053865)
    ·
      refine ⟨5946041578370054659540399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7928055437826739546053865 5946041578370054659540399)
      ·
        refine ⟨8919062367555081989310599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5946041578370054659540399 8919062367555081989310599)
        ·
          refine ⟨13378593551332622983965899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8919062367555081989310599 13378593551332622983965899)
          ·
            refine ⟨20067890326998934475948849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13378593551332622983965899 20067890326998934475948849)
            ·
              refine ⟨15050917745249200856961637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20067890326998934475948849 15050917745249200856961637)
              ·
                refine ⟨2822047077234225160680307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15050917745249200856961637 2822047077234225160680307)
                ·
                  refine ⟨4233070615851337741020461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822047077234225160680307 4233070615851337741020461)
                  ·
                    refine ⟨1587401480944251652882673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4233070615851337741020461 1587401480944251652882673)
                    ·
                      refine ⟨1190551110708188739662005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1587401480944251652882673 1190551110708188739662005)
                      ·
                        rfl

theorem cell23_2318590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_2318590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318590 prefixEnd_2318590 := by exact prefixLift 2318590
  have htrace : WordTrace (prefixWord ++ tailWord_2318590) baseStart_2318590 baseEnd_2318590 := by
    simpa [prefixWord, tailWord_2318590, baseEnd_2318590] using wordTrace_append hprefix tailTrace_2318590
  have hstable : (prefixWord ++ tailWord_2318590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318590).length < 2 ^ (prefixWord ++ tailWord_2318590).sum := by decide
  have hdescent : baseEnd_2318590 < baseStart_2318590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318603 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 4, 2, 2]
def baseStart_2318603 : Nat := 118140960795 + 2318603 * 2 ^ 59
def prefixEnd_2318603 : Nat := 4983230072969 + 3 ^ 40 * 2318603 * 2
def baseEnd_2318603 : Nat := 1190557785956697188799445

theorem tailTrace_2318603 : CollatzResearch.WordTrace tailWord_2318603 prefixEnd_2318603 1190557785956697188799445 := by
  unfold tailWord_2318603
  simp only [CollatzResearch.WordTrace]
  refine ⟨84566398819104791711464463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56377599212736527807642975 84566398819104791711464463)
  ·
    refine ⟨126849598228657187567196695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84566398819104791711464463 126849598228657187567196695)
    ·
      refine ⟨190274397342985781350795043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126849598228657187567196695 190274397342985781350795043)
      ·
        refine ⟨285411596014478672026192565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190274397342985781350795043 285411596014478672026192565)
        ·
          refine ⟨26757337126357375502455553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285411596014478672026192565 26757337126357375502455553)
          ·
            refine ⟨20068002844768031626841665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26757337126357375502455553 20068002844768031626841665)
            ·
              refine ⟨15051002133576023720131249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20068002844768031626841665 15051002133576023720131249)
              ·
                refine ⟨11288251600182017790098437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15051002133576023720131249 11288251600182017790098437)
                ·
                  refine ⟨2116547175034128335643457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11288251600182017790098437 2116547175034128335643457)
                  ·
                    refine ⟨1587410381275596251732593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2116547175034128335643457 1587410381275596251732593)
                    ·
                      refine ⟨1190557785956697188799445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1587410381275596251732593 1190557785956697188799445)
                      ·
                        rfl

theorem cell23_2318603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 2, 2].length) (baseStart_2318603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318603 prefixEnd_2318603 := by exact prefixLift 2318603
  have htrace : WordTrace (prefixWord ++ tailWord_2318603) baseStart_2318603 baseEnd_2318603 := by
    simpa [prefixWord, tailWord_2318603, baseEnd_2318603] using wordTrace_append hprefix tailTrace_2318603
  have hstable : (prefixWord ++ tailWord_2318603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318603).length < 2 ^ (prefixWord ++ tailWord_2318603).sum := by decide
  have hdescent : baseEnd_2318603 < baseStart_2318603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318626 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 7]
def baseStart_2318626 : Nat := 118140960795 + 2318626 * 2 ^ 59
def prefixEnd_2318626 : Nat := 4983230072969 + 3 ^ 40 * 2318626 * 2
def baseEnd_2318626 : Nat := 132285510667972288756871

theorem tailTrace_2318626 : CollatzResearch.WordTrace tailWord_2318626 prefixEnd_2318626 132285510667972288756871 := by
  unfold tailWord_2318626
  simp only [CollatzResearch.WordTrace]
  refine ⟨21141809424505366659887933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56378158465347644426367821 21141809424505366659887933)
  ·
    refine ⟨7928178534189512497457975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21141809424505366659887933 7928178534189512497457975)
    ·
      refine ⟨11892267801284268746186963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7928178534189512497457975 11892267801284268746186963)
      ·
        refine ⟨17838401701926403119280445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11892267801284268746186963 17838401701926403119280445)
        ·
          refine ⟨6689400638222401169730167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17838401701926403119280445 6689400638222401169730167)
          ·
            refine ⟨10034100957333601754595251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6689400638222401169730167 10034100957333601754595251)
            ·
              refine ⟨15051151436000402631892877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10034100957333601754595251 15051151436000402631892877)
              ·
                refine ⟨5644181788500150986959829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15051151436000402631892877 5644181788500150986959829)
                ·
                  refine ⟨132285510667972288756871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5644181788500150986959829 132285510667972288756871)
                  ·
                    rfl

theorem cell23_2318626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_2318626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318626 prefixEnd_2318626 := by exact prefixLift 2318626
  have htrace : WordTrace (prefixWord ++ tailWord_2318626) baseStart_2318626 baseEnd_2318626 := by
    simpa [prefixWord, tailWord_2318626, baseEnd_2318626] using wordTrace_append hprefix tailTrace_2318626
  have hstable : (prefixWord ++ tailWord_2318626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318626).length < 2 ^ (prefixWord ++ tailWord_2318626).sum := by decide
  have hdescent : baseEnd_2318626 < baseStart_2318626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318631 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2318631 : Nat := 118140960795 + 2318631 * 2 ^ 59
def prefixEnd_2318631 : Nat := 4983230072969 + 3 ^ 40 * 2318631 * 2
def baseEnd_2318631 : Nat := 1190572163415023079249317

theorem tailTrace_2318631 : CollatzResearch.WordTrace tailWord_2318631 prefixEnd_2318631 1190572163415023079249317 := by
  unfold tailWord_2318631
  simp only [CollatzResearch.WordTrace]
  refine ⟨84567420063003352493483747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56378280042002234995655831 84567420063003352493483747)
  ·
    refine ⟨126851130094505028740225621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84567420063003352493483747 126851130094505028740225621)
    ·
      refine ⟨1486536680794980805549519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 126851130094505028740225621 1486536680794980805549519)
      ·
        refine ⟨2229805021192471208324279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486536680794980805549519 2229805021192471208324279)
        ·
          refine ⟨3344707531788706812486419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2229805021192471208324279 3344707531788706812486419)
          ·
            refine ⟨5017061297683060218729629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344707531788706812486419 5017061297683060218729629)
            ·
              refine ⟨1881397986631147582023611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5017061297683060218729629 1881397986631147582023611)
              ·
                refine ⟨2822096979946721373035417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881397986631147582023611 2822096979946721373035417)
                ·
                  refine ⟨2116572734960041029776563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2822096979946721373035417 2116572734960041029776563)
                  ·
                    refine ⟨3174859102440061544664845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2116572734960041029776563 3174859102440061544664845)
                    ·
                      refine ⟨1190572163415023079249317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3174859102440061544664845 1190572163415023079249317)
                      ·
                        rfl

theorem cell23_2318631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2318631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318631 prefixEnd_2318631 := by exact prefixLift 2318631
  have htrace : WordTrace (prefixWord ++ tailWord_2318631) baseStart_2318631 baseEnd_2318631 := by
    simpa [prefixWord, tailWord_2318631, baseEnd_2318631] using wordTrace_append hprefix tailTrace_2318631
  have hstable : (prefixWord ++ tailWord_2318631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318631).length < 2 ^ (prefixWord ++ tailWord_2318631).sum := by decide
  have hdescent : baseEnd_2318631 < baseStart_2318631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318636 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_2318636 : Nat := 118140960795 + 2318636 * 2 ^ 59
def prefixEnd_2318636 : Nat := 4983230072969 + 3 ^ 40 * 2318636 * 2
def baseEnd_2318636 : Nat := 1190574730818295559686793

theorem tailTrace_2318636 : CollatzResearch.WordTrace tailWord_2318636 prefixEnd_2318636 1190574730818295559686793 := by
  unfold tailWord_2318636
  simp only [CollatzResearch.WordTrace]
  refine ⟨42283801213992619173707881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56378401618656825564943841 42283801213992619173707881)
  ·
    refine ⟨31712850910494464380280911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42283801213992619173707881 31712850910494464380280911)
    ·
      refine ⟨47569276365741696570421367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31712850910494464380280911 47569276365741696570421367)
      ·
        refine ⟨71353914548612544855632051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47569276365741696570421367 71353914548612544855632051)
        ·
          refine ⟨107030871822918817283448077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71353914548612544855632051 107030871822918817283448077)
          ·
            refine ⟨40136576933594556481293029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107030871822918817283448077 40136576933594556481293029)
            ·
              refine ⟨7525608175048979340242443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40136576933594556481293029 7525608175048979340242443)
              ·
                refine ⟨11288412262573469010363665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7525608175048979340242443 11288412262573469010363665)
                ·
                  refine ⟨8466309196930101757772749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11288412262573469010363665 8466309196930101757772749)
                  ·
                    refine ⟨3174865948848788159164781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8466309196930101757772749 3174865948848788159164781)
                    ·
                      refine ⟨1190574730818295559686793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3174865948848788159164781 1190574730818295559686793)
                      ·
                        rfl

theorem cell23_2318636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_2318636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318636 prefixEnd_2318636 := by exact prefixLift 2318636
  have htrace : WordTrace (prefixWord ++ tailWord_2318636) baseStart_2318636 baseEnd_2318636 := by
    simpa [prefixWord, tailWord_2318636, baseEnd_2318636] using wordTrace_append hprefix tailTrace_2318636
  have hstable : (prefixWord ++ tailWord_2318636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318636).length < 2 ^ (prefixWord ++ tailWord_2318636).sum := by decide
  have hdescent : baseEnd_2318636 < baseStart_2318636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318639 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 1, 7]
def baseStart_2318639 : Nat := 118140960795 + 2318639 * 2 ^ 59
def prefixEnd_2318639 : Nat := 4983230072969 + 3 ^ 40 * 2318639 * 2
def baseEnd_2318639 : Nat := 396858757086753015983093

theorem tailTrace_2318639 : CollatzResearch.WordTrace tailWord_2318639 prefixEnd_2318639 396858757086753015983093 := by
  unfold tailWord_2318639
  simp only [CollatzResearch.WordTrace]
  refine ⟨84567711846974369859774971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56378474564649579906516647 84567711846974369859774971)
  ·
    refine ⟨126851567770461554789662457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84567711846974369859774971 126851567770461554789662457)
    ·
      refine ⟨95138675827846166092246843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126851567770461554789662457 95138675827846166092246843)
      ·
        refine ⟨142708013741769249138370265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95138675827846166092246843 142708013741769249138370265)
        ·
          refine ⟨107031010306326936853777699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142708013741769249138370265 107031010306326936853777699)
          ·
            refine ⟨160546515459490405280666549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107031010306326936853777699 160546515459490405280666549)
            ·
              refine ⟨15051235824327225495062489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160546515459490405280666549 15051235824327225495062489)
              ·
                refine ⟨11288426868245419121296867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15051235824327225495062489 11288426868245419121296867)
                ·
                  refine ⟨16932640302368128681945301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11288426868245419121296867 16932640302368128681945301)
                  ·
                    refine ⟨396858757086753015983093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16932640302368128681945301 396858757086753015983093)
                    ·
                      rfl

theorem cell23_2318639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_2318639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318639 prefixEnd_2318639 := by exact prefixLift 2318639
  have htrace : WordTrace (prefixWord ++ tailWord_2318639) baseStart_2318639 baseEnd_2318639 := by
    simpa [prefixWord, tailWord_2318639, baseEnd_2318639] using wordTrace_append hprefix tailTrace_2318639
  have hstable : (prefixWord ++ tailWord_2318639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318639).length < 2 ^ (prefixWord ++ tailWord_2318639).sum := by decide
  have hdescent : baseEnd_2318639 < baseStart_2318639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318750 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_2318750 : Nat := 118140960795 + 2318750 * 2 ^ 59
def prefixEnd_2318750 : Nat := 4983230072969 + 3 ^ 40 * 2318750 * 2
def baseEnd_2318750 : Nat := 132292585290323123740141

theorem tailTrace_2318750 : CollatzResearch.WordTrace tailWord_2318750 prefixEnd_2318750 132292585290323123740141 := by
  unfold tailWord_2318750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10571470043696529477133213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56381173566381490544710469 10571470043696529477133213)
  ·
    refine ⟨3964301266386198553924955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10571470043696529477133213 3964301266386198553924955)
    ·
      refine ⟨5946451899579297830887433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964301266386198553924955 5946451899579297830887433)
      ·
        refine ⟨4459838924684473373165575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5946451899579297830887433 4459838924684473373165575)
        ·
          refine ⟨6689758387026710059748363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459838924684473373165575 6689758387026710059748363)
          ·
            refine ⟨10034637580540065089622545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6689758387026710059748363 10034637580540065089622545)
            ·
              refine ⟨7525978185405048817216909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10034637580540065089622545 7525978185405048817216909)
              ·
                refine ⟨2822241819526893306456341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7525978185405048817216909 2822241819526893306456341)
                ·
                  refine ⟨132292585290323123740141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2822241819526893306456341 132292585290323123740141)
                  ·
                    rfl

theorem cell23_2318750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_2318750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318750 prefixEnd_2318750 := by exact prefixLift 2318750
  have htrace : WordTrace (prefixWord ++ tailWord_2318750) baseStart_2318750 baseEnd_2318750 := by
    simpa [prefixWord, tailWord_2318750, baseEnd_2318750] using wordTrace_append hprefix tailTrace_2318750
  have hstable : (prefixWord ++ tailWord_2318750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318750).length < 2 ^ (prefixWord ++ tailWord_2318750).sum := by decide
  have hdescent : baseEnd_2318750 < baseStart_2318750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318777 : List Nat := [1, 2, 1, 4, 3, 1, 1, 5, 1, 1, 3]
def baseStart_2318777 : Nat := 118140960795 + 2318777 * 2 ^ 59
def prefixEnd_2318777 : Nat := 4983230072969 + 3 ^ 40 * 2318777 * 2
def baseEnd_2318777 : Nat := 1190647131590579508023645

theorem tailTrace_2318777 : CollatzResearch.WordTrace tailWord_2318777 prefixEnd_2318777 1190647131590579508023645 := by
  unfold tailWord_2318777
  simp only [CollatzResearch.WordTrace]
  refine ⟨84572745120474419428298585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56381830080316279618865723 84572745120474419428298585)
  ·
    refine ⟨63429558840355814571223939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84572745120474419428298585 63429558840355814571223939)
    ·
      refine ⟨95144338260533721856835909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63429558840355814571223939 95144338260533721856835909)
      ·
        refine ⟨17839563423850072848156733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95144338260533721856835909 17839563423850072848156733)
        ·
          refine ⟨6689836283943777318058775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17839563423850072848156733 6689836283943777318058775)
          ·
            refine ⟨10034754425915665977088163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6689836283943777318058775 10034754425915665977088163)
            ·
              refine ⟨15052131638873498965632245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10034754425915665977088163 15052131638873498965632245)
              ·
                refine ⟨1411137341144390528028023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15052131638873498965632245 1411137341144390528028023)
                ·
                  refine ⟨2116706011716585792042035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411137341144390528028023 2116706011716585792042035)
                  ·
                    refine ⟨3175059017574878688063053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2116706011716585792042035 3175059017574878688063053)
                    ·
                      refine ⟨1190647131590579508023645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175059017574878688063053 1190647131590579508023645)
                      ·
                        rfl

theorem cell23_2318777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_2318777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318777 prefixEnd_2318777 := by exact prefixLift 2318777
  have htrace : WordTrace (prefixWord ++ tailWord_2318777) baseStart_2318777 baseEnd_2318777 := by
    simpa [prefixWord, tailWord_2318777, baseEnd_2318777] using wordTrace_append hprefix tailTrace_2318777
  have hstable : (prefixWord ++ tailWord_2318777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318777).length < 2 ^ (prefixWord ++ tailWord_2318777).sum := by decide
  have hdescent : baseEnd_2318777 < baseStart_2318777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318780 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_2318780 : Nat := 118140960795 + 2318780 * 2 ^ 59
def prefixEnd_2318780 : Nat := 4983230072969 + 3 ^ 40 * 2318780 * 2
def baseEnd_2318780 : Nat := 396882890677514332095377

theorem tailTrace_2318780 : CollatzResearch.WordTrace tailWord_2318780 prefixEnd_2318780 396882890677514332095377 := by
  unfold tailWord_2318780
  simp only [CollatzResearch.WordTrace]
  refine ⟨42286427269731775470328897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56381903026309033960438529 42286427269731775470328897)
  ·
    refine ⟨31714820452298831602746673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42286427269731775470328897 31714820452298831602746673)
    ·
      refine ⟨23786115339224123702060005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31714820452298831602746673 23786115339224123702060005)
      ·
        refine ⟨4459896626104523194136251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23786115339224123702060005 4459896626104523194136251)
        ·
          refine ⟨6689844939156784791204377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459896626104523194136251 6689844939156784791204377)
          ·
            refine ⟨5017383704367588593403283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6689844939156784791204377 5017383704367588593403283)
            ·
              refine ⟨7526075556551382890104925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017383704367588593403283 7526075556551382890104925)
              ·
                refine ⟨2822278333706768583789347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7526075556551382890104925 2822278333706768583789347)
                ·
                  refine ⟨4233417500560152875684021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822278333706768583789347 4233417500560152875684021)
                  ·
                    refine ⟨396882890677514332095377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4233417500560152875684021 396882890677514332095377)
                    ·
                      rfl

theorem cell23_2318780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_2318780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318780 prefixEnd_2318780 := by exact prefixLift 2318780
  have htrace : WordTrace (prefixWord ++ tailWord_2318780) baseStart_2318780 baseEnd_2318780 := by
    simpa [prefixWord, tailWord_2318780, baseEnd_2318780] using wordTrace_append hprefix tailTrace_2318780
  have hstable : (prefixWord ++ tailWord_2318780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318780).length < 2 ^ (prefixWord ++ tailWord_2318780).sum := by decide
  have hdescent : baseEnd_2318780 < baseStart_2318780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318813 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2318813 : Nat := 118140960795 + 2318813 * 2 ^ 59
def prefixEnd_2318813 : Nat := 4983230072969 + 3 ^ 40 * 2318813 * 2
def baseEnd_2318813 : Nat := 1190665616894141367173479

theorem tailTrace_2318813 : CollatzResearch.WordTrace tailWord_2318813 prefixEnd_2318813 1190665616894141367173479 := by
  unfold tailWord_2318813
  simp only [CollatzResearch.WordTrace]
  refine ⟨84574058148343997576609093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56382705432229331717739395 84574058148343997576609093)
  ·
    refine ⟨15857635902814499545614205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84574058148343997576609093 15857635902814499545614205)
    ·
      refine ⟨5946613463555437329605327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15857635902814499545614205 5946613463555437329605327)
      ·
        refine ⟨8919920195333155994407991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5946613463555437329605327 8919920195333155994407991)
        ·
          refine ⟨13379880292999733991611987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8919920195333155994407991 13379880292999733991611987)
          ·
            refine ⟨20069820439499600987417981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13379880292999733991611987 20069820439499600987417981)
            ·
              refine ⟨7526182664812350370281743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20069820439499600987417981 7526182664812350370281743)
              ·
                refine ⟨11289273997218525555422615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526182664812350370281743 11289273997218525555422615)
                ·
                  refine ⟨16933910995827788333133923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11289273997218525555422615 16933910995827788333133923)
                  ·
                    refine ⟨25400866493741682499700885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16933910995827788333133923 25400866493741682499700885)
                    ·
                      refine ⟨1190665616894141367173479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25400866493741682499700885 1190665616894141367173479)
                      ·
                        rfl

theorem cell23_2318813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2318813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318813 prefixEnd_2318813 := by exact prefixLift 2318813
  have htrace : WordTrace (prefixWord ++ tailWord_2318813) baseStart_2318813 baseEnd_2318813 := by
    simpa [prefixWord, tailWord_2318813, baseEnd_2318813] using wordTrace_append hprefix tailTrace_2318813
  have hstable : (prefixWord ++ tailWord_2318813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318813).length < 2 ^ (prefixWord ++ tailWord_2318813).sum := by decide
  have hdescent : baseEnd_2318813 < baseStart_2318813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318833 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_2318833 : Nat := 118140960795 + 2318833 * 2 ^ 59
def prefixEnd_2318833 : Nat := 4983230072969 + 3 ^ 40 * 2318833 * 2
def baseEnd_2318833 : Nat := 1190675886507231288923387

theorem tailTrace_2318833 : CollatzResearch.WordTrace tailWord_2318833 prefixEnd_2318833 1190675886507231288923387 := by
  unfold tailWord_2318833
  simp only [CollatzResearch.WordTrace]
  refine ⟨84574787608271540992337153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56383191738847693994891435 84574787608271540992337153)
  ·
    refine ⟨63431090706203655744252865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84574787608271540992337153 63431090706203655744252865)
    ·
      refine ⟨47573318029652741808189649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63431090706203655744252865 47573318029652741808189649)
      ·
        refine ⟨35679988522239556356142237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47573318029652741808189649 35679988522239556356142237)
        ·
          refine ⟨13379995695839833633553339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35679988522239556356142237 13379995695839833633553339)
          ·
            refine ⟨20069993543759750450330009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13379995695839833633553339 20069993543759750450330009)
            ·
              refine ⟨15052495157819812837747507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20069993543759750450330009 15052495157819812837747507)
              ·
                refine ⟨22578742736729719256621261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15052495157819812837747507 22578742736729719256621261)
                ·
                  refine ⟨8467028526273644721232973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22578742736729719256621261 8467028526273644721232973)
                  ·
                    refine ⟨3175135697352616770462365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8467028526273644721232973 3175135697352616770462365)
                    ·
                      refine ⟨1190675886507231288923387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175135697352616770462365 1190675886507231288923387)
                      ·
                        rfl

theorem cell23_2318833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_2318833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318833 prefixEnd_2318833 := by exact prefixLift 2318833
  have htrace : WordTrace (prefixWord ++ tailWord_2318833) baseStart_2318833 baseEnd_2318833 := by
    simpa [prefixWord, tailWord_2318833, baseEnd_2318833] using wordTrace_append hprefix tailTrace_2318833
  have hstable : (prefixWord ++ tailWord_2318833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318833).length < 2 ^ (prefixWord ++ tailWord_2318833).sum := by decide
  have hdescent : baseEnd_2318833 < baseStart_2318833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318837 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2318837 : Nat := 118140960795 + 2318837 * 2 ^ 59
def prefixEnd_2318837 : Nat := 4983230072969 + 3 ^ 40 * 2318837 * 2
def baseEnd_2318837 : Nat := 1190677940429849273273369

theorem tailTrace_2318837 : CollatzResearch.WordTrace tailWord_2318837 prefixEnd_2318837 1190677940429849273273369 := by
  unfold tailWord_2318837
  simp only [CollatzResearch.WordTrace]
  refine ⟨84574933500257049675482765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56383289000171366450321843 84574933500257049675482765)
  ·
    refine ⟨31715600062596393628306037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84574933500257049675482765 31715600062596393628306037)
    ·
      refine ⟨2973337505868411902653691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31715600062596393628306037 2973337505868411902653691)
      ·
        refine ⟨4460006258802617853980537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973337505868411902653691 4460006258802617853980537)
        ·
          refine ⟨3345004694101963390485403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4460006258802617853980537 3345004694101963390485403)
          ·
            refine ⟨5017507041152945085728105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345004694101963390485403 5017507041152945085728105)
            ·
              refine ⟨3763130280864708814296079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5017507041152945085728105 3763130280864708814296079)
              ·
                refine ⟨5644695421297063221444119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763130280864708814296079 5644695421297063221444119)
                ·
                  refine ⟨8467043131945594832166179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5644695421297063221444119 8467043131945594832166179)
                  ·
                    refine ⟨12700564697918392248249269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8467043131945594832166179 12700564697918392248249269)
                    ·
                      refine ⟨1190677940429849273273369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12700564697918392248249269 1190677940429849273273369)
                      ·
                        rfl

theorem cell23_2318837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2318837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318837 prefixEnd_2318837 := by exact prefixLift 2318837
  have htrace : WordTrace (prefixWord ++ tailWord_2318837) baseStart_2318837 baseEnd_2318837 := by
    simpa [prefixWord, tailWord_2318837, baseEnd_2318837] using wordTrace_append hprefix tailTrace_2318837
  have hstable : (prefixWord ++ tailWord_2318837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318837).length < 2 ^ (prefixWord ++ tailWord_2318837).sum := by decide
  have hdescent : baseEnd_2318837 < baseStart_2318837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318854 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2318854 : Nat := 118140960795 + 2318854 * 2 ^ 59
def prefixEnd_2318854 : Nat := 4983230072969 + 3 ^ 40 * 2318854 * 2
def baseEnd_2318854 : Nat := 1190686669600975706760791

theorem tailTrace_2318854 : CollatzResearch.WordTrace tailWord_2318854 prefixEnd_2318854 1190686669600975706760791 := by
  unfold tailWord_2318854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642986048162358174339113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56383702360796974385901077 2642986048162358174339113)
  ·
    refine ⟨1982239536121768630754335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2642986048162358174339113 1982239536121768630754335)
    ·
      refine ⟨2973359304182652946131503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982239536121768630754335 2973359304182652946131503)
      ·
        refine ⟨4460038956273979419197255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973359304182652946131503 4460038956273979419197255)
        ·
          refine ⟨6690058434410969128795883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4460038956273979419197255 6690058434410969128795883)
          ·
            refine ⟨10035087651616453693193825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6690058434410969128795883 10035087651616453693193825)
            ·
              refine ⟨7526315738712340269895369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10035087651616453693193825 7526315738712340269895369)
              ·
                refine ⟨5644736804034255202421527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7526315738712340269895369 5644736804034255202421527)
                ·
                  refine ⟨8467105206051382803632291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5644736804034255202421527 8467105206051382803632291)
                  ·
                    refine ⟨12700657809077074205448437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8467105206051382803632291 12700657809077074205448437)
                    ·
                      refine ⟨1190686669600975706760791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12700657809077074205448437 1190686669600975706760791)
                      ·
                        rfl

theorem cell23_2318854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2318854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318854 prefixEnd_2318854 := by exact prefixLift 2318854
  have htrace : WordTrace (prefixWord ++ tailWord_2318854) baseStart_2318854 baseEnd_2318854 := by
    simpa [prefixWord, tailWord_2318854, baseEnd_2318854] using wordTrace_append hprefix tailTrace_2318854
  have hstable : (prefixWord ++ tailWord_2318854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318854).length < 2 ^ (prefixWord ++ tailWord_2318854).sum := by decide
  have hdescent : baseEnd_2318854 < baseStart_2318854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318861 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2318861 : Nat := 118140960795 + 2318861 * 2 ^ 59
def prefixEnd_2318861 : Nat := 4983230072969 + 3 ^ 40 * 2318861 * 2
def baseEnd_2318861 : Nat := 396896754655185726457753

theorem tailTrace_2318861 : CollatzResearch.WordTrace tailWord_2318861 prefixEnd_2318861 396896754655185726457753 := by
  unfold tailWord_2318861
  simp only [CollatzResearch.WordTrace]
  refine ⟨84575808852170101774356437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56383872568113401182904291 84575808852170101774356437)
  ·
    refine ⟨1982245519972736760336479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 84575808852170101774356437 1982245519972736760336479)
    ·
      refine ⟨2973368279959105140504719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982245519972736760336479 2973368279959105140504719)
      ·
        refine ⟨4460052419938657710757079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973368279959105140504719 4460052419938657710757079)
        ·
          refine ⟨6690078629907986566135619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4460052419938657710757079 6690078629907986566135619)
          ·
            refine ⟨10035117944861979849203429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6690078629907986566135619 10035117944861979849203429)
            ·
              refine ⟨1881584614661621221725643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10035117944861979849203429 1881584614661621221725643)
              ·
                refine ⟨2822376921992431832588465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881584614661621221725643 2822376921992431832588465)
                ·
                  refine ⟨2116782691494323874441349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2822376921992431832588465 2116782691494323874441349)
                  ·
                    refine ⟨396896754655185726457753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2116782691494323874441349 396896754655185726457753)
                    ·
                      rfl

theorem cell23_2318861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2318861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318861 prefixEnd_2318861 := by exact prefixLift 2318861
  have htrace : WordTrace (prefixWord ++ tailWord_2318861) baseStart_2318861 baseEnd_2318861 := by
    simpa [prefixWord, tailWord_2318861, baseEnd_2318861] using wordTrace_append hprefix tailTrace_2318861
  have hstable : (prefixWord ++ tailWord_2318861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318861).length < 2 ^ (prefixWord ++ tailWord_2318861).sum := by decide
  have hdescent : baseEnd_2318861 < baseStart_2318861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318871 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2318871 : Nat := 118140960795 + 2318871 * 2 ^ 59
def prefixEnd_2318871 : Nat := 4983230072969 + 3 ^ 40 * 2318871 * 2
def baseEnd_2318871 : Nat := 1190695398772102140248213

theorem tailTrace_2318871 : CollatzResearch.WordTrace tailWord_2318871 prefixEnd_2318871 1190695398772102140248213 := by
  unfold tailWord_2318871
  simp only [CollatzResearch.WordTrace]
  refine ⟨84576173582133873482220467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56384115721422582321480311 84576173582133873482220467)
  ·
    refine ⟨126864260373200810223330701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84576173582133873482220467 126864260373200810223330701)
    ·
      refine ⟨47574097639950303833749013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126864260373200810223330701 47574097639950303833749013)
      ·
        refine ⟨2230035826872670492206985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47574097639950303833749013 2230035826872670492206985)
        ·
          refine ⟨1672526870154502869155239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2230035826872670492206985 1672526870154502869155239)
          ·
            refine ⟨2508790305231754303732859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672526870154502869155239 2508790305231754303732859)
            ·
              refine ⟨3763185457847631455599289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508790305231754303732859 3763185457847631455599289)
              ·
                refine ⟨2822389093385723591699467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3763185457847631455599289 2822389093385723591699467)
                ·
                  refine ⟨4233583640078585387549201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822389093385723591699467 4233583640078585387549201)
                  ·
                    refine ⟨3175187730058939040661901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4233583640078585387549201 3175187730058939040661901)
                    ·
                      refine ⟨1190695398772102140248213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175187730058939040661901 1190695398772102140248213)
                      ·
                        rfl

theorem cell23_2318871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2318871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318871 prefixEnd_2318871 := by exact prefixLift 2318871
  have htrace : WordTrace (prefixWord ++ tailWord_2318871) baseStart_2318871 baseEnd_2318871 := by
    simpa [prefixWord, tailWord_2318871, baseEnd_2318871] using wordTrace_append hprefix tailTrace_2318871
  have hstable : (prefixWord ++ tailWord_2318871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318871).length < 2 ^ (prefixWord ++ tailWord_2318871).sum := by decide
  have hdescent : baseEnd_2318871 < baseStart_2318871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318877 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_2318877 : Nat := 118140960795 + 2318877 * 2 ^ 59
def prefixEnd_2318877 : Nat := 4983230072969 + 3 ^ 40 * 2318877 * 2
def baseEnd_2318877 : Nat := 1190698479656029116773185

theorem tailTrace_2318877 : CollatzResearch.WordTrace tailWord_2318877 prefixEnd_2318877 1190698479656029116773185 := by
  unfold tailWord_2318877
  simp only [CollatzResearch.WordTrace]
  refine ⟨84576392420112136506938885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56384261613408091004625923 84576392420112136506938885)
  ·
    refine ⟨15858073578771025595051041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84576392420112136506938885 15858073578771025595051041)
    ·
      refine ⟨11893555184078269196288281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15858073578771025595051041 11893555184078269196288281)
      ·
        refine ⟨8920166388058701897216211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11893555184078269196288281 8920166388058701897216211)
        ·
          refine ⟨13380249582088052845824317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8920166388058701897216211 13380249582088052845824317)
          ·
            refine ⟨5017593593283019817184119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13380249582088052845824317 5017593593283019817184119)
            ·
              refine ⟨7526390389924529725776179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017593593283019817184119 7526390389924529725776179)
              ·
                refine ⟨11289585584886794588664269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526390389924529725776179 11289585584886794588664269)
                ·
                  refine ⟨4233594594332547970749101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11289585584886794588664269 4233594594332547970749101)
                  ·
                    refine ⟨1587597972874705489030913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4233594594332547970749101 1587597972874705489030913)
                    ·
                      refine ⟨1190698479656029116773185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1587597972874705489030913 1190698479656029116773185)
                      ·
                        rfl

theorem cell23_2318877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_2318877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318877 prefixEnd_2318877 := by exact prefixLift 2318877
  have htrace : WordTrace (prefixWord ++ tailWord_2318877) baseStart_2318877 baseEnd_2318877 := by
    simpa [prefixWord, tailWord_2318877, baseEnd_2318877] using wordTrace_append hprefix tailTrace_2318877
  have hstable : (prefixWord ++ tailWord_2318877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318877).length < 2 ^ (prefixWord ++ tailWord_2318877).sum := by decide
  have hdescent : baseEnd_2318877 < baseStart_2318877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318903 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_2318903 : Nat := 118140960795 + 2318903 * 2 ^ 59
def prefixEnd_2318903 : Nat := 4983230072969 + 3 ^ 40 * 2318903 * 2
def baseEnd_2318903 : Nat := 1190711830153046015048065

theorem tailTrace_2318903 : CollatzResearch.WordTrace tailWord_2318903 prefixEnd_2318903 1190711830153046015048065 := by
  unfold tailWord_2318903
  simp only [CollatzResearch.WordTrace]
  refine ⟨84577340718017942947385363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56384893812011961964923575 84577340718017942947385363)
  ·
    refine ⟨126866011077026914421078045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84577340718017942947385363 126866011077026914421078045)
    ·
      refine ⟨47574754153885092907904267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126866011077026914421078045 47574754153885092907904267)
      ·
        refine ⟨71362131230827639361856401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47574754153885092907904267 71362131230827639361856401)
        ·
          refine ⟨53521598423120729521392301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71362131230827639361856401 53521598423120729521392301)
          ·
            refine ⟨20070599408670273570522113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53521598423120729521392301 20070599408670273570522113)
            ·
              refine ⟨15052949556502705177891585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20070599408670273570522113 15052949556502705177891585)
              ·
                refine ⟨11289712167377028883418689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15052949556502705177891585 11289712167377028883418689)
                ·
                  refine ⟨8467284125532771662564017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11289712167377028883418689 8467284125532771662564017)
                  ·
                    refine ⟨6350463094149578746923013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8467284125532771662564017 6350463094149578746923013)
                    ·
                      refine ⟨1190711830153046015048065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6350463094149578746923013 1190711830153046015048065)
                      ·
                        rfl

theorem cell23_2318903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_2318903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318903 prefixEnd_2318903 := by exact prefixLift 2318903
  have htrace : WordTrace (prefixWord ++ tailWord_2318903) baseStart_2318903 baseEnd_2318903 := by
    simpa [prefixWord, tailWord_2318903, baseEnd_2318903] using wordTrace_append hprefix tailTrace_2318903
  have hstable : (prefixWord ++ tailWord_2318903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318903).length < 2 ^ (prefixWord ++ tailWord_2318903).sum := by decide
  have hdescent : baseEnd_2318903 < baseStart_2318903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318923 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 3]
def baseStart_2318923 : Nat := 118140960795 + 2318923 * 2 ^ 59
def prefixEnd_2318923 : Nat := 4983230072969 + 3 ^ 40 * 2318923 * 2
def baseEnd_2318923 : Nat := 1190722099766135936797973

theorem tailTrace_2318923 : CollatzResearch.WordTrace tailWord_2318923 prefixEnd_2318923 1190722099766135936797973 := by
  unfold tailWord_2318923
  simp only [CollatzResearch.WordTrace]
  refine ⟨84578070177945486363113423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56385380118630324242075615 84578070177945486363113423)
  ·
    refine ⟨126867105266918229544670135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84578070177945486363113423 126867105266918229544670135)
    ·
      refine ⟨190300657900377344317005203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126867105266918229544670135 190300657900377344317005203)
      ·
        refine ⟨285450986850566016475507805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190300657900377344317005203 285450986850566016475507805)
        ·
          refine ⟨107044120068962256178315427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285450986850566016475507805 107044120068962256178315427)
          ·
            refine ⟨160566180103443384267473141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107044120068962256178315427 160566180103443384267473141)
            ·
              refine ⟨15053079384697817275075607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160566180103443384267473141 15053079384697817275075607)
              ·
                refine ⟨22579619077046725912613411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15053079384697817275075607 22579619077046725912613411)
                ·
                  refine ⟨33869428615570088868920117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22579619077046725912613411 33869428615570088868920117)
                  ·
                    refine ⟨3175258932709695831461261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33869428615570088868920117 3175258932709695831461261)
                    ·
                      refine ⟨1190722099766135936797973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175258932709695831461261 1190722099766135936797973)
                      ·
                        rfl

theorem cell23_2318923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 3].length) (baseStart_2318923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318923 prefixEnd_2318923 := by exact prefixLift 2318923
  have htrace : WordTrace (prefixWord ++ tailWord_2318923) baseStart_2318923 baseEnd_2318923 := by
    simpa [prefixWord, tailWord_2318923, baseEnd_2318923] using wordTrace_append hprefix tailTrace_2318923
  have hstable : (prefixWord ++ tailWord_2318923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318923).length < 2 ^ (prefixWord ++ tailWord_2318923).sum := by decide
  have hdescent : baseEnd_2318923 < baseStart_2318923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318980 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2318980 : Nat := 118140960795 + 2318980 * 2 ^ 59
def prefixEnd_2318980 : Nat := 4983230072969 + 3 ^ 40 * 2318980 * 2
def baseEnd_2318980 : Nat := 1190751368163442213785211

theorem tailTrace_2318980 : CollatzResearch.WordTrace tailWord_2318980 prefixEnd_2318980 1190751368163442213785211 := by
  unfold tailWord_2318980
  simp only [CollatzResearch.WordTrace]
  refine ⟨42290074569369492548969197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56386766092492656731958929 42290074569369492548969197)
  ·
    refine ⟨15858777963513559705863449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42290074569369492548969197 15858777963513559705863449)
    ·
      refine ⟨11894083472635169779397587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15858777963513559705863449 11894083472635169779397587)
      ·
        refine ⟨17841125208952754669096381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11894083472635169779397587 17841125208952754669096381)
        ·
          refine ⟨6690421953357283000911143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17841125208952754669096381 6690421953357283000911143)
          ·
            refine ⟨10035632930035924501366715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6690421953357283000911143 10035632930035924501366715)
            ·
              refine ⟨15053449395053886752050073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10035632930035924501366715 15053449395053886752050073)
              ·
                refine ⟨11290087046290415064037555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15053449395053886752050073 11290087046290415064037555)
                ·
                  refine ⟨16935130569435622596056333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11290087046290415064037555 16935130569435622596056333)
                  ·
                    refine ⟨6350673963538358473521125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16935130569435622596056333 6350673963538358473521125)
                    ·
                      refine ⟨1190751368163442213785211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6350673963538358473521125 1190751368163442213785211)
                      ·
                        rfl

theorem cell23_2318980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2318980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2318980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2318980 prefixEnd_2318980 := by exact prefixLift 2318980
  have htrace : WordTrace (prefixWord ++ tailWord_2318980) baseStart_2318980 baseEnd_2318980 := by
    simpa [prefixWord, tailWord_2318980, baseEnd_2318980] using wordTrace_append hprefix tailTrace_2318980
  have hstable : (prefixWord ++ tailWord_2318980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318980).length < 2 ^ (prefixWord ++ tailWord_2318980).sum := by decide
  have hdescent : baseEnd_2318980 < baseStart_2318980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319000 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2319000 : Nat := 118140960795 + 2319000 * 2 ^ 59
def prefixEnd_2319000 : Nat := 4983230072969 + 3 ^ 40 * 2319000 * 2
def baseEnd_2319000 : Nat := 1190761637776532135535119

theorem tailTrace_2319000 : CollatzResearch.WordTrace tailWord_2319000 prefixEnd_2319000 1190761637776532135535119 := by
  unfold tailWord_2319000
  simp only [CollatzResearch.WordTrace]
  refine ⟨42290439299333264256833227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56387252399111019009110969 42290439299333264256833227)
  ·
    refine ⟨63435658948999896385249841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42290439299333264256833227 63435658948999896385249841)
    ·
      refine ⟨47576744211749922288937381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63435658948999896385249841 47576744211749922288937381)
      ·
        refine ⟨8920639539703110429175759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47576744211749922288937381 8920639539703110429175759)
        ·
          refine ⟨13380959309554665643763639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8920639539703110429175759 13380959309554665643763639)
          ·
            refine ⟨20071438964331998465645459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13380959309554665643763639 20071438964331998465645459)
            ·
              refine ⟨30107158446497997698468189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20071438964331998465645459 30107158446497997698468189)
              ·
                refine ⟨11290184417436749136925571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30107158446497997698468189 11290184417436749136925571)
                ·
                  refine ⟨16935276626155123705388357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11290184417436749136925571 16935276626155123705388357)
                  ·
                    refine ⟨3175364367404085694760317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16935276626155123705388357 3175364367404085694760317)
                    ·
                      refine ⟨1190761637776532135535119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175364367404085694760317 1190761637776532135535119)
                      ·
                        rfl

theorem cell23_2319000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2319000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319000 prefixEnd_2319000 := by exact prefixLift 2319000
  have htrace : WordTrace (prefixWord ++ tailWord_2319000) baseStart_2319000 baseEnd_2319000 := by
    simpa [prefixWord, tailWord_2319000, baseEnd_2319000] using wordTrace_append hprefix tailTrace_2319000
  have hstable : (prefixWord ++ tailWord_2319000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319000).length < 2 ^ (prefixWord ++ tailWord_2319000).sum := by decide
  have hdescent : baseEnd_2319000 < baseStart_2319000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319033 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 2, 9]
def baseStart_2319033 : Nat := 118140960795 + 2319033 * 2 ^ 59
def prefixEnd_2319033 : Nat := 4983230072969 + 3 ^ 40 * 2319033 * 2
def baseEnd_2319033 : Nat := 396926194212710168807489

theorem tailTrace_2319033 : CollatzResearch.WordTrace tailWord_2319033 prefixEnd_2319033 396926194212710168807489 := by
  unfold tailWord_2319033
  simp only [CollatzResearch.WordTrace]
  refine ⟨84582082207546975149617753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56388054805031316766411835 84582082207546975149617753)
  ·
    refine ⟨63436561655660231362213315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84582082207546975149617753 63436561655660231362213315)
    ·
      refine ⟨95154842483490347043319973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63436561655660231362213315 95154842483490347043319973)
      ·
        refine ⟨17841532965654440070622495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95154842483490347043319973 17841532965654440070622495)
        ·
          refine ⟨26762299448481660105933743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17841532965654440070622495 26762299448481660105933743)
          ·
            refine ⟨40143449172722490158900615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26762299448481660105933743 40143449172722490158900615)
            ·
              refine ⟨60215173759083735238350923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40143449172722490158900615 60215173759083735238350923)
              ·
                refine ⟨90322760638625602857526385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60215173759083735238350923 90322760638625602857526385)
                ·
                  refine ⟨67742070478969202143144789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90322760638625602857526385 67742070478969202143144789)
                  ·
                    refine ⟨396926194212710168807489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 67742070478969202143144789 396926194212710168807489)
                    ·
                      rfl

theorem cell23_2319033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_2319033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319033 prefixEnd_2319033 := by exact prefixLift 2319033
  have htrace : WordTrace (prefixWord ++ tailWord_2319033) baseStart_2319033 baseEnd_2319033 := by
    simpa [prefixWord, tailWord_2319033, baseEnd_2319033] using wordTrace_append hprefix tailTrace_2319033
  have hstable : (prefixWord ++ tailWord_2319033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319033).length < 2 ^ (prefixWord ++ tailWord_2319033).sum := by decide
  have hdescent : baseEnd_2319033 < baseStart_2319033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319037 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 6]
def baseStart_2319037 : Nat := 118140960795 + 2319037 * 2 ^ 59
def prefixEnd_2319037 : Nat := 4983230072969 + 3 ^ 40 * 2319037 * 2
def baseEnd_2319037 : Nat := 132308959617860943419161

theorem tailTrace_2319037 : CollatzResearch.WordTrace tailWord_2319037 prefixEnd_2319037 132308959617860943419161 := by
  unfold tailWord_2319037
  simp only [CollatzResearch.WordTrace]
  refine ⟨84582228099532483832763365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56388152066354989221842243 84582228099532483832763365)
  ·
    refine ⟨15859167768662340718643131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84582228099532483832763365 15859167768662340718643131)
    ·
      refine ⟨23788751652993511077964697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15859167768662340718643131 23788751652993511077964697)
      ·
        refine ⟨17841563739745133308473523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23788751652993511077964697 17841563739745133308473523)
        ·
          refine ⟨26762345609617699962710285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17841563739745133308473523 26762345609617699962710285)
          ·
            refine ⟨10035879603606637486016357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26762345609617699962710285 10035879603606637486016357)
            ·
              refine ⟨1881727425676244528628067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10035879603606637486016357 1881727425676244528628067)
              ·
                refine ⟨2822591138514366792942101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881727425676244528628067 2822591138514366792942101)
                ·
                  refine ⟨132308959617860943419161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2822591138514366792942101 132308959617860943419161)
                  ·
                    rfl

theorem cell23_2319037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_2319037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319037 prefixEnd_2319037 := by exact prefixLift 2319037
  have htrace : WordTrace (prefixWord ++ tailWord_2319037) baseStart_2319037 baseEnd_2319037 := by
    simpa [prefixWord, tailWord_2319037, baseEnd_2319037] using wordTrace_append hprefix tailTrace_2319037
  have hstable : (prefixWord ++ tailWord_2319037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319037).length < 2 ^ (prefixWord ++ tailWord_2319037).sum := by decide
  have hdescent : baseEnd_2319037 < baseStart_2319037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319081 : List Nat := [1, 2, 1, 1, 1, 2, 8, 2, 1, 1, 3]
def baseStart_2319081 : Nat := 118140960795 + 2319081 * 2 ^ 59
def prefixEnd_2319081 : Nat := 4983230072969 + 3 ^ 40 * 2319081 * 2
def baseEnd_2319081 : Nat := 1190803229709546318622247

theorem tailTrace_2319081 : CollatzResearch.WordTrace tailWord_2319081 prefixEnd_2319081 1190803229709546318622247 := by
  unfold tailWord_2319081
  simp only [CollatzResearch.WordTrace]
  refine ⟨84583832911373079347365097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56389221940915386231576731 84583832911373079347365097)
  ·
    refine ⟨63437874683529809510523823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84583832911373079347365097 63437874683529809510523823)
    ·
      refine ⟨95156812025294714265785735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63437874683529809510523823 95156812025294714265785735)
      ·
        refine ⟨142735218037942071398678603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95156812025294714265785735 142735218037942071398678603)
        ·
          refine ⟨214102827056913107098017905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142735218037942071398678603 214102827056913107098017905)
          ·
            refine ⟨160577120292684830323513429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214102827056913107098017905 160577120292684830323513429)
            ·
              refine ⟨1881763128429900355353673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 160577120292684830323513429 1881763128429900355353673)
              ·
                refine ⟨1411322346322425266515255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881763128429900355353673 1411322346322425266515255)
                ·
                  refine ⟨2116983519483637899772883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411322346322425266515255 2116983519483637899772883)
                  ·
                    refine ⟨3175475279225456849659325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2116983519483637899772883 3175475279225456849659325)
                    ·
                      refine ⟨1190803229709546318622247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175475279225456849659325 1190803229709546318622247)
                      ·
                        rfl

theorem cell23_2319081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 1, 3].length) (baseStart_2319081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319081 prefixEnd_2319081 := by exact prefixLift 2319081
  have htrace : WordTrace (prefixWord ++ tailWord_2319081) baseStart_2319081 baseEnd_2319081 := by
    simpa [prefixWord, tailWord_2319081, baseEnd_2319081] using wordTrace_append hprefix tailTrace_2319081
  have hstable : (prefixWord ++ tailWord_2319081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319081).length < 2 ^ (prefixWord ++ tailWord_2319081).sum := by decide
  have hdescent : baseEnd_2319081 < baseStart_2319081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319107 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 3]
def baseStart_2319107 : Nat := 118140960795 + 2319107 * 2 ^ 59
def prefixEnd_2319107 : Nat := 4983230072969 + 3 ^ 40 * 2319107 * 2
def baseEnd_2319107 : Nat := 1190816580206563216897127

theorem tailTrace_2319107 : CollatzResearch.WordTrace tailWord_2319107 prefixEnd_2319107 1190816580206563216897127 := by
  unfold tailWord_2319107
  simp only [CollatzResearch.WordTrace]
  refine ⟨84584781209278885787811575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56389854139519257191874383 84584781209278885787811575)
  ·
    refine ⟨126877171813918328681717363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84584781209278885787811575 126877171813918328681717363)
    ·
      refine ⟨190315757720877493022576045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126877171813918328681717363 190315757720877493022576045)
      ·
        refine ⟨71368409145329059883466017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190315757720877493022576045 71368409145329059883466017)
        ·
          refine ⟨53526306858996794912599513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71368409145329059883466017 53526306858996794912599513)
          ·
            refine ⟨40144730144247596184449635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53526306858996794912599513 40144730144247596184449635)
            ·
              refine ⟨60217095216371394276674453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40144730144247596184449635 60217095216371394276674453)
              ·
                refine ⟨2822676338267409106719115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60217095216371394276674453 2822676338267409106719115)
                ·
                  refine ⟨4234014507401113660078673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822676338267409106719115 4234014507401113660078673)
                  ·
                    refine ⟨3175510880550835245059005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4234014507401113660078673 3175510880550835245059005)
                    ·
                      refine ⟨1190816580206563216897127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175510880550835245059005 1190816580206563216897127)
                      ·
                        rfl

theorem cell23_2319107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_2319107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319107 prefixEnd_2319107 := by exact prefixLift 2319107
  have htrace : WordTrace (prefixWord ++ tailWord_2319107) baseStart_2319107 baseEnd_2319107 := by
    simpa [prefixWord, tailWord_2319107, baseEnd_2319107] using wordTrace_append hprefix tailTrace_2319107
  have hstable : (prefixWord ++ tailWord_2319107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319107).length < 2 ^ (prefixWord ++ tailWord_2319107).sum := by decide
  have hdescent : baseEnd_2319107 < baseStart_2319107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319121 : List Nat := [1, 2, 2, 1, 1, 3, 3, 5, 1, 2, 2]
def baseStart_2319121 : Nat := 118140960795 + 2319121 * 2 ^ 59
def prefixEnd_2319121 : Nat := 4983230072969 + 3 ^ 40 * 2319121 * 2
def baseEnd_2319121 : Nat := 1190823768935726162122063

theorem tailTrace_2319121 : CollatzResearch.WordTrace tailWord_2319121 prefixEnd_2319121 1190823768935726162122063 := by
  unfold tailWord_2319121
  simp only [CollatzResearch.WordTrace]
  refine ⟨84585291831228166178821217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56390194554152110785880811 84585291831228166178821217)
  ·
    refine ⟨63438968873421124634115913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84585291831228166178821217 63438968873421124634115913)
    ·
      refine ⟨47579226655065843475586935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63438968873421124634115913 47579226655065843475586935)
      ·
        refine ⟨71368839982598765213380403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47579226655065843475586935 71368839982598765213380403)
        ·
          refine ⟨107053259973898147820070605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71368839982598765213380403 107053259973898147820070605)
          ·
            refine ⟨40144972490211805432526477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107053259973898147820070605 40144972490211805432526477)
            ·
              refine ⟨15054364683829427037197429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40144972490211805432526477 15054364683829427037197429)
              ·
                refine ⟨1411346689109008784737259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15054364683829427037197429 1411346689109008784737259)
                ·
                  refine ⟨2117020033663513177105889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411346689109008784737259 2117020033663513177105889)
                  ·
                    refine ⟨1587765025247634882829417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2117020033663513177105889 1587765025247634882829417)
                    ·
                      refine ⟨1190823768935726162122063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1587765025247634882829417 1190823768935726162122063)
                      ·
                        rfl

theorem cell23_2319121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_2319121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319121 prefixEnd_2319121 := by exact prefixLift 2319121
  have htrace : WordTrace (prefixWord ++ tailWord_2319121) baseStart_2319121 baseEnd_2319121 := by
    simpa [prefixWord, tailWord_2319121, baseEnd_2319121] using wordTrace_append hprefix tailTrace_2319121
  have hstable : (prefixWord ++ tailWord_2319121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319121).length < 2 ^ (prefixWord ++ tailWord_2319121).sum := by decide
  have hdescent : baseEnd_2319121 < baseStart_2319121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319138 : List Nat := [3, 3, 1, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_2319138 : Nat := 118140960795 + 2319138 * 2 ^ 59
def prefixEnd_2319138 : Nat := 4983230072969 + 3 ^ 40 * 2319138 * 2
def baseEnd_2319138 : Nat := 1190832498106852595609485

theorem tailTrace_2319138 : CollatzResearch.WordTrace tailWord_2319138 prefixEnd_2319138 1190832498106852595609485 := by
  unfold tailWord_2319138
  simp only [CollatzResearch.WordTrace]
  refine ⟨21146477968041644520547517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56390607914777718721460045 21146477968041644520547517)
  ·
    refine ⟨7929929238015616695205319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21146477968041644520547517 7929929238015616695205319)
    ·
      refine ⟨11894893857023425042807979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7929929238015616695205319 11894893857023425042807979)
      ·
        refine ⟨17842340785535137564211969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11894893857023425042807979 17842340785535137564211969)
        ·
          refine ⟨13381755589151353173158977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17842340785535137564211969 13381755589151353173158977)
          ·
            refine ⟨10036316691863514879869233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13381755589151353173158977 10036316691863514879869233)
            ·
              refine ⟨7527237518897636159901925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10036316691863514879869233 7527237518897636159901925)
              ·
                refine ⟨1411357034793306779981611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7527237518897636159901925 1411357034793306779981611)
                ·
                  refine ⟨2117035552189960169972417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411357034793306779981611 2117035552189960169972417)
                  ·
                    refine ⟨1587776664142470127479313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2117035552189960169972417 1587776664142470127479313)
                    ·
                      refine ⟨1190832498106852595609485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1587776664142470127479313 1190832498106852595609485)
                      ·
                        rfl

theorem cell23_2319138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_2319138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319138 prefixEnd_2319138 := by exact prefixLift 2319138
  have htrace : WordTrace (prefixWord ++ tailWord_2319138) baseStart_2319138 baseEnd_2319138 := by
    simpa [prefixWord, tailWord_2319138, baseEnd_2319138] using wordTrace_append hprefix tailTrace_2319138
  have hstable : (prefixWord ++ tailWord_2319138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319138).length < 2 ^ (prefixWord ++ tailWord_2319138).sum := by decide
  have hdescent : baseEnd_2319138 < baseStart_2319138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319158 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2319158 : Nat := 118140960795 + 2319158 * 2 ^ 59
def prefixEnd_2319158 : Nat := 4983230072969 + 3 ^ 40 * 2319158 * 2
def baseEnd_2319158 : Nat := 1190842767719942517359393

theorem tailTrace_2319158 : CollatzResearch.WordTrace tailWord_2319158 prefixEnd_2319158 1190842767719942517359393 := by
  unfold tailWord_2319158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5286665083255882593619883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56391094221396080998612085 5286665083255882593619883)
  ·
    refine ⟨7929997624883823890429825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5286665083255882593619883 7929997624883823890429825)
    ·
      refine ⟨5947498218662867917822369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7929997624883823890429825 5947498218662867917822369)
      ·
        refine ⟨4460623663997150938366777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5947498218662867917822369 4460623663997150938366777)
        ·
          refine ⟨3345467747997863203775083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4460623663997150938366777 3345467747997863203775083)
          ·
            refine ⟨5018201621996794805662625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345467747997863203775083 5018201621996794805662625)
            ·
              refine ⟨3763651216497596104246969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5018201621996794805662625 3763651216497596104246969)
              ·
                refine ⟨2822738412373197078185227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3763651216497596104246969 2822738412373197078185227)
                ·
                  refine ⟨4234107618559795617277841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822738412373197078185227 4234107618559795617277841)
                  ·
                    refine ⟨3175580713919846712958381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4234107618559795617277841 3175580713919846712958381)
                    ·
                      refine ⟨1190842767719942517359393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175580713919846712958381 1190842767719942517359393)
                      ·
                        rfl

theorem cell23_2319158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2319158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319158 prefixEnd_2319158 := by exact prefixLift 2319158
  have htrace : WordTrace (prefixWord ++ tailWord_2319158) baseStart_2319158 baseEnd_2319158 := by
    simpa [prefixWord, tailWord_2319158, baseEnd_2319158] using wordTrace_append hprefix tailTrace_2319158
  have hstable : (prefixWord ++ tailWord_2319158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319158).length < 2 ^ (prefixWord ++ tailWord_2319158).sum := by decide
  have hdescent : baseEnd_2319158 < baseStart_2319158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319267 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 4]
def baseStart_2319267 : Nat := 118140960795 + 2319267 * 2 ^ 59
def prefixEnd_2319267 : Nat := 4983230072969 + 3 ^ 40 * 2319267 * 2
def baseEnd_2319267 : Nat := 1190898737111282590896391

theorem tailTrace_2319267 : CollatzResearch.WordTrace tailWord_2319267 prefixEnd_2319267 1190898737111282590896391 := by
  unfold tailWord_2319267
  simp only [CollatzResearch.WordTrace]
  refine ⟨84590616888699233113636055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56393744592466155409090703 84590616888699233113636055)
  ·
    refine ⟨126885925333048849670454083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84590616888699233113636055 126885925333048849670454083)
    ·
      refine ⟨190328887999573274505681125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126885925333048849670454083 190328887999573274505681125)
      ·
        refine ⟨35686666499919988969815211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190328887999573274505681125 35686666499919988969815211)
        ·
          refine ⟨53529999749879983454722817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35686666499919988969815211 53529999749879983454722817)
          ·
            refine ⟨40147499812409987591042113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53529999749879983454722817 40147499812409987591042113)
            ·
              refine ⟨30110624859307490693281585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40147499812409987591042113 30110624859307490693281585)
              ·
                refine ⟨22582968644480618019961189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30110624859307490693281585 22582968644480618019961189)
                ·
                  refine ⟨4234306620840115878742723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22582968644480618019961189 4234306620840115878742723)
                  ·
                    refine ⟨6351459931260173818114085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4234306620840115878742723 6351459931260173818114085)
                    ·
                      refine ⟨1190898737111282590896391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6351459931260173818114085 1190898737111282590896391)
                      ·
                        rfl

theorem cell23_2319267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_2319267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319267 prefixEnd_2319267 := by exact prefixLift 2319267
  have htrace : WordTrace (prefixWord ++ tailWord_2319267) baseStart_2319267 baseEnd_2319267 := by
    simpa [prefixWord, tailWord_2319267, baseEnd_2319267] using wordTrace_append hprefix tailTrace_2319267
  have hstable : (prefixWord ++ tailWord_2319267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319267).length < 2 ^ (prefixWord ++ tailWord_2319267).sum := by decide
  have hdescent : baseEnd_2319267 < baseStart_2319267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319281 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 2, 5]
def baseStart_2319281 : Nat := 118140960795 + 2319281 * 2 ^ 59
def prefixEnd_2319281 : Nat := 4983230072969 + 3 ^ 40 * 2319281 * 2
def baseEnd_2319281 : Nat := 396968641946815178707109

theorem tailTrace_2319281 : CollatzResearch.WordTrace tailWord_2319281 prefixEnd_2319281 396968641946815178707109 := by
  unfold tailWord_2319281
  simp only [CollatzResearch.WordTrace]
  refine ⟨84591127510648513504645697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56394085007099009003097131 84591127510648513504645697)
  ·
    refine ⟨63443345632986385128484273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84591127510648513504645697 63443345632986385128484273)
    ·
      refine ⟨47582509224739788846363205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63443345632986385128484273 47582509224739788846363205)
      ·
        refine ⟨8921720479638710408693101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47582509224739788846363205 8921720479638710408693101)
        ·
          refine ⟨3345645179864516403259913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8921720479638710408693101 3345645179864516403259913)
          ·
            refine ⟨2509233884898387302444935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3345645179864516403259913 2509233884898387302444935)
            ·
              refine ⟨3763850827347580953667403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509233884898387302444935 3763850827347580953667403)
              ·
                refine ⟨5645776241021371430501105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763850827347580953667403 5645776241021371430501105)
                ·
                  refine ⟨4234332180766028572875829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5645776241021371430501105 4234332180766028572875829)
                  ·
                    refine ⟨396968641946815178707109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4234332180766028572875829 396968641946815178707109)
                    ·
                      rfl

theorem cell23_2319281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_2319281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319281 prefixEnd_2319281 := by exact prefixLift 2319281
  have htrace : WordTrace (prefixWord ++ tailWord_2319281) baseStart_2319281 baseEnd_2319281 := by
    simpa [prefixWord, tailWord_2319281, baseEnd_2319281] using wordTrace_append hprefix tailTrace_2319281
  have hstable : (prefixWord ++ tailWord_2319281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319281).length < 2 ^ (prefixWord ++ tailWord_2319281).sum := by decide
  have hdescent : baseEnd_2319281 < baseStart_2319281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319294 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2319294 : Nat := 118140960795 + 2319294 * 2 ^ 59
def prefixEnd_2319294 : Nat := 4983230072969 + 3 ^ 40 * 2319294 * 2
def baseEnd_2319294 : Nat := 396970867029651328419589

theorem tailTrace_2319294 : CollatzResearch.WordTrace tailWord_2319294 prefixEnd_2319294 396970867029651328419589 := by
  unfold tailWord_2319294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10573950207450177090608617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56394401106400944483245957 10573950207450177090608617)
  ·
    refine ⟨7930462655587632817956463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10573950207450177090608617 7930462655587632817956463)
    ·
      refine ⟨11895693983381449226934695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7930462655587632817956463 11895693983381449226934695)
      ·
        refine ⟨17843540975072173840402043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11895693983381449226934695 17843540975072173840402043)
        ·
          refine ⟨26765311462608260760603065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17843540975072173840402043 26765311462608260760603065)
          ·
            refine ⟨20073983596956195570452299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26765311462608260760603065 20073983596956195570452299)
            ·
              refine ⟨30110975395434293355678449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20073983596956195570452299 30110975395434293355678449)
              ·
                refine ⟨22583231546575720016758837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30110975395434293355678449 22583231546575720016758837)
                ·
                  refine ⟨2117177957491473751571141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22583231546575720016758837 2117177957491473751571141)
                  ·
                    refine ⟨396970867029651328419589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2117177957491473751571141 396970867029651328419589)
                    ·
                      rfl

theorem cell23_2319294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2319294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319294 prefixEnd_2319294 := by exact prefixLift 2319294
  have htrace : WordTrace (prefixWord ++ tailWord_2319294) baseStart_2319294 baseEnd_2319294 := by
    simpa [prefixWord, tailWord_2319294, baseEnd_2319294] using wordTrace_append hprefix tailTrace_2319294
  have hstable : (prefixWord ++ tailWord_2319294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319294).length < 2 ^ (prefixWord ++ tailWord_2319294).sum := by decide
  have hdescent : baseEnd_2319294 < baseStart_2319294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319307 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 8]
def baseStart_2319307 : Nat := 118140960795 + 2319307 * 2 ^ 59
def prefixEnd_2319307 : Nat := 4983230072969 + 3 ^ 40 * 2319307 * 2
def baseEnd_2319307 : Nat := 132324364037495826044023

theorem tailTrace_2319307 : CollatzResearch.WordTrace tailWord_2319307 prefixEnd_2319307 132324364037495826044023 := by
  unfold tailWord_2319307
  simp only [CollatzResearch.WordTrace]
  refine ⟨84592075808554319945092175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56394717205702879963394783 84592075808554319945092175)
  ·
    refine ⟨126888113712831479917638263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84592075808554319945092175 126888113712831479917638263)
    ·
      refine ⟨190332170569247219876457395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126888113712831479917638263 190332170569247219876457395)
      ·
        refine ⟨285498255853870829814686093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190332170569247219876457395 285498255853870829814686093)
        ·
          refine ⟨107061845945201561180507285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285498255853870829814686093 107061845945201561180507285)
          ·
            refine ⟨5018524028681323180336279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107061845945201561180507285 5018524028681323180336279)
            ·
              refine ⟨7527786043021984770504419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5018524028681323180336279 7527786043021984770504419)
              ·
                refine ⟨11291679064532977155756629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7527786043021984770504419 11291679064532977155756629)
                ·
                  refine ⟨132324364037495826044023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11291679064532977155756629 132324364037495826044023)
                  ·
                    rfl

theorem cell23_2319307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 8].length) (baseStart_2319307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319307 prefixEnd_2319307 := by exact prefixLift 2319307
  have htrace : WordTrace (prefixWord ++ tailWord_2319307) baseStart_2319307 baseEnd_2319307 := by
    simpa [prefixWord, tailWord_2319307, baseEnd_2319307] using wordTrace_append hprefix tailTrace_2319307
  have hstable : (prefixWord ++ tailWord_2319307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319307).length < 2 ^ (prefixWord ++ tailWord_2319307).sum := by decide
  have hdescent : baseEnd_2319307 < baseStart_2319307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319311 : List Nat := [1, 1, 2, 1, 1, 6, 2, 4, 1, 4]
def baseStart_2319311 : Nat := 118140960795 + 2319311 * 2 ^ 59
def prefixEnd_2319311 : Nat := 4983230072969 + 3 ^ 40 * 2319311 * 2
def baseEnd_2319311 : Nat := 396973776753360139582063

theorem tailTrace_2319311 : CollatzResearch.WordTrace tailWord_2319311 prefixEnd_2319311 396973776753360139582063 := by
  unfold tailWord_2319311
  simp only [CollatzResearch.WordTrace]
  refine ⟨84592221700539828628237787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56394814467026552418825191 84592221700539828628237787)
  ·
    refine ⟨126888332550809742942356681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84592221700539828628237787 126888332550809742942356681)
    ·
      refine ⟨95166249413107307206767511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126888332550809742942356681 95166249413107307206767511)
      ·
        refine ⟨142749374119660960810151267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95166249413107307206767511 142749374119660960810151267)
        ·
          refine ⟨214124061179491441215226901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142749374119660960810151267 214124061179491441215226901)
          ·
            refine ⟨10037065367788661306963761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 214124061179491441215226901 10037065367788661306963761)
            ·
              refine ⟨7527799025841495980222821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10037065367788661306963761 7527799025841495980222821)
              ·
                refine ⟨1411462317345280496291779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7527799025841495980222821 1411462317345280496291779)
                ·
                  refine ⟨2117193476017920744437669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411462317345280496291779 2117193476017920744437669)
                  ·
                    refine ⟨396973776753360139582063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2117193476017920744437669 396973776753360139582063)
                    ·
                      rfl

theorem cell23_2319311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 4].length) (baseStart_2319311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319311 prefixEnd_2319311 := by exact prefixLift 2319311
  have htrace : WordTrace (prefixWord ++ tailWord_2319311) baseStart_2319311 baseEnd_2319311 := by
    simpa [prefixWord, tailWord_2319311, baseEnd_2319311] using wordTrace_append hprefix tailTrace_2319311
  have hstable : (prefixWord ++ tailWord_2319311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319311).length < 2 ^ (prefixWord ++ tailWord_2319311).sum := by decide
  have hdescent : baseEnd_2319311 < baseStart_2319311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319318 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_2319318 : Nat := 118140960795 + 2319318 * 2 ^ 59
def prefixEnd_2319318 : Nat := 4983230072969 + 3 ^ 40 * 2319318 * 2
def baseEnd_2319318 : Nat := 1190924924624661891358657

theorem tailTrace_2319318 : CollatzResearch.WordTrace tailWord_2319318 prefixEnd_2319318 1190924924624661891358657 := by
  unfold tailWord_2319318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287029813219654301483913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56394984674342979215828405 5287029813219654301483913)
  ·
    refine ⟨3965272359914740726112935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5287029813219654301483913 3965272359914740726112935)
    ·
      refine ⟨5947908539872111089169403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3965272359914740726112935 5947908539872111089169403)
      ·
        refine ⟨8921862809808166633754105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5947908539872111089169403 8921862809808166633754105)
        ·
          refine ⟨6691397107356124975315579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8921862809808166633754105 6691397107356124975315579)
          ·
            refine ⟨10037095661034187462973369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6691397107356124975315579 10037095661034187462973369)
            ·
              refine ⟨7527821745775640597230027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10037095661034187462973369 7527821745775640597230027)
              ·
                refine ⟨11291732618663460895845041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7527821745775640597230027 11291732618663460895845041)
                ·
                  refine ⟨8468799463997595671883781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11291732618663460895845041 8468799463997595671883781)
                  ·
                    refine ⟨1587899899499549188478209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8468799463997595671883781 1587899899499549188478209)
                    ·
                      refine ⟨1190924924624661891358657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1587899899499549188478209 1190924924624661891358657)
                      ·
                        rfl

theorem cell23_2319318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_2319318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319318 prefixEnd_2319318 := by exact prefixLift 2319318
  have htrace : WordTrace (prefixWord ++ tailWord_2319318) baseStart_2319318 baseEnd_2319318 := by
    simpa [prefixWord, tailWord_2319318, baseEnd_2319318] using wordTrace_append hprefix tailTrace_2319318
  have hstable : (prefixWord ++ tailWord_2319318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319318).length < 2 ^ (prefixWord ++ tailWord_2319318).sum := by decide
  have hdescent : baseEnd_2319318 < baseStart_2319318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319361 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_2319361 : Nat := 118140960795 + 2319361 * 2 ^ 59
def prefixEnd_2319361 : Nat := 4983230072969 + 3 ^ 40 * 2319361 * 2
def baseEnd_2319361 : Nat := 1190947004292805223120959

theorem tailTrace_2319361 : CollatzResearch.WordTrace tailWord_2319361 prefixEnd_2319361 1190947004292805223120959 := by
  unfold tailWord_2319361
  simp only [CollatzResearch.WordTrace]
  refine ⟨84594045350358687167557937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56396030233572458111705291 84594045350358687167557937)
  ·
    refine ⟨63445534012769015375668453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84594045350358687167557937 63445534012769015375668453)
    ·
      refine ⟨11896037627394190382937835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63445534012769015375668453 11896037627394190382937835)
      ·
        refine ⟨17844056441091285574406753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11896037627394190382937835 17844056441091285574406753)
        ·
          refine ⟨13383042330818464180805065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17844056441091285574406753 13383042330818464180805065)
          ·
            refine ⟨10037281748113848135603799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13383042330818464180805065 10037281748113848135603799)
            ·
              refine ⟨15055922622170772203405699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10037281748113848135603799 15055922622170772203405699)
              ·
                refine ⟨22583883933256158305108549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15055922622170772203405699 22583883933256158305108549)
                ·
                  refine ⟨4234478237485529682207853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22583883933256158305108549 4234478237485529682207853)
                  ·
                    refine ⟨1587929339057073630827945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4234478237485529682207853 1587929339057073630827945)
                    ·
                      refine ⟨1190947004292805223120959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1587929339057073630827945 1190947004292805223120959)
                      ·
                        rfl

theorem cell23_2319361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_2319361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319361 prefixEnd_2319361 := by exact prefixLift 2319361
  have htrace : WordTrace (prefixWord ++ tailWord_2319361) baseStart_2319361 baseEnd_2319361 := by
    simpa [prefixWord, tailWord_2319361, baseEnd_2319361] using wordTrace_append hprefix tailTrace_2319361
  have hstable : (prefixWord ++ tailWord_2319361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319361).length < 2 ^ (prefixWord ++ tailWord_2319361).sum := by decide
  have hdescent : baseEnd_2319361 < baseStart_2319361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319362 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2319362 : Nat := 118140960795 + 2319362 * 2 ^ 59
def prefixEnd_2319362 : Nat := 4983230072969 + 3 ^ 40 * 2319362 * 2
def baseEnd_2319362 : Nat := 396982505924486573069485

theorem tailTrace_2319362 : CollatzResearch.WordTrace tailWord_2319362 prefixEnd_2319362 396982505924486573069485 := by
  unfold tailWord_2319362
  simp only [CollatzResearch.WordTrace]
  refine ⟨21148520455838766084586085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56396054548903376225562893 21148520455838766084586085)
  ·
    refine ⟨3965347585469768640859891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21148520455838766084586085 3965347585469768640859891)
    ·
      refine ⟨5948021378204652961289837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3965347585469768640859891 5948021378204652961289837)
      ·
        refine ⟨2230508016826744860483689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5948021378204652961289837 2230508016826744860483689)
        ·
          refine ⟨1672881012620058645362767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2230508016826744860483689 1672881012620058645362767)
          ·
            refine ⟨2509321518930087968044151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672881012620058645362767 2509321518930087968044151)
            ·
              refine ⟨3763982278395131952066227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509321518930087968044151 3763982278395131952066227)
              ·
                refine ⟨5645973417592697928099341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763982278395131952066227 5645973417592697928099341)
                ·
                  refine ⟨2117240031597261723037253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5645973417592697928099341 2117240031597261723037253)
                  ·
                    refine ⟨396982505924486573069485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2117240031597261723037253 396982505924486573069485)
                    ·
                      rfl

theorem cell23_2319362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2319362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319362 prefixEnd_2319362 := by exact prefixLift 2319362
  have htrace : WordTrace (prefixWord ++ tailWord_2319362) baseStart_2319362 baseEnd_2319362 := by
    simpa [prefixWord, tailWord_2319362, baseEnd_2319362] using wordTrace_append hprefix tailTrace_2319362
  have hstable : (prefixWord ++ tailWord_2319362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319362).length < 2 ^ (prefixWord ++ tailWord_2319362).sum := by decide
  have hdescent : baseEnd_2319362 < baseStart_2319362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319368 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_2319368 : Nat := 118140960795 + 2319368 * 2 ^ 59
def prefixEnd_2319368 : Nat := 4983230072969 + 3 ^ 40 * 2319368 * 2
def baseEnd_2319368 : Nat := 1190950598657386695733427

theorem tailTrace_2319368 : CollatzResearch.WordTrace tailWord_2319368 prefixEnd_2319368 1190950598657386695733427 := by
  unfold tailWord_2319368
  simp only [CollatzResearch.WordTrace]
  refine ⟨42297150330666663681531379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56396200440888884908708505 42297150330666663681531379)
  ·
    refine ⟨63445725495999995522297069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42297150330666663681531379 63445725495999995522297069)
    ·
      refine ⟨23792147060999998320861401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63445725495999995522297069 23792147060999998320861401)
      ·
        refine ⟨17844110295749998740646051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23792147060999998320861401 17844110295749998740646051)
        ·
          refine ⟨26766165443624998110969077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17844110295749998740646051 26766165443624998110969077)
          ·
            refine ⟨2509328010339843572903351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26766165443624998110969077 2509328010339843572903351)
            ·
              refine ⟨3763992015509765359355027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509328010339843572903351 3763992015509765359355027)
              ·
                refine ⟨5645988023264648039032541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763992015509765359355027 5645988023264648039032541)
                ·
                  refine ⟨2117245508724243014637203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5645988023264648039032541 2117245508724243014637203)
                  ·
                    refine ⟨3175868263086364521955805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2117245508724243014637203 3175868263086364521955805)
                    ·
                      refine ⟨1190950598657386695733427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175868263086364521955805 1190950598657386695733427)
                      ·
                        rfl

theorem cell23_2319368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_2319368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319368 prefixEnd_2319368 := by exact prefixLift 2319368
  have htrace : WordTrace (prefixWord ++ tailWord_2319368) baseStart_2319368 baseEnd_2319368 := by
    simpa [prefixWord, tailWord_2319368, baseEnd_2319368] using wordTrace_append hprefix tailTrace_2319368
  have hstable : (prefixWord ++ tailWord_2319368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319368).length < 2 ^ (prefixWord ++ tailWord_2319368).sum := by decide
  have hdescent : baseEnd_2319368 < baseStart_2319368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319388 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_2319388 : Nat := 118140960795 + 2319388 * 2 ^ 59
def prefixEnd_2319388 : Nat := 4983230072969 + 3 ^ 40 * 2319388 * 2
def baseEnd_2319388 : Nat := 396986956090158872494445

theorem tailTrace_2319388 : CollatzResearch.WordTrace tailWord_2319388 prefixEnd_2319388 396986956090158872494445 := by
  unfold tailWord_2319388
  simp only [CollatzResearch.WordTrace]
  refine ⟨42297515060630435389395409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56396686747507247185860545 42297515060630435389395409)
  ·
    refine ⟨31723136295472826542046557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42297515060630435389395409 31723136295472826542046557)
    ·
      refine ⟨11896176110802309953267459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31723136295472826542046557 11896176110802309953267459)
      ·
        refine ⟨17844264166203464929901189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11896176110802309953267459 17844264166203464929901189)
        ·
          refine ⟨3345799531163149674356473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17844264166203464929901189 3345799531163149674356473)
          ·
            refine ⟨2509349648372362255767355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3345799531163149674356473 2509349648372362255767355)
            ·
              refine ⟨3764024472558543383651033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509349648372362255767355 3764024472558543383651033)
              ·
                refine ⟨2823018354418907537738275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3764024472558543383651033 2823018354418907537738275)
                ·
                  refine ⟨4234527531628361306607413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823018354418907537738275 4234527531628361306607413)
                  ·
                    refine ⟨396986956090158872494445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4234527531628361306607413 396986956090158872494445)
                    ·
                      rfl

theorem cell23_2319388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_2319388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319388 prefixEnd_2319388 := by exact prefixLift 2319388
  have htrace : WordTrace (prefixWord ++ tailWord_2319388) baseStart_2319388 baseEnd_2319388 := by
    simpa [prefixWord, tailWord_2319388, baseEnd_2319388] using wordTrace_append hprefix tailTrace_2319388
  have hstable : (prefixWord ++ tailWord_2319388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319388).length < 2 ^ (prefixWord ++ tailWord_2319388).sum := by decide
  have hdescent : baseEnd_2319388 < baseStart_2319388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319391 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 4]
def baseStart_2319391 : Nat := 118140960795 + 2319391 * 2 ^ 59
def prefixEnd_2319391 : Nat := 4983230072969 + 3 ^ 40 * 2319391 * 2
def baseEnd_2319391 : Nat := 1190962408712440105745821

theorem tailTrace_2319391 : CollatzResearch.WordTrace tailWord_2319391 prefixEnd_2319391 1190962408712440105745821 := by
  unfold tailWord_2319391
  simp only [CollatzResearch.WordTrace]
  refine ⟨84595139540250002291150027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56396759693500001527433351 84595139540250002291150027)
  ·
    refine ⟨126892709310375003436725041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84595139540250002291150027 126892709310375003436725041)
    ·
      refine ⟨95169531982781252577543781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126892709310375003436725041 95169531982781252577543781)
      ·
        refine ⟨17844287246771484858289459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95169531982781252577543781 17844287246771484858289459)
        ·
          refine ⟨26766430870157227287434189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17844287246771484858289459 26766430870157227287434189)
          ·
            refine ⟨10037411576308960232787821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26766430870157227287434189 10037411576308960232787821)
            ·
              refine ⟨3764029341115860087295433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10037411576308960232787821 3764029341115860087295433)
              ·
                refine ⟨2823022005836895065471575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3764029341115860087295433 2823022005836895065471575)
                ·
                  refine ⟨4234533008755342598207363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823022005836895065471575 4234533008755342598207363)
                  ·
                    refine ⟨6351799513133013897311045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4234533008755342598207363 6351799513133013897311045)
                    ·
                      refine ⟨1190962408712440105745821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6351799513133013897311045 1190962408712440105745821)
                      ·
                        rfl

theorem cell23_2319391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_2319391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319391 prefixEnd_2319391 := by exact prefixLift 2319391
  have htrace : WordTrace (prefixWord ++ tailWord_2319391) baseStart_2319391 baseEnd_2319391 := by
    simpa [prefixWord, tailWord_2319391, baseEnd_2319391] using wordTrace_append hprefix tailTrace_2319391
  have hstable : (prefixWord ++ tailWord_2319391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319391).length < 2 ^ (prefixWord ++ tailWord_2319391).sum := by decide
  have hdescent : baseEnd_2319391 < baseStart_2319391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319397 : List Nat := [1, 3, 1, 2, 2, 2, 1, 11]
def baseStart_2319397 : Nat := 118140960795 + 2319397 * 2 ^ 59
def prefixEnd_2319397 : Nat := 4983230072969 + 3 ^ 40 * 2319397 * 2
def baseEnd_2319397 : Nat := 44109832948013595639659

theorem tailTrace_2319397 : CollatzResearch.WordTrace tailWord_2319397 prefixEnd_2319397 44109832948013595639659 := by
  unfold tailWord_2319397
  simp only [CollatzResearch.WordTrace]
  refine ⟨84595358378228265315868445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56396905585485510210578963 84595358378228265315868445)
  ·
    refine ⟨31723259391835599493450667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84595358378228265315868445 31723259391835599493450667)
    ·
      refine ⟨47584889087753399240176001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31723259391835599493450667 47584889087753399240176001)
      ·
        refine ⟨35688666815815049430132001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47584889087753399240176001 35688666815815049430132001)
        ·
          refine ⟨26766500111861287072599001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35688666815815049430132001 26766500111861287072599001)
          ·
            refine ⟨20074875083895965304449251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26766500111861287072599001 20074875083895965304449251)
            ·
              refine ⟨30112312625843947956673877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20074875083895965304449251 30112312625843947956673877)
              ·
                refine ⟨44109832948013595639659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 30112312625843947956673877 44109832948013595639659)
                ·
                  rfl

theorem cell23_2319397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 11].length) (baseStart_2319397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319397 prefixEnd_2319397 := by exact prefixLift 2319397
  have htrace : WordTrace (prefixWord ++ tailWord_2319397) baseStart_2319397 baseEnd_2319397 := by
    simpa [prefixWord, tailWord_2319397, baseEnd_2319397] using wordTrace_append hprefix tailTrace_2319397
  have hstable : (prefixWord ++ tailWord_2319397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319397).length < 2 ^ (prefixWord ++ tailWord_2319397).sum := by decide
  have hdescent : baseEnd_2319397 < baseStart_2319397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319404 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_2319404 : Nat := 118140960795 + 2319404 * 2 ^ 59
def prefixEnd_2319404 : Nat := 4983230072969 + 3 ^ 40 * 2319404 * 2
def baseEnd_2319404 : Nat := 1190969083960948554883261

theorem tailTrace_2319404 : CollatzResearch.WordTrace tailWord_2319404 prefixEnd_2319404 1190969083960948554883261 := by
  unfold tailWord_2319404
  simp only [CollatzResearch.WordTrace]
  refine ⟨42297806844601452755686633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56397075792801937007582177 42297806844601452755686633)
  ·
    refine ⟨31723355133451089566764975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42297806844601452755686633 31723355133451089566764975)
    ·
      refine ⟨47585032700176634350147463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31723355133451089566764975 47585032700176634350147463)
      ·
        refine ⟨71377549050264951525221195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47585032700176634350147463 71377549050264951525221195)
        ·
          refine ⟨107066323575397427287831793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71377549050264951525221195 107066323575397427287831793)
          ·
            refine ⟨80299742681548070465873845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107066323575397427287831793 80299742681548070465873845)
            ·
              refine ⟨7528100876395131606175673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80299742681548070465873845 7528100876395131606175673)
              ·
                refine ⟨5646075657296348704631755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7528100876395131606175673 5646075657296348704631755)
                ·
                  refine ⟨8469113485944523056947633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5646075657296348704631755 8469113485944523056947633)
                  ·
                    refine ⟨6351835114458392292710725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8469113485944523056947633 6351835114458392292710725)
                    ·
                      refine ⟨1190969083960948554883261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6351835114458392292710725 1190969083960948554883261)
                      ·
                        rfl

theorem cell23_2319404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_2319404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319404 prefixEnd_2319404 := by exact prefixLift 2319404
  have htrace : WordTrace (prefixWord ++ tailWord_2319404) baseStart_2319404 baseEnd_2319404 := by
    simpa [prefixWord, tailWord_2319404, baseEnd_2319404] using wordTrace_append hprefix tailTrace_2319404
  have hstable : (prefixWord ++ tailWord_2319404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319404).length < 2 ^ (prefixWord ++ tailWord_2319404).sum := by decide
  have hdescent : baseEnd_2319404 < baseStart_2319404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319414 : List Nat := [5, 1, 2, 1, 1, 13]
def baseStart_2319414 : Nat := 118140960795 + 2319414 * 2 ^ 59
def prefixEnd_2319414 : Nat := 4983230072969 + 3 ^ 40 * 2319414 * 2
def baseEnd_2319414 : Nat := 4901128472294211999005

theorem tailTrace_2319414 : CollatzResearch.WordTrace tailWord_2319414 prefixEnd_2319414 4901128472294211999005 := by
  unfold tailWord_2319414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287248651197917326202331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56397318946111118146158197 5287248651197917326202331)
  ·
    refine ⟨7930872976796875989303497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5287248651197917326202331 7930872976796875989303497)
    ·
      refine ⟨5948154732597656991977623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7930872976796875989303497 5948154732597656991977623)
      ·
        refine ⟨8922232098896485487966435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5948154732597656991977623 8922232098896485487966435)
        ·
          refine ⟨13383348148344728231949653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8922232098896485487966435 13383348148344728231949653)
          ·
            refine ⟨4901128472294211999005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 13383348148344728231949653 4901128472294211999005)
            ·
              rfl

theorem cell23_2319414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 13].length) (baseStart_2319414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319414 prefixEnd_2319414 := by exact prefixLift 2319414
  have htrace : WordTrace (prefixWord ++ tailWord_2319414) baseStart_2319414 baseEnd_2319414 := by
    simpa [prefixWord, tailWord_2319414, baseEnd_2319414] using wordTrace_append hprefix tailTrace_2319414
  have hstable : (prefixWord ++ tailWord_2319414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319414).length < 2 ^ (prefixWord ++ tailWord_2319414).sum := by decide
  have hdescent : baseEnd_2319414 < baseStart_2319414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319424 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 3]
def baseStart_2319424 : Nat := 118140960795 + 2319424 * 2 ^ 59
def prefixEnd_2319424 : Nat := 4983230072969 + 3 ^ 40 * 2319424 * 2
def baseEnd_2319424 : Nat := 1190979353574038476633169

theorem tailTrace_2319424 : CollatzResearch.WordTrace tailWord_2319424 prefixEnd_2319424 1190979353574038476633169 := by
  unfold tailWord_2319424
  simp only [CollatzResearch.WordTrace]
  refine ⟨42298171574565224463550663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56397562099420299284734217 42298171574565224463550663)
  ·
    refine ⟨63447257361847836695325995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42298171574565224463550663 63447257361847836695325995)
    ·
      refine ⟨95170886042771755042988993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63447257361847836695325995 95170886042771755042988993)
      ·
        refine ⟨71378164532078816282241745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95170886042771755042988993 71378164532078816282241745)
        ·
          refine ⟨53533623399059112211681309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71378164532078816282241745 53533623399059112211681309)
          ·
            refine ⟨20075108774647167079380491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53533623399059112211681309 20075108774647167079380491)
            ·
              refine ⟨30112663161970750619070737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20075108774647167079380491 30112663161970750619070737)
              ·
                refine ⟨22584497371478062964303053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30112663161970750619070737 22584497371478062964303053)
                ·
                  refine ⟨8469186514304273611613645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22584497371478062964303053 8469186514304273611613645)
                  ·
                    refine ⟨3175944942864102604355117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8469186514304273611613645 3175944942864102604355117)
                    ·
                      refine ⟨1190979353574038476633169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175944942864102604355117 1190979353574038476633169)
                      ·
                        rfl

theorem cell23_2319424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_2319424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319424 prefixEnd_2319424 := by exact prefixLift 2319424
  have htrace : WordTrace (prefixWord ++ tailWord_2319424) baseStart_2319424 baseEnd_2319424 := by
    simpa [prefixWord, tailWord_2319424, baseEnd_2319424] using wordTrace_append hprefix tailTrace_2319424
  have hstable : (prefixWord ++ tailWord_2319424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319424).length < 2 ^ (prefixWord ++ tailWord_2319424).sum := by decide
  have hdescent : baseEnd_2319424 < baseStart_2319424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319427 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 1, 9]
def baseStart_2319427 : Nat := 118140960795 + 2319427 * 2 ^ 59
def prefixEnd_2319427 : Nat := 4983230072969 + 3 ^ 40 * 2319427 * 2
def baseEnd_2319427 : Nat := 396993631338667321631885

theorem tailTrace_2319427 : CollatzResearch.WordTrace tailWord_2319427 prefixEnd_2319427 396993631338667321631885 := by
  unfold tailWord_2319427
  simp only [CollatzResearch.WordTrace]
  refine ⟨84596452568119580439460535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56397635045413053626307023 84596452568119580439460535)
  ·
    refine ⟨126894678852179370659190803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84596452568119580439460535 126894678852179370659190803)
    ·
      refine ⟨190342018278269055988786205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126894678852179370659190803 190342018278269055988786205)
      ·
        refine ⟨71378256854350895995794827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190342018278269055988786205 71378256854350895995794827)
        ·
          refine ⟨107067385281526343993692241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71378256854350895995794827 107067385281526343993692241)
          ·
            refine ⟨80300538961144757995269181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107067385281526343993692241 80300538961144757995269181)
            ·
              refine ⟨30112702110429284248225943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80300538961144757995269181 30112702110429284248225943)
              ·
                refine ⟨45169053165643926372338915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30112702110429284248225943 45169053165643926372338915)
                ·
                  refine ⟨67753579748465889558508373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45169053165643926372338915 67753579748465889558508373)
                  ·
                    refine ⟨396993631338667321631885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 67753579748465889558508373 396993631338667321631885)
                    ·
                      rfl

theorem cell23_2319427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 9].length) (baseStart_2319427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319427 prefixEnd_2319427 := by exact prefixLift 2319427
  have htrace : WordTrace (prefixWord ++ tailWord_2319427) baseStart_2319427 baseEnd_2319427 := by
    simpa [prefixWord, tailWord_2319427, baseEnd_2319427] using wordTrace_append hprefix tailTrace_2319427
  have hstable : (prefixWord ++ tailWord_2319427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319427).length < 2 ^ (prefixWord ++ tailWord_2319427).sum := by decide
  have hdescent : baseEnd_2319427 < baseStart_2319427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319458 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2319458 : Nat := 118140960795 + 2319458 * 2 ^ 59
def prefixEnd_2319458 : Nat := 4983230072969 + 3 ^ 40 * 2319458 * 2
def baseEnd_2319458 : Nat := 1190996811916291343608013

theorem tailTrace_2319458 : CollatzResearch.WordTrace tailWord_2319458 prefixEnd_2319458 1190996811916291343608013 := by
  unfold tailWord_2319458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21149395807751818183459757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56398388820671515155892685 21149395807751818183459757)
  ·
    refine ⟨7931023427906931818797409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21149395807751818183459757 7931023427906931818797409)
    ·
      refine ⟨5948267570930198864098057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7931023427906931818797409 5948267570930198864098057)
      ·
        refine ⟨4461200678197649148073543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5948267570930198864098057 4461200678197649148073543)
        ·
          refine ⟨6691801017296473722110315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4461200678197649148073543 6691801017296473722110315)
          ·
            refine ⟨10037701525944710583165473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6691801017296473722110315 10037701525944710583165473)
            ·
              refine ⟨7528276144458532937374105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10037701525944710583165473 7528276144458532937374105)
              ·
                refine ⟨5646207108343899703030579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7528276144458532937374105 5646207108343899703030579)
                ·
                  refine ⟨8469310662515849554545869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5646207108343899703030579 8469310662515849554545869)
                  ·
                    refine ⟨3175991498443443582954701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8469310662515849554545869 3175991498443443582954701)
                    ·
                      refine ⟨1190996811916291343608013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3175991498443443582954701 1190996811916291343608013)
                      ·
                        rfl

theorem cell23_2319458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2319458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319458 prefixEnd_2319458 := by exact prefixLift 2319458
  have htrace : WordTrace (prefixWord ++ tailWord_2319458) baseStart_2319458 baseEnd_2319458 := by
    simpa [prefixWord, tailWord_2319458, baseEnd_2319458] using wordTrace_append hprefix tailTrace_2319458
  have hstable : (prefixWord ++ tailWord_2319458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319458).length < 2 ^ (prefixWord ++ tailWord_2319458).sum := by decide
  have hdescent : baseEnd_2319458 < baseStart_2319458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319468 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 1, 3, 2]
def baseStart_2319468 : Nat := 118140960795 + 2319468 * 2 ^ 59
def prefixEnd_2319468 : Nat := 4983230072969 + 3 ^ 40 * 2319468 * 2
def baseEnd_2319468 : Nat := 1191001946722836304482967

theorem tailTrace_2319468 : CollatzResearch.WordTrace tailWord_2319468 prefixEnd_2319468 1191001946722836304482967 := by
  unfold tailWord_2319468
  simp only [CollatzResearch.WordTrace]
  refine ⟨42298973980485522220851529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56398631973980696294468705 42298973980485522220851529)
  ·
    refine ⟨31724230485364141665638647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42298973980485522220851529 31724230485364141665638647)
    ·
      refine ⟨47586345728046212498457971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31724230485364141665638647 47586345728046212498457971)
      ·
        refine ⟨71379518592069318747686957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47586345728046212498457971 71379518592069318747686957)
        ·
          refine ⟨26767319472025994530382609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71379518592069318747686957 26767319472025994530382609)
          ·
            refine ⟨20075489604019495897786957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26767319472025994530382609 20075489604019495897786957)
            ·
              refine ⟨7528308601507310961670109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20075489604019495897786957 7528308601507310961670109)
              ·
                refine ⟨2823115725565241610626291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7528308601507310961670109 2823115725565241610626291)
                ·
                  refine ⟨4234673588347862415939437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823115725565241610626291 4234673588347862415939437)
                  ·
                    refine ⟨1588002595630448405977289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4234673588347862415939437 1588002595630448405977289)
                    ·
                      refine ⟨1191001946722836304482967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588002595630448405977289 1191001946722836304482967)
                      ·
                        rfl

theorem cell23_2319468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_2319468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319468 prefixEnd_2319468 := by exact prefixLift 2319468
  have htrace : WordTrace (prefixWord ++ tailWord_2319468) baseStart_2319468 baseEnd_2319468 := by
    simpa [prefixWord, tailWord_2319468, baseEnd_2319468] using wordTrace_append hprefix tailTrace_2319468
  have hstable : (prefixWord ++ tailWord_2319468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319468).length < 2 ^ (prefixWord ++ tailWord_2319468).sum := by decide
  have hdescent : baseEnd_2319468 < baseStart_2319468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319474 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_2319474 : Nat := 118140960795 + 2319474 * 2 ^ 59
def prefixEnd_2319474 : Nat := 4983230072969 + 3 ^ 40 * 2319474 * 2
def baseEnd_2319474 : Nat := 397001675868921093669313

theorem tailTrace_2319474 : CollatzResearch.WordTrace tailWord_2319474 prefixEnd_2319474 397001675868921093669313 := by
  unfold tailWord_2319474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21149541699737326866605369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56398777865966204977614317 21149541699737326866605369)
  ·
    refine ⟨15862156274802995149954027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21149541699737326866605369 15862156274802995149954027)
    ·
      refine ⟨23793234412204492724931041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15862156274802995149954027 23793234412204492724931041)
      ·
        refine ⟨17844925809153369543698281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23793234412204492724931041 17844925809153369543698281)
        ·
          refine ⟨13383694356865027157773711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17844925809153369543698281 13383694356865027157773711)
          ·
            refine ⟨20075541535297540736660567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13383694356865027157773711 20075541535297540736660567)
            ·
              refine ⟨30113312302946311104990851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20075541535297540736660567 30113312302946311104990851)
              ·
                refine ⟨45169968454419466657486277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30113312302946311104990851 45169968454419466657486277)
                ·
                  refine ⟨8469369085203649998278677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45169968454419466657486277 8469369085203649998278677)
                  ·
                    refine ⟨397001675868921093669313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8469369085203649998278677 397001675868921093669313)
                    ·
                      rfl

theorem cell23_2319474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_2319474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319474 prefixEnd_2319474 := by exact prefixLift 2319474
  have htrace : WordTrace (prefixWord ++ tailWord_2319474) baseStart_2319474 baseEnd_2319474 := by
    simpa [prefixWord, tailWord_2319474, baseEnd_2319474] using wordTrace_append hprefix tailTrace_2319474
  have hstable : (prefixWord ++ tailWord_2319474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319474).length < 2 ^ (prefixWord ++ tailWord_2319474).sum := by decide
  have hdescent : baseEnd_2319474 < baseStart_2319474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319518 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2319518 : Nat := 118140960795 + 2319518 * 2 ^ 59
def prefixEnd_2319518 : Nat := 4983230072969 + 3 ^ 40 * 2319518 * 2
def baseEnd_2319518 : Nat := 1191027620755561108857737

theorem tailTrace_2319518 : CollatzResearch.WordTrace tailWord_2319518 prefixEnd_2319518 1191027620755561108857737 := by
  unfold tailWord_2319518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10574971451348737872627901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56399847740526601987348805 10574971451348737872627901)
  ·
    refine ⟨3965614294255776702235463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10574971451348737872627901 3965614294255776702235463)
    ·
      refine ⟨5948421441383665053353195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3965614294255776702235463 5948421441383665053353195)
      ·
        refine ⟨8922632162075497580029793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5948421441383665053353195 8922632162075497580029793)
        ·
          refine ⟨6691974121556623185022345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8922632162075497580029793 6691974121556623185022345)
          ·
            refine ⟨5018980591167467388766759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6691974121556623185022345 5018980591167467388766759)
            ·
              refine ⟨7528470886751201083150139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5018980591167467388766759 7528470886751201083150139)
              ·
                refine ⟨11292706330126801624725209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7528470886751201083150139 11292706330126801624725209)
                ·
                  refine ⟨8469529747595101218543907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11292706330126801624725209 8469529747595101218543907)
                  ·
                    refine ⟨12704294621392651827815861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8469529747595101218543907 12704294621392651827815861)
                    ·
                      refine ⟨1191027620755561108857737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12704294621392651827815861 1191027620755561108857737)
                      ·
                        rfl

theorem cell23_2319518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2319518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319518 prefixEnd_2319518 := by exact prefixLift 2319518
  have htrace : WordTrace (prefixWord ++ tailWord_2319518) baseStart_2319518 baseEnd_2319518 := by
    simpa [prefixWord, tailWord_2319518, baseEnd_2319518] using wordTrace_append hprefix tailTrace_2319518
  have hstable : (prefixWord ++ tailWord_2319518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319518).length < 2 ^ (prefixWord ++ tailWord_2319518).sum := by decide
  have hdescent : baseEnd_2319518 < baseStart_2319518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319571 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 1, 6, 2]
def baseStart_2319571 : Nat := 118140960795 + 2319571 * 2 ^ 59
def prefixEnd_2319571 : Nat := 4983230072969 + 3 ^ 40 * 2319571 * 2
def baseEnd_2319571 : Nat := 1191054835230249401494993

theorem tailTrace_2319571 : CollatzResearch.WordTrace tailWord_2319571 prefixEnd_2319571 1191054835230249401494993 := by
  unfold tailWord_2319571
  simp only [CollatzResearch.WordTrace]
  refine ⟨84601704679597893032702567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56401136453065262021801711 84601704679597893032702567)
  ·
    refine ⟨126902557019396839549053851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84601704679597893032702567 126902557019396839549053851)
    ·
      refine ⟨190353835529095259323580777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126902557019396839549053851 190353835529095259323580777)
      ·
        refine ⟨142765376646821444492685583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190353835529095259323580777 142765376646821444492685583)
        ·
          refine ⟨214148064970232166739028375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142765376646821444492685583 214148064970232166739028375)
          ·
            refine ⟨321222097455348250108542563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214148064970232166739028375 321222097455348250108542563)
            ·
              refine ⟨481833146183022375162813845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321222097455348250108542563 481833146183022375162813845)
              ·
                refine ⟨22585928727329173835756899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 481833146183022375162813845 22585928727329173835756899)
                ·
                  refine ⟨33878893090993760753635349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22585928727329173835756899 33878893090993760753635349)
                  ·
                    refine ⟨1588073113640332535326657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33878893090993760753635349 1588073113640332535326657)
                    ·
                      refine ⟨1191054835230249401494993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588073113640332535326657 1191054835230249401494993)
                      ·
                        rfl

theorem cell23_2319571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 6, 2].length) (baseStart_2319571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319571 prefixEnd_2319571 := by exact prefixLift 2319571
  have htrace : WordTrace (prefixWord ++ tailWord_2319571) baseStart_2319571 baseEnd_2319571 := by
    simpa [prefixWord, tailWord_2319571, baseEnd_2319571] using wordTrace_append hprefix tailTrace_2319571
  have hstable : (prefixWord ++ tailWord_2319571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319571).length < 2 ^ (prefixWord ++ tailWord_2319571).sum := by decide
  have hdescent : baseEnd_2319571 < baseStart_2319571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319645 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 6]
def baseStart_2319645 : Nat := 118140960795 + 2319645 * 2 ^ 59
def prefixEnd_2319645 : Nat := 4983230072969 + 3 ^ 40 * 2319645 * 2
def baseEnd_2319645 : Nat := 132343648088742456885517

theorem tailTrace_2319645 : CollatzResearch.WordTrace tailWord_2319645 prefixEnd_2319645 132343648088742456885517 := by
  unfold tailWord_2319645
  simp only [CollatzResearch.WordTrace]
  refine ⟨84604403681329803670896389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56402935787553202447264259 84604403681329803670896389)
  ·
    refine ⟨15863325690249338188293073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84604403681329803670896389 15863325690249338188293073)
    ·
      refine ⟨11897494267687003641219805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15863325690249338188293073 11897494267687003641219805)
      ·
        refine ⟨4461560350382626365457427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11897494267687003641219805 4461560350382626365457427)
        ·
          refine ⟨6692340525573939548186141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4461560350382626365457427 6692340525573939548186141)
          ·
            refine ⟨2509627697090227330569803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6692340525573939548186141 2509627697090227330569803)
            ·
              refine ⟨3764441545635340995854705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509627697090227330569803 3764441545635340995854705)
              ·
                refine ⟨2823331159226505746891029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3764441545635340995854705 2823331159226505746891029)
                ·
                  refine ⟨132343648088742456885517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2823331159226505746891029 132343648088742456885517)
                  ·
                    rfl

theorem cell23_2319645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_2319645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319645 prefixEnd_2319645 := by exact prefixLift 2319645
  have htrace : WordTrace (prefixWord ++ tailWord_2319645) baseStart_2319645 baseEnd_2319645 := by
    simpa [prefixWord, tailWord_2319645, baseEnd_2319645] using wordTrace_append hprefix tailTrace_2319645
  have hstable : (prefixWord ++ tailWord_2319645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319645).length < 2 ^ (prefixWord ++ tailWord_2319645).sum := by decide
  have hdescent : baseEnd_2319645 < baseStart_2319645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319698 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_2319698 : Nat := 118140960795 + 2319698 * 2 ^ 59
def prefixEnd_2319698 : Nat := 4983230072969 + 3 ^ 40 * 2319698 * 2
def baseEnd_2319698 : Nat := 1191120047273370404606909

theorem tailTrace_2319698 : CollatzResearch.WordTrace tailWord_2319698 prefixEnd_2319698 1191120047273370404606909 := by
  unfold tailWord_2319698
  simp only [CollatzResearch.WordTrace]
  refine ⟨21151584187534448430643937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56404224500091862481717165 21151584187534448430643937)
  ·
    refine ⟨15863688140650836322982953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21151584187534448430643937 15863688140650836322982953)
    ·
      refine ⟨11897766105488127242237215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15863688140650836322982953 11897766105488127242237215)
      ·
        refine ⟨17846649158232190863355823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11897766105488127242237215 17846649158232190863355823)
        ·
          refine ⟨26769973737348286295033735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17846649158232190863355823 26769973737348286295033735)
          ·
            refine ⟨40154960606022429442550603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26769973737348286295033735 40154960606022429442550603)
            ·
              refine ⟨60232440909033644163825905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40154960606022429442550603 60232440909033644163825905)
              ·
                refine ⟨45174330681775233122869429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60232440909033644163825905 45174330681775233122869429)
                ·
                  refine ⟨4235093501416428105269009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45174330681775233122869429 4235093501416428105269009)
                  ·
                    refine ⟨3176320126062321078951757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4235093501416428105269009 3176320126062321078951757)
                    ·
                      refine ⟨1191120047273370404606909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3176320126062321078951757 1191120047273370404606909)
                      ·
                        rfl

theorem cell23_2319698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_2319698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319698 prefixEnd_2319698 := by exact prefixLift 2319698
  have htrace : WordTrace (prefixWord ++ tailWord_2319698) baseStart_2319698 baseEnd_2319698 := by
    simpa [prefixWord, tailWord_2319698, baseEnd_2319698] using wordTrace_append hprefix tailTrace_2319698
  have hstable : (prefixWord ++ tailWord_2319698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319698).length < 2 ^ (prefixWord ++ tailWord_2319698).sum := by decide
  have hdescent : baseEnd_2319698 < baseStart_2319698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319701 : List Nat := [1, 3, 2, 2, 3, 1, 11]
def baseStart_2319701 : Nat := 118140960795 + 2319701 * 2 ^ 59
def prefixEnd_2319701 : Nat := 4983230072969 + 3 ^ 40 * 2319701 * 2
def baseEnd_2319701 : Nat := 14705204786609060405795

theorem tailTrace_2319701 : CollatzResearch.WordTrace tailWord_2319701 prefixEnd_2319701 14705204786609060405795 := by
  unfold tailWord_2319701
  simp only [CollatzResearch.WordTrace]
  refine ⟨84606446169126925234934957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56404297446084616823289971 84606446169126925234934957)
  ·
    refine ⟨31727417313422596963100609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84606446169126925234934957 31727417313422596963100609)
    ·
      refine ⟨23795562985066947722325457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31727417313422596963100609 23795562985066947722325457)
      ·
        refine ⟨17846672238800210791744093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23795562985066947722325457 17846672238800210791744093)
        ·
          refine ⟨6692502089550079046904035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17846672238800210791744093 6692502089550079046904035)
          ·
            refine ⟨10038753134325118570356053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6692502089550079046904035 10038753134325118570356053)
            ·
              refine ⟨14705204786609060405795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10038753134325118570356053 14705204786609060405795)
              ·
                rfl

theorem cell23_2319701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 11].length) (baseStart_2319701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319701 prefixEnd_2319701 := by exact prefixLift 2319701
  have htrace : WordTrace (prefixWord ++ tailWord_2319701) baseStart_2319701 baseEnd_2319701 := by
    simpa [prefixWord, tailWord_2319701, baseEnd_2319701] using wordTrace_append hprefix tailTrace_2319701
  have hstable : (prefixWord ++ tailWord_2319701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319701).length < 2 ^ (prefixWord ++ tailWord_2319701).sum := by decide
  have hdescent : baseEnd_2319701 < baseStart_2319701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319712 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 3, 2, 2]
def baseStart_2319712 : Nat := 118140960795 + 2319712 * 2 ^ 59
def prefixEnd_2319712 : Nat := 4983230072969 + 3 ^ 40 * 2319712 * 2
def baseEnd_2319712 : Nat := 1191127236002533349831845

theorem tailTrace_2319712 : CollatzResearch.WordTrace tailWord_2319712 prefixEnd_2319712 1191127236002533349831845 := by
  unfold tailWord_2319712
  simp only [CollatzResearch.WordTrace]
  refine ⟨42303423686043537056792695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56404564914724716075723593 42303423686043537056792695)
  ·
    refine ⟨63455135529065305585189043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42303423686043537056792695 63455135529065305585189043)
    ·
      refine ⟨95182703293597958377783565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63455135529065305585189043 95182703293597958377783565)
      ·
        refine ⟨35693513735099234391668837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95182703293597958377783565 35693513735099234391668837)
        ·
          refine ⟨6692533825331106448437907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35693513735099234391668837 6692533825331106448437907)
          ·
            refine ⟨10038800737996659672656861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6692533825331106448437907 10038800737996659672656861)
            ·
              refine ⟨3764550276748747377246323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10038800737996659672656861 3764550276748747377246323)
              ·
                refine ⟨5646825415123121065869485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3764550276748747377246323 5646825415123121065869485)
                ·
                  refine ⟨2117559530671170399701057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5646825415123121065869485 2117559530671170399701057)
                  ·
                    refine ⟨1588169648003377799775793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2117559530671170399701057 1588169648003377799775793)
                    ·
                      refine ⟨1191127236002533349831845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588169648003377799775793 1191127236002533349831845)
                      ·
                        rfl

theorem cell23_2319712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_2319712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319712 prefixEnd_2319712 := by exact prefixLift 2319712
  have htrace : WordTrace (prefixWord ++ tailWord_2319712) baseStart_2319712 baseEnd_2319712 := by
    simpa [prefixWord, tailWord_2319712, baseEnd_2319712] using wordTrace_append hprefix tailTrace_2319712
  have hstable : (prefixWord ++ tailWord_2319712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319712).length < 2 ^ (prefixWord ++ tailWord_2319712).sum := by decide
  have hdescent : baseEnd_2319712 < baseStart_2319712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319722 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_2319722 : Nat := 118140960795 + 2319722 * 2 ^ 59
def prefixEnd_2319722 : Nat := 4983230072969 + 3 ^ 40 * 2319722 * 2
def baseEnd_2319722 : Nat := 397044123603026103568933

theorem tailTrace_2319722 : CollatzResearch.WordTrace tailWord_2319722 prefixEnd_2319722 397044123603026103568933 := by
  unfold tailWord_2319722
  simp only [CollatzResearch.WordTrace]
  refine ⟨21151803025512711455362355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56404808068033897214299613 21151803025512711455362355)
  ·
    refine ⟨31727704538269067183043533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21151803025512711455362355 31727704538269067183043533)
    ·
      refine ⟨11897889201850900193641325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31727704538269067183043533 11897889201850900193641325)
      ·
        refine ⟨4461708450694087572615497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11897889201850900193641325 4461708450694087572615497)
        ·
          refine ⟨3346281338020565679461623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4461708450694087572615497 3346281338020565679461623)
          ·
            refine ⟨5019422007030848519192435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346281338020565679461623 5019422007030848519192435)
            ·
              refine ⟨7529133010546272778788653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5019422007030848519192435 7529133010546272778788653)
              ·
                refine ⟨2823424878954852292045745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7529133010546272778788653 2823424878954852292045745)
                ·
                  refine ⟨2117568659216139219034309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2823424878954852292045745 2117568659216139219034309)
                  ·
                    refine ⟨397044123603026103568933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2117568659216139219034309 397044123603026103568933)
                    ·
                      rfl

theorem cell23_2319722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_2319722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319722 prefixEnd_2319722 := by exact prefixLift 2319722
  have htrace : WordTrace (prefixWord ++ tailWord_2319722) baseStart_2319722 baseEnd_2319722 := by
    simpa [prefixWord, tailWord_2319722, baseEnd_2319722] using wordTrace_append hprefix tailTrace_2319722
  have hstable : (prefixWord ++ tailWord_2319722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319722).length < 2 ^ (prefixWord ++ tailWord_2319722).sum := by decide
  have hdescent : baseEnd_2319722 < baseStart_2319722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319728 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 3]
def baseStart_2319728 : Nat := 118140960795 + 2319728 * 2 ^ 59
def prefixEnd_2319728 : Nat := 4983230072969 + 3 ^ 40 * 2319728 * 2
def baseEnd_2319728 : Nat := 1191135451693005287231771

theorem tailTrace_2319728 : CollatzResearch.WordTrace tailWord_2319728 prefixEnd_2319728 1191135451693005287231771 := by
  unfold tailWord_2319728
  simp only [CollatzResearch.WordTrace]
  refine ⟨42303715470014554423083919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56404953960019405897445225 42303715470014554423083919)
  ·
    refine ⟨63455573205021831634625879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42303715470014554423083919 63455573205021831634625879)
    ·
      refine ⟨95183359807532747451938819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63455573205021831634625879 95183359807532747451938819)
      ·
        refine ⟨142775039711299121177908229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95183359807532747451938819 142775039711299121177908229)
        ·
          refine ⟨26770319945868585220857793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142775039711299121177908229 26770319945868585220857793)
          ·
            refine ⟨20077739959401438915643345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26770319945868585220857793 20077739959401438915643345)
            ·
              refine ⟨15058304969551079186732509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20077739959401438915643345 15058304969551079186732509)
              ·
                refine ⟨5646864363581654695024691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15058304969551079186732509 5646864363581654695024691)
                ·
                  refine ⟨8470296545372482042537037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5646864363581654695024691 8470296545372482042537037)
                  ·
                    refine ⟨3176361204514680765951389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8470296545372482042537037 3176361204514680765951389)
                    ·
                      refine ⟨1191135451693005287231771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3176361204514680765951389 1191135451693005287231771)
                      ·
                        rfl

theorem cell23_2319728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_2319728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319728 prefixEnd_2319728 := by exact prefixLift 2319728
  have htrace : WordTrace (prefixWord ++ tailWord_2319728) baseStart_2319728 baseEnd_2319728 := by
    simpa [prefixWord, tailWord_2319728, baseEnd_2319728] using wordTrace_append hprefix tailTrace_2319728
  have hstable : (prefixWord ++ tailWord_2319728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319728).length < 2 ^ (prefixWord ++ tailWord_2319728).sum := by decide
  have hdescent : baseEnd_2319728 < baseStart_2319728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319738 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2]
def baseStart_2319738 : Nat := 118140960795 + 2319738 * 2 ^ 59
def prefixEnd_2319738 : Nat := 4983230072969 + 3 ^ 40 * 2319738 * 2
def baseEnd_2319738 : Nat := 1191140586499550248106725

theorem tailTrace_2319738 : CollatzResearch.WordTrace tailWord_2319738 prefixEnd_2319738 1191140586499550248106725 := by
  unfold tailWord_2319738
  simp only [CollatzResearch.WordTrace]
  refine ⟨21151948917498220138507967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56405197113328587036021245 21151948917498220138507967)
  ·
    refine ⟨31727923376247330207761951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21151948917498220138507967 31727923376247330207761951)
    ·
      refine ⟨47591885064370995311642927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31727923376247330207761951 47591885064370995311642927)
      ·
        refine ⟨71387827596556492967464391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47591885064370995311642927 71387827596556492967464391)
        ·
          refine ⟨107081741394834739451196587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71387827596556492967464391 107081741394834739451196587)
          ·
            refine ⟨160622612092252109176794881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107081741394834739451196587 160622612092252109176794881)
            ·
              refine ⟨120466959069189081882596161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160622612092252109176794881 120466959069189081882596161)
              ·
                refine ⟨90350219301891811411947121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120466959069189081882596161 90350219301891811411947121)
                ·
                  refine ⟨67762664476418858558960341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90350219301891811411947121 67762664476418858558960341)
                  ·
                    refine ⟨1588187448666066997475633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 67762664476418858558960341 1588187448666066997475633)
                    ·
                      refine ⟨1191140586499550248106725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588187448666066997475633 1191140586499550248106725)
                      ·
                        rfl

theorem cell23_2319738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_2319738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319738 prefixEnd_2319738 := by exact prefixLift 2319738
  have htrace : WordTrace (prefixWord ++ tailWord_2319738) baseStart_2319738 baseEnd_2319738 := by
    simpa [prefixWord, tailWord_2319738, baseEnd_2319738] using wordTrace_append hprefix tailTrace_2319738
  have hstable : (prefixWord ++ tailWord_2319738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319738).length < 2 ^ (prefixWord ++ tailWord_2319738).sum := by decide
  have hdescent : baseEnd_2319738 < baseStart_2319738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319761 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 4, 6]
def baseStart_2319761 : Nat := 118140960795 + 2319761 * 2 ^ 59
def prefixEnd_2319761 : Nat := 4983230072969 + 3 ^ 40 * 2319761 * 2
def baseEnd_2319761 : Nat := 397050798851534552706373

theorem tailTrace_2319761 : CollatzResearch.WordTrace tailWord_2319761 prefixEnd_2319761 397050798851534552706373 := by
  unfold tailWord_2319761
  simp only [CollatzResearch.WordTrace]
  refine ⟨84608634548909555482119137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56405756365939703654746091 84608634548909555482119137)
  ·
    refine ⟨63456475911682166611589353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84608634548909555482119137 63456475911682166611589353)
    ·
      refine ⟨47592356933761624958692015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63456475911682166611589353 47592356933761624958692015)
      ·
        refine ⟨71388535400642437438038023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47592356933761624958692015 71388535400642437438038023)
        ·
          refine ⟨107082803100963656157057035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71388535400642437438038023 107082803100963656157057035)
          ·
            refine ⟨160624204651445484235585553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107082803100963656157057035 160624204651445484235585553)
            ·
              refine ⟨120468153488584113176689165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160624204651445484235585553 120468153488584113176689165)
              ·
                refine ⟨45175557558219042441258437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120468153488584113176689165 45175557558219042441258437)
                ·
                  refine ⟨8470417042166070457735957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45175557558219042441258437 8470417042166070457735957)
                  ·
                    refine ⟨397050798851534552706373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8470417042166070457735957 397050798851534552706373)
                    ·
                      rfl

theorem cell23_2319761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_2319761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319761 prefixEnd_2319761 := by exact prefixLift 2319761
  have htrace : WordTrace (prefixWord ++ tailWord_2319761) baseStart_2319761 baseEnd_2319761 := by
    simpa [prefixWord, tailWord_2319761, baseEnd_2319761] using wordTrace_append hprefix tailTrace_2319761
  have hstable : (prefixWord ++ tailWord_2319761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319761).length < 2 ^ (prefixWord ++ tailWord_2319761).sum := by decide
  have hdescent : baseEnd_2319761 < baseStart_2319761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319778 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2319778 : Nat := 118140960795 + 2319778 * 2 ^ 59
def prefixEnd_2319778 : Nat := 4983230072969 + 3 ^ 40 * 2319778 * 2
def baseEnd_2319778 : Nat := 397053708575243363868847

theorem tailTrace_2319778 : CollatzResearch.WordTrace tailWord_2319778 prefixEnd_2319778 397053708575243363868847 := by
  unfold tailWord_2319778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21152313647461991846371997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56406169726565311590325325 21152313647461991846371997)
  ·
    refine ⟨7932117617798246942389499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21152313647461991846371997 7932117617798246942389499)
    ·
      refine ⟨11898176426697370413584249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7932117617798246942389499 11898176426697370413584249)
      ·
        refine ⟨8923632320023027810188187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11898176426697370413584249 8923632320023027810188187)
        ·
          refine ⟨13385448480034541715282281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8923632320023027810188187 13385448480034541715282281)
          ·
            refine ⟨10039086360025906286461711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13385448480034541715282281 10039086360025906286461711)
            ·
              refine ⟨15058629540038859429692567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10039086360025906286461711 15058629540038859429692567)
              ·
                refine ⟨22587944310058289144538851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15058629540038859429692567 22587944310058289144538851)
                ·
                  refine ⟨33881916465087433716808277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22587944310058289144538851 33881916465087433716808277)
                  ·
                    refine ⟨397053708575243363868847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33881916465087433716808277 397053708575243363868847)
                    ·
                      rfl

theorem cell23_2319778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2319778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319778 prefixEnd_2319778 := by exact prefixLift 2319778
  have htrace : WordTrace (prefixWord ++ tailWord_2319778) baseStart_2319778 baseEnd_2319778 := by
    simpa [prefixWord, tailWord_2319778, baseEnd_2319778] using wordTrace_append hprefix tailTrace_2319778
  have hstable : (prefixWord ++ tailWord_2319778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319778).length < 2 ^ (prefixWord ++ tailWord_2319778).sum := by decide
  have hdescent : baseEnd_2319778 < baseStart_2319778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319785 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 8, 2, 2]
def baseStart_2319785 : Nat := 118140960795 + 2319785 * 2 ^ 59
def prefixEnd_2319785 : Nat := 4983230072969 + 3 ^ 40 * 2319785 * 2
def baseEnd_2319785 : Nat := 1191164720090311564219009

theorem tailTrace_2319785 : CollatzResearch.WordTrace tailWord_2319785 prefixEnd_2319785 1191164720090311564219009 := by
  unfold tailWord_2319785
  simp only [CollatzResearch.WordTrace]
  refine ⟨84609509900822607580992809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56406339933881738387328539 84609509900822607580992809)
  ·
    refine ⟨63457132425616955685744607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84609509900822607580992809 63457132425616955685744607)
    ·
      refine ⟨95185698638425433528616911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63457132425616955685744607 95185698638425433528616911)
      ·
        refine ⟨142778547957638150292925367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95185698638425433528616911 142778547957638150292925367)
        ·
          refine ⟨214167821936457225439388051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142778547957638150292925367 214167821936457225439388051)
          ·
            refine ⟨321251732904685838159082077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214167821936457225439388051 321251732904685838159082077)
            ·
              refine ⟨120469399839257189309655779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321251732904685838159082077 120469399839257189309655779)
              ·
                refine ⟨180704099758885783964483669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120469399839257189309655779 180704099758885783964483669)
                ·
                  refine ⟨2117626169049442780833793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 180704099758885783964483669 2117626169049442780833793)
                  ·
                    refine ⟨1588219626787082085625345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2117626169049442780833793 1588219626787082085625345)
                    ·
                      refine ⟨1191164720090311564219009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588219626787082085625345 1191164720090311564219009)
                      ·
                        rfl

theorem cell23_2319785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 2, 2].length) (baseStart_2319785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319785 prefixEnd_2319785 := by exact prefixLift 2319785
  have htrace : WordTrace (prefixWord ++ tailWord_2319785) baseStart_2319785 baseEnd_2319785 := by
    simpa [prefixWord, tailWord_2319785, baseEnd_2319785] using wordTrace_append hprefix tailTrace_2319785
  have hstable : (prefixWord ++ tailWord_2319785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319785).length < 2 ^ (prefixWord ++ tailWord_2319785).sum := by decide
  have hdescent : baseEnd_2319785 < baseStart_2319785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319875 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 2, 4, 2]
def baseStart_2319875 : Nat := 118140960795 + 2319875 * 2 ^ 59
def prefixEnd_2319875 : Nat := 4983230072969 + 3 ^ 40 * 2319875 * 2
def baseEnd_2319875 : Nat := 1191210933349216212093595

theorem tailTrace_2319875 : CollatzResearch.WordTrace tailWord_2319875 prefixEnd_2319875 1191210933349216212093595 := by
  unfold tailWord_2319875
  simp only [CollatzResearch.WordTrace]
  refine ⟨84612792470496552951769079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56408528313664368634512719 84612792470496552951769079)
  ·
    refine ⟨126919188705744829427653619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84612792470496552951769079 126919188705744829427653619)
    ·
      refine ⟨190378783058617244141480429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126919188705744829427653619 190378783058617244141480429)
      ·
        refine ⟨71392043646981466553055161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190378783058617244141480429 71392043646981466553055161)
        ·
          refine ⟨53544032735236099914791371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71392043646981466553055161 53544032735236099914791371)
          ·
            refine ⟨80316049102854149872187057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53544032735236099914791371 80316049102854149872187057)
            ·
              refine ⟨60237036827140612404140293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80316049102854149872187057 60237036827140612404140293)
              ·
                refine ⟨11294444405088864825776305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60237036827140612404140293 11294444405088864825776305)
                ·
                  refine ⟨8470833303816648619332229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11294444405088864825776305 8470833303816648619332229)
                  ·
                    refine ⟨1588281244465621616124793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8470833303816648619332229 1588281244465621616124793)
                    ·
                      refine ⟨1191210933349216212093595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588281244465621616124793 1191210933349216212093595)
                      ·
                        rfl

theorem cell23_2319875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_2319875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319875 prefixEnd_2319875 := by exact prefixLift 2319875
  have htrace : WordTrace (prefixWord ++ tailWord_2319875) baseStart_2319875 baseEnd_2319875 := by
    simpa [prefixWord, tailWord_2319875, baseEnd_2319875] using wordTrace_append hprefix tailTrace_2319875
  have hstable : (prefixWord ++ tailWord_2319875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319875).length < 2 ^ (prefixWord ++ tailWord_2319875).sum := by decide
  have hdescent : baseEnd_2319875 < baseStart_2319875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319932 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 6]
def baseStart_2319932 : Nat := 118140960795 + 2319932 * 2 ^ 59
def prefixEnd_2319932 : Nat := 4983230072969 + 3 ^ 40 * 2319932 * 2
def baseEnd_2319932 : Nat := 132360022416280276564537

theorem tailTrace_2319932 : CollatzResearch.WordTrace tailWord_2319932 prefixEnd_2319932 132360022416280276564537 := by
  unfold tailWord_2319932
  simp only [CollatzResearch.WordTrace]
  refine ⟨42307435715645025843297025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56409914287526701124396033 42307435715645025843297025)
  ·
    refine ⟨31730576786733769382472769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42307435715645025843297025 31730576786733769382472769)
    ·
      refine ⟨23797932590050327036854577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31730576786733769382472769 23797932590050327036854577)
      ·
        refine ⟨17848449442537745277640933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23797932590050327036854577 17848449442537745277640933)
        ·
          refine ⟨3346584270475827239557675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17848449442537745277640933 3346584270475827239557675)
          ·
            refine ⟨5019876405713740859336513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346584270475827239557675 5019876405713740859336513)
            ·
              refine ⟨3764907304285305644502385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5019876405713740859336513 3764907304285305644502385)
              ·
                refine ⟨2823680478213979233376789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3764907304285305644502385 2823680478213979233376789)
                ·
                  refine ⟨132360022416280276564537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2823680478213979233376789 132360022416280276564537)
                  ·
                    rfl

theorem cell23_2319932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_2319932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319932 prefixEnd_2319932 := by exact prefixLift 2319932
  have htrace : WordTrace (prefixWord ++ tailWord_2319932) baseStart_2319932 baseEnd_2319932 := by
    simpa [prefixWord, tailWord_2319932, baseEnd_2319932] using wordTrace_append hprefix tailTrace_2319932
  have hstable : (prefixWord ++ tailWord_2319932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319932).length < 2 ^ (prefixWord ++ tailWord_2319932).sum := by decide
  have hdescent : baseEnd_2319932 < baseStart_2319932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319975 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 1, 6]
def baseStart_2319975 : Nat := 118140960795 + 2319975 * 2 ^ 59
def prefixEnd_2319975 : Nat := 4983230072969 + 3 ^ 40 * 2319975 * 2
def baseEnd_2319975 : Nat := 397087427138221940281045

theorem tailTrace_2319975 : CollatzResearch.WordTrace tailWord_2319975 prefixEnd_2319975 397087427138221940281045 := by
  unfold tailWord_2319975
  simp only [CollatzResearch.WordTrace]
  refine ⟨84616439770134270030409379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56410959846756180020272919 84616439770134270030409379)
  ·
    refine ⟨126924659655201405045614069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84616439770134270030409379 126924659655201405045614069)
    ·
      refine ⟨11899186842675131723026319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126924659655201405045614069 11899186842675131723026319)
      ·
        refine ⟨17848780264012697584539479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11899186842675131723026319 17848780264012697584539479)
        ·
          refine ⟨26773170396019046376809219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17848780264012697584539479 26773170396019046376809219)
          ·
            refine ⟨40159755594028569565213829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26773170396019046376809219 40159755594028569565213829)
            ·
              refine ⟨7529954173880356793477593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40159755594028569565213829 7529954173880356793477593)
              ·
                refine ⟨5647465630410267595108195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7529954173880356793477593 5647465630410267595108195)
                ·
                  refine ⟨8471198445615401392662293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5647465630410267595108195 8471198445615401392662293)
                  ·
                    refine ⟨397087427138221940281045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8471198445615401392662293 397087427138221940281045)
                    ·
                      rfl

theorem cell23_2319975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_2319975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319975 prefixEnd_2319975 := by exact prefixLift 2319975
  have htrace : WordTrace (prefixWord ++ tailWord_2319975) baseStart_2319975 baseEnd_2319975 := by
    simpa [prefixWord, tailWord_2319975, baseEnd_2319975] using wordTrace_append hprefix tailTrace_2319975
  have hstable : (prefixWord ++ tailWord_2319975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319975).length < 2 ^ (prefixWord ++ tailWord_2319975).sum := by decide
  have hdescent : baseEnd_2319975 < baseStart_2319975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319976 : List Nat := [2, 1, 4, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2319976 : Nat := 118140960795 + 2319976 * 2 ^ 59
def prefixEnd_2319976 : Nat := 4983230072969 + 3 ^ 40 * 2319976 * 2
def baseEnd_2319976 : Nat := 1191262794895320316930631

theorem tailTrace_2319976 : CollatzResearch.WordTrace tailWord_2319976 prefixEnd_2319976 1191262794895320316930631 := by
  unfold tailWord_2319976
  simp only [CollatzResearch.WordTrace]
  refine ⟨42308238121565323600597891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56410984162087098134130521 42308238121565323600597891)
  ·
    refine ⟨63462357182347985400896837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42308238121565323600597891 63462357182347985400896837)
    ·
      refine ⟨11899191971690247262668157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63462357182347985400896837 11899191971690247262668157)
      ·
        refine ⟨4462196989383842723500559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11899191971690247262668157 4462196989383842723500559)
        ·
          refine ⟨6693295484075764085250839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4462196989383842723500559 6693295484075764085250839)
          ·
            refine ⟨10039943226113646127876259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6693295484075764085250839 10039943226113646127876259)
            ·
              refine ⟨15059914839170469191814389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10039943226113646127876259 15059914839170469191814389)
              ·
                refine ⟨1411867016172231486732599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15059914839170469191814389 1411867016172231486732599)
                ·
                  refine ⟨2117800524258347230098899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411867016172231486732599 2117800524258347230098899)
                  ·
                    refine ⟨3176700786387520845148349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2117800524258347230098899 3176700786387520845148349)
                    ·
                      refine ⟨1191262794895320316930631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3176700786387520845148349 1191262794895320316930631)
                      ·
                        rfl

theorem cell23_2319976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2319976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2319976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2319976 prefixEnd_2319976 := by exact prefixLift 2319976
  have htrace : WordTrace (prefixWord ++ tailWord_2319976) baseStart_2319976 baseEnd_2319976 := by
    simpa [prefixWord, tailWord_2319976, baseEnd_2319976] using wordTrace_append hprefix tailTrace_2319976
  have hstable : (prefixWord ++ tailWord_2319976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319976).length < 2 ^ (prefixWord ++ tailWord_2319976).sum := by decide
  have hdescent : baseEnd_2319976 < baseStart_2319976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320033 : List Nat := [1, 2, 3, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_2320033 : Nat := 118140960795 + 2320033 * 2 ^ 59
def prefixEnd_2320033 : Nat := 4983230072969 + 3 ^ 40 * 2320033 * 2
def baseEnd_2320033 : Nat := 1191292063292626593917869

theorem tailTrace_2320033 : CollatzResearch.WordTrace tailWord_2320033 prefixEnd_2320033 1191292063292626593917869 := by
  unfold tailWord_2320033
  simp only [CollatzResearch.WordTrace]
  refine ⟨84618555203924145936020753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56412370135949430624013835 84618555203924145936020753)
  ·
    refine ⟨63463916402943109452015565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84618555203924145936020753 63463916402943109452015565)
    ·
      refine ⟨23798968651103666044505837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63463916402943109452015565 23798968651103666044505837)
      ·
        refine ⟨8924613244163874766689689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23798968651103666044505837 8924613244163874766689689)
        ·
          refine ⟨6693459933122906075017267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8924613244163874766689689 6693459933122906075017267)
          ·
            refine ⟨10040189899684359112525901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6693459933122906075017267 10040189899684359112525901)
            ·
              refine ⟨3765071212381634667197213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10040189899684359112525901 3765071212381634667197213)
              ·
                refine ⟨1411901704643113000198955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3765071212381634667197213 1411901704643113000198955)
                ·
                  refine ⟨2117852556964669500298433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411901704643113000198955 2117852556964669500298433)
                  ·
                    refine ⟨1588389417723502125223825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2117852556964669500298433 1588389417723502125223825)
                    ·
                      refine ⟨1191292063292626593917869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588389417723502125223825 1191292063292626593917869)
                      ·
                        rfl

theorem cell23_2320033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_2320033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320033 prefixEnd_2320033 := by exact prefixLift 2320033
  have htrace : WordTrace (prefixWord ++ tailWord_2320033) baseStart_2320033 baseEnd_2320033 := by
    simpa [prefixWord, tailWord_2320033, baseEnd_2320033] using wordTrace_append hprefix tailTrace_2320033
  have hstable : (prefixWord ++ tailWord_2320033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320033).length < 2 ^ (prefixWord ++ tailWord_2320033).sum := by decide
  have hdescent : baseEnd_2320033 < baseStart_2320033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320070 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2320070 : Nat := 118140960795 + 2320070 * 2 ^ 59
def prefixEnd_2320070 : Nat := 4983230072969 + 3 ^ 40 * 2320070 * 2
def baseEnd_2320070 : Nat := 1191311062076842949155199

theorem tailTrace_2320070 : CollatzResearch.WordTrace tailWord_2320070 prefixEnd_2320070 1191311062076842949155199 := by
  unfold tailWord_2320070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644372022024690664222427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56413269803193400836745109 2644372022024690664222427)
  ·
    refine ⟨3966558033037035996333641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2644372022024690664222427 3966558033037035996333641)
    ·
      refine ⟨2974918524777776997250231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3966558033037035996333641 2974918524777776997250231)
      ·
        refine ⟨4462377787166665495875347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974918524777776997250231 4462377787166665495875347)
        ·
          refine ⟨6693566680749998243813021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4462377787166665495875347 6693566680749998243813021)
          ·
            refine ⟨2510087505281249341429883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6693566680749998243813021 2510087505281249341429883)
            ·
              refine ⟨3765131257921874012144825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510087505281249341429883 3765131257921874012144825)
              ·
                refine ⟨2823848443441405509108619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3765131257921874012144825 2823848443441405509108619)
                ·
                  refine ⟨4235772665162108263662929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823848443441405509108619 4235772665162108263662929)
                  ·
                    refine ⟨3176829498871581197747197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4235772665162108263662929 3176829498871581197747197)
                    ·
                      refine ⟨1191311062076842949155199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3176829498871581197747197 1191311062076842949155199)
                      ·
                        rfl

theorem cell23_2320070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2320070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320070 prefixEnd_2320070 := by exact prefixLift 2320070
  have htrace : WordTrace (prefixWord ++ tailWord_2320070) baseStart_2320070 baseEnd_2320070 := by
    simpa [prefixWord, tailWord_2320070, baseEnd_2320070] using wordTrace_append hprefix tailTrace_2320070
  have hstable : (prefixWord ++ tailWord_2320070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320070).length < 2 ^ (prefixWord ++ tailWord_2320070).sum := by decide
  have hdescent : baseEnd_2320070 < baseStart_2320070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320076 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2320076 : Nat := 118140960795 + 2320076 * 2 ^ 59
def prefixEnd_2320076 : Nat := 4983230072969 + 3 ^ 40 * 2320076 * 2
def baseEnd_2320076 : Nat := 1191314142960769925680171

theorem tailTrace_2320076 : CollatzResearch.WordTrace tailWord_2320076 prefixEnd_2320076 1191314142960769925680171 := by
  unfold tailWord_2320076
  simp only [CollatzResearch.WordTrace]
  refine ⟨42310061771384182139918041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56413415695178909519890721 42310061771384182139918041)
  ·
    refine ⟨31732546328538136604938531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42310061771384182139918041 31732546328538136604938531)
    ·
      refine ⟨47598819492807204907407797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31732546328538136604938531 47598819492807204907407797)
      ·
        refine ⟨4462389327450675460069481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47598819492807204907407797 4462389327450675460069481)
        ·
          refine ⟨3346791995588006595052111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4462389327450675460069481 3346791995588006595052111)
          ·
            refine ⟨5020187993382009892578167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346791995588006595052111 5020187993382009892578167)
            ·
              refine ⟨7530281990073014838867251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020187993382009892578167 7530281990073014838867251)
              ·
                refine ⟨11295422985109522258300877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7530281990073014838867251 11295422985109522258300877)
                ·
                  refine ⟨4235783619416070846862829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11295422985109522258300877 4235783619416070846862829)
                  ·
                    refine ⟨1588418857281026567573561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4235783619416070846862829 1588418857281026567573561)
                    ·
                      refine ⟨1191314142960769925680171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588418857281026567573561 1191314142960769925680171)
                      ·
                        rfl

theorem cell23_2320076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2320076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320076 prefixEnd_2320076 := by exact prefixLift 2320076
  have htrace : WordTrace (prefixWord ++ tailWord_2320076) baseStart_2320076 baseEnd_2320076 := by
    simpa [prefixWord, tailWord_2320076, baseEnd_2320076] using wordTrace_append hprefix tailTrace_2320076
  have hstable : (prefixWord ++ tailWord_2320076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320076).length < 2 ^ (prefixWord ++ tailWord_2320076).sum := by decide
  have hdescent : baseEnd_2320076 < baseStart_2320076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320089 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 1, 4, 2]
def baseStart_2320089 : Nat := 118140960795 + 2320089 * 2 ^ 59
def prefixEnd_2320089 : Nat := 4983230072969 + 3 ^ 40 * 2320089 * 2
def baseEnd_2320089 : Nat := 1191320818209278374817611

theorem tailTrace_2320089 : CollatzResearch.WordTrace tailWord_2320089 prefixEnd_2320089 1191320818209278374817611 := by
  unfold tailWord_2320089
  simp only [CollatzResearch.WordTrace]
  refine ⟨84620597691721267500059321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56413731794480845000039547 84620597691721267500059321)
  ·
    refine ⟨63465448268790950625044491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84620597691721267500059321 63465448268790950625044491)
    ·
      refine ⟨95198172403186425937566737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63465448268790950625044491 95198172403186425937566737)
      ·
        refine ⟨71398629302389819453175053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95198172403186425937566737 71398629302389819453175053)
        ·
          refine ⟨26774485988396182294940645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71398629302389819453175053 26774485988396182294940645)
          ·
            refine ⟨5020216122824284180301371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26774485988396182294940645 5020216122824284180301371)
            ·
              refine ⟨7530324184236426270452057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020216122824284180301371 7530324184236426270452057)
              ·
                refine ⟨5647743138177319702839043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7530324184236426270452057 5647743138177319702839043)
                ·
                  refine ⟨8471614707265979554258565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5647743138177319702839043 8471614707265979554258565)
                  ·
                    refine ⟨1588427757612371166423481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8471614707265979554258565 1588427757612371166423481)
                    ·
                      refine ⟨1191320818209278374817611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588427757612371166423481 1191320818209278374817611)
                      ·
                        rfl

theorem cell23_2320089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_2320089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320089 prefixEnd_2320089 := by exact prefixLift 2320089
  have htrace : WordTrace (prefixWord ++ tailWord_2320089) baseStart_2320089 baseEnd_2320089 := by
    simpa [prefixWord, tailWord_2320089, baseEnd_2320089] using wordTrace_append hprefix tailTrace_2320089
  have hstable : (prefixWord ++ tailWord_2320089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320089).length < 2 ^ (prefixWord ++ tailWord_2320089).sum := by decide
  have hdescent : baseEnd_2320089 < baseStart_2320089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320106 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_2320106 : Nat := 118140960795 + 2320106 * 2 ^ 59
def prefixEnd_2320106 : Nat := 4983230072969 + 3 ^ 40 * 2320106 * 2
def baseEnd_2320106 : Nat := 1191329547380404808305033

theorem tailTrace_2320106 : CollatzResearch.WordTrace tailWord_2320106 prefixEnd_2320106 1191329547380404808305033 := by
  unfold tailWord_2320106
  simp only [CollatzResearch.WordTrace]
  refine ⟨21155304433164919850857043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56414145155106452935618781 21155304433164919850857043)
  ·
    refine ⟨31732956649747379776285565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21155304433164919850857043 31732956649747379776285565)
    ·
      refine ⟨11899858743655267416107087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31732956649747379776285565 11899858743655267416107087)
      ·
        refine ⟨17849788115482901124160631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11899858743655267416107087 17849788115482901124160631)
        ·
          refine ⟨26774682173224351686240947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17849788115482901124160631 26774682173224351686240947)
          ·
            refine ⟨40162023259836527529361421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26774682173224351686240947 40162023259836527529361421)
            ·
              refine ⟨15060758722438697823510533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40162023259836527529361421 15060758722438697823510533)
              ·
                refine ⟨2823892260457255841908225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15060758722438697823510533 2823892260457255841908225)
                ·
                  refine ⟨2117919195342941881431169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2823892260457255841908225 2117919195342941881431169)
                  ·
                    refine ⟨1588439396507206411073377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2117919195342941881431169 1588439396507206411073377)
                    ·
                      refine ⟨1191329547380404808305033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588439396507206411073377 1191329547380404808305033)
                      ·
                        rfl

theorem cell23_2320106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_2320106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320106 prefixEnd_2320106 := by exact prefixLift 2320106
  have htrace : WordTrace (prefixWord ++ tailWord_2320106) baseStart_2320106 baseEnd_2320106 := by
    simpa [prefixWord, tailWord_2320106, baseEnd_2320106] using wordTrace_append hprefix tailTrace_2320106
  have hstable : (prefixWord ++ tailWord_2320106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320106).length < 2 ^ (prefixWord ++ tailWord_2320106).sum := by decide
  have hdescent : baseEnd_2320106 < baseStart_2320106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320116 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2320116 : Nat := 118140960795 + 2320116 * 2 ^ 59
def prefixEnd_2320116 : Nat := 4983230072969 + 3 ^ 40 * 2320116 * 2
def baseEnd_2320116 : Nat := 397111560728983256393329

theorem tailTrace_2320116 : CollatzResearch.WordTrace tailWord_2320116 prefixEnd_2320116 397111560728983256393329 := by
  unfold tailWord_2320116
  simp only [CollatzResearch.WordTrace]
  refine ⟨42310791231311725555646101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56414388308415634074194801 42310791231311725555646101)
  ·
    refine ⟨1983318338967737135420911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42310791231311725555646101 1983318338967737135420911)
    ·
      refine ⟨2974977508451605703131367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983318338967737135420911 2974977508451605703131367)
      ·
        refine ⟨4462466262677408554697051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974977508451605703131367 4462466262677408554697051)
        ·
          refine ⟨6693699394016112832045577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4462466262677408554697051 6693699394016112832045577)
          ·
            refine ⟨5020274545512084624034183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6693699394016112832045577 5020274545512084624034183)
            ·
              refine ⟨7530411818268126936051275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020274545512084624034183 7530411818268126936051275)
              ·
                refine ⟨11295617727402190404076913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7530411818268126936051275 11295617727402190404076913)
                ·
                  refine ⟨8471713295551642803057685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11295617727402190404076913 8471713295551642803057685)
                  ·
                    refine ⟨397111560728983256393329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8471713295551642803057685 397111560728983256393329)
                    ·
                      rfl

theorem cell23_2320116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2320116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320116 prefixEnd_2320116 := by exact prefixLift 2320116
  have htrace : WordTrace (prefixWord ++ tailWord_2320116) baseStart_2320116 baseEnd_2320116 := by
    simpa [prefixWord, tailWord_2320116, baseEnd_2320116] using wordTrace_append hprefix tailTrace_2320116
  have hstable : (prefixWord ++ tailWord_2320116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320116).length < 2 ^ (prefixWord ++ tailWord_2320116).sum := by decide
  have hdescent : baseEnd_2320116 < baseStart_2320116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320146 : List Nat := [3, 2, 4, 1, 1, 1, 1, 5, 5]
def baseStart_2320146 : Nat := 118140960795 + 2320146 * 2 ^ 59
def prefixEnd_2320146 : Nat := 4983230072969 + 3 ^ 40 * 2320146 * 2
def baseEnd_2320146 : Nat := 132372231845176072422761

theorem tailTrace_2320146 : CollatzResearch.WordTrace tailWord_2320146 prefixEnd_2320146 132372231845176072422761 := by
  unfold tailWord_2320146
  simp only [CollatzResearch.WordTrace]
  refine ⟨21155669163128691558721073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56415117768343177489922861 21155669163128691558721073)
  ·
    refine ⟨15866751872346518669040805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21155669163128691558721073 15866751872346518669040805)
    ·
      refine ⟨2975015976064972250445151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15866751872346518669040805 2975015976064972250445151)
      ·
        refine ⟨4462523964097458375667727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975015976064972250445151 4462523964097458375667727)
        ·
          refine ⟨6693785946146187563501591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4462523964097458375667727 6693785946146187563501591)
          ·
            refine ⟨10040678919219281345252387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6693785946146187563501591 10040678919219281345252387)
            ·
              refine ⟨15061018378828922017878581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10040678919219281345252387 15061018378828922017878581)
              ·
                refine ⟨1411970473015211439176117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15061018378828922017878581 1411970473015211439176117)
                ·
                  refine ⟨132372231845176072422761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1411970473015211439176117 132372231845176072422761)
                  ·
                    rfl

theorem cell23_2320146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_2320146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320146 prefixEnd_2320146 := by exact prefixLift 2320146
  have htrace : WordTrace (prefixWord ++ tailWord_2320146) baseStart_2320146 baseEnd_2320146 := by
    simpa [prefixWord, tailWord_2320146, baseEnd_2320146] using wordTrace_append hprefix tailTrace_2320146
  have hstable : (prefixWord ++ tailWord_2320146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320146).length < 2 ^ (prefixWord ++ tailWord_2320146).sum := by decide
  have hdescent : baseEnd_2320146 < baseStart_2320146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320223 : List Nat := [1, 1, 2, 3, 1, 5, 3, 2, 1, 4]
def baseStart_2320223 : Nat := 118140960795 + 2320223 * 2 ^ 59
def prefixEnd_2320223 : Nat := 4983230072969 + 3 ^ 40 * 2320223 * 2
def baseEnd_2320223 : Nat := 397129874872326950180665

theorem tailTrace_2320223 : CollatzResearch.WordTrace tailWord_2320223 prefixEnd_2320223 397129874872326950180665 := by
  unfold tailWord_2320223
  simp only [CollatzResearch.WordTrace]
  refine ⟨84625485073235808385437323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56416990048823872256958215 84625485073235808385437323)
  ·
    refine ⟨126938227609853712578155985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84625485073235808385437323 126938227609853712578155985)
    ·
      refine ⟨95203670707390284433616989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126938227609853712578155985 95203670707390284433616989)
      ·
        refine ⟨35701376515271356662606371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95203670707390284433616989 35701376515271356662606371)
        ·
          refine ⟨53552064772907034993909557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35701376515271356662606371 53552064772907034993909557)
          ·
            refine ⟨5020506072460034530679021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53552064772907034993909557 5020506072460034530679021)
            ·
              refine ⟨1882689777172512949004633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5020506072460034530679021 1882689777172512949004633)
              ·
                refine ⟨1412017332879384711753475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1882689777172512949004633 1412017332879384711753475)
                ·
                  refine ⟨2118025999319077067630213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412017332879384711753475 2118025999319077067630213)
                  ·
                    refine ⟨397129874872326950180665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2118025999319077067630213 397129874872326950180665)
                    ·
                      rfl

theorem cell23_2320223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 4].length) (baseStart_2320223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320223 prefixEnd_2320223 := by exact prefixLift 2320223
  have htrace : WordTrace (prefixWord ++ tailWord_2320223) baseStart_2320223 baseEnd_2320223 := by
    simpa [prefixWord, tailWord_2320223, baseEnd_2320223] using wordTrace_append hprefix tailTrace_2320223
  have hstable : (prefixWord ++ tailWord_2320223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320223).length < 2 ^ (prefixWord ++ tailWord_2320223).sum := by decide
  have hdescent : baseEnd_2320223 < baseStart_2320223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320236 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 6]
def baseStart_2320236 : Nat := 118140960795 + 2320236 * 2 ^ 59
def prefixEnd_2320236 : Nat := 4983230072969 + 3 ^ 40 * 2320236 * 2
def baseEnd_2320236 : Nat := 132377366651721033297715

theorem tailTrace_2320236 : CollatzResearch.WordTrace tailWord_2320236 prefixEnd_2320236 132377366651721033297715 := by
  unfold tailWord_2320236
  simp only [CollatzResearch.WordTrace]
  refine ⟨42312979611094355802830281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56417306148125807737107041 42312979611094355802830281)
  ·
    refine ⟨31734734708320766852122711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42312979611094355802830281 31734734708320766852122711)
    ·
      refine ⟨47602102062481150278184067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31734734708320766852122711 47602102062481150278184067)
      ·
        refine ⟨71403153093721725417276101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47602102062481150278184067 71403153093721725417276101)
        ·
          refine ⟨13388091205072823515739269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71403153093721725417276101 13388091205072823515739269)
          ·
            refine ⟨2510267100951154409201113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13388091205072823515739269 2510267100951154409201113)
            ·
              refine ⟨1882700325713365806900835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2510267100951154409201113 1882700325713365806900835)
              ·
                refine ⟨2824050488570048710351253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882700325713365806900835 2824050488570048710351253)
                ·
                  refine ⟨132377366651721033297715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2824050488570048710351253 132377366651721033297715)
                  ·
                    rfl

theorem cell23_2320236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_2320236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320236 prefixEnd_2320236 := by exact prefixLift 2320236
  have htrace : WordTrace (prefixWord ++ tailWord_2320236) baseStart_2320236 baseEnd_2320236 := by
    simpa [prefixWord, tailWord_2320236, baseEnd_2320236] using wordTrace_append hprefix tailTrace_2320236
  have hstable : (prefixWord ++ tailWord_2320236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320236).length < 2 ^ (prefixWord ++ tailWord_2320236).sum := by decide
  have hdescent : baseEnd_2320236 < baseStart_2320236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320256 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 2, 3, 2]
def baseStart_2320256 : Nat := 118140960795 + 2320256 * 2 ^ 59
def prefixEnd_2320256 : Nat := 4983230072969 + 3 ^ 40 * 2320256 * 2
def baseEnd_2320256 : Nat := 1191406569478579221429343

theorem tailTrace_2320256 : CollatzResearch.WordTrace tailWord_2320256 prefixEnd_2320256 1191406569478579221429343 := by
  unfold tailWord_2320256
  simp only [CollatzResearch.WordTrace]
  refine ⟨42313344341058127510694311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56417792454744170014259081 42313344341058127510694311)
  ·
    refine ⟨63470016511587191266041467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42313344341058127510694311 63470016511587191266041467)
    ·
      refine ⟨95205024767380786899062201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63470016511587191266041467 95205024767380786899062201)
      ·
        refine ⟨71403768575535590174296651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95205024767380786899062201 71403768575535590174296651)
        ·
          refine ⟨107105652863303385261444977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71403768575535590174296651 107105652863303385261444977)
          ·
            refine ⟨80329239647477538946083733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107105652863303385261444977 80329239647477538946083733)
            ·
              refine ⟨3765433108475509638097675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80329239647477538946083733 3765433108475509638097675)
              ·
                refine ⟨5648149662713264457146513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765433108475509638097675 5648149662713264457146513)
                ·
                  refine ⟨4236112247034948342859885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5648149662713264457146513 4236112247034948342859885)
                  ·
                    refine ⟨1588542092638105628572457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4236112247034948342859885 1588542092638105628572457)
                    ·
                      refine ⟨1191406569478579221429343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588542092638105628572457 1191406569478579221429343)
                      ·
                        rfl

theorem cell23_2320256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_2320256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320256 prefixEnd_2320256 := by exact prefixLift 2320256
  have htrace : WordTrace (prefixWord ++ tailWord_2320256) baseStart_2320256 baseEnd_2320256 := by
    simpa [prefixWord, tailWord_2320256, baseEnd_2320256] using wordTrace_append hprefix tailTrace_2320256
  have hstable : (prefixWord ++ tailWord_2320256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320256).length < 2 ^ (prefixWord ++ tailWord_2320256).sum := by decide
  have hdescent : baseEnd_2320256 < baseStart_2320256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320319 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 3]
def baseStart_2320319 : Nat := 118140960795 + 2320319 * 2 ^ 59
def prefixEnd_2320319 : Nat := 4983230072969 + 3 ^ 40 * 2320319 * 2
def baseEnd_2320319 : Nat := 1191438918759812474941553

theorem tailTrace_2320319 : CollatzResearch.WordTrace tailWord_2320319 prefixEnd_2320319 1191438918759812474941553 := by
  unfold tailWord_2320319
  simp only [CollatzResearch.WordTrace]
  refine ⟨84628986480888016780932011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56419324320592011187288007 84628986480888016780932011)
  ·
    refine ⟨126943479721332025171398017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84628986480888016780932011 126943479721332025171398017)
    ·
      refine ⟨95207609790999018878548513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126943479721332025171398017 95207609790999018878548513)
      ·
        refine ⟨71405707343249264158911385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95207609790999018878548513 71405707343249264158911385)
        ·
          refine ⟨53554280507436948119183539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71405707343249264158911385 53554280507436948119183539)
          ·
            refine ⟨80331420761155422178775309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53554280507436948119183539 80331420761155422178775309)
            ·
              refine ⟨30124282785433283317040741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80331420761155422178775309 30124282785433283317040741)
              ·
                refine ⟨5648303022268740621945139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30124282785433283317040741 5648303022268740621945139)
                ·
                  refine ⟨8472454533403110932917709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5648303022268740621945139 8472454533403110932917709)
                  ·
                    refine ⟨3177170450026166599844141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8472454533403110932917709 3177170450026166599844141)
                    ·
                      refine ⟨1191438918759812474941553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3177170450026166599844141 1191438918759812474941553)
                      ·
                        rfl

theorem cell23_2320319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_2320319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320319 prefixEnd_2320319 := by exact prefixLift 2320319
  have htrace : WordTrace (prefixWord ++ tailWord_2320319) baseStart_2320319 baseEnd_2320319 := by
    simpa [prefixWord, tailWord_2320319, baseEnd_2320319] using wordTrace_append hprefix tailTrace_2320319
  have hstable : (prefixWord ++ tailWord_2320319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320319).length < 2 ^ (prefixWord ++ tailWord_2320319).sum := by decide
  have hdescent : baseEnd_2320319 < baseStart_2320319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320320 : List Nat := [2, 1, 1, 2, 3, 2, 4, 3, 1, 2, 2]
def baseStart_2320320 : Nat := 118140960795 + 2320320 * 2 ^ 59
def prefixEnd_2320320 : Nat := 4983230072969 + 3 ^ 40 * 2320320 * 2
def baseEnd_2320320 : Nat := 1191439432240466971029049

theorem tailTrace_2320320 : CollatzResearch.WordTrace tailWord_2320320 prefixEnd_2320320 1191439432240466971029049 := by
  unfold tailWord_2320320
  simp only [CollatzResearch.WordTrace]
  refine ⟨42314511476942196975859207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56419348635922929301145609 42314511476942196975859207)
  ·
    refine ⟨63471767215413295463788811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42314511476942196975859207 63471767215413295463788811)
    ·
      refine ⟨95207650823119943195683217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63471767215413295463788811 95207650823119943195683217)
      ·
        refine ⟨71405738117339957396762413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95207650823119943195683217 71405738117339957396762413)
        ·
          refine ⟨26777151794002484023785905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71405738117339957396762413 26777151794002484023785905)
          ·
            refine ⟨20082863845501863017839429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26777151794002484023785905 20082863845501863017839429)
            ·
              refine ⟨3765536971031599315844893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20082863845501863017839429 3765536971031599315844893)
              ·
                refine ⟨1412076364136849743441835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3765536971031599315844893 1412076364136849743441835)
                ·
                  refine ⟨2118114546205274615162753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412076364136849743441835 2118114546205274615162753)
                  ·
                    refine ⟨1588585909653955961372065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2118114546205274615162753 1588585909653955961372065)
                    ·
                      refine ⟨1191439432240466971029049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588585909653955961372065 1191439432240466971029049)
                      ·
                        rfl

theorem cell23_2320320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_2320320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320320 prefixEnd_2320320 := by exact prefixLift 2320320
  have htrace : WordTrace (prefixWord ++ tailWord_2320320) baseStart_2320320 baseEnd_2320320 := by
    simpa [prefixWord, tailWord_2320320, baseEnd_2320320] using wordTrace_append hprefix tailTrace_2320320
  have hstable : (prefixWord ++ tailWord_2320320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320320).length < 2 ^ (prefixWord ++ tailWord_2320320).sum := by decide
  have hdescent : baseEnd_2320320 < baseStart_2320320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320376 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 1, 4, 2]
def baseStart_2320376 : Nat := 118140960795 + 2320376 * 2 ^ 59
def prefixEnd_2320376 : Nat := 4983230072969 + 3 ^ 40 * 2320376 * 2
def baseEnd_2320376 : Nat := 1191468187157118751928791

theorem tailTrace_2320376 : CollatzResearch.WordTrace tailWord_2320376 prefixEnd_2320376 1191468187157118751928791 := by
  unfold tailWord_2320376
  simp only [CollatzResearch.WordTrace]
  refine ⟨42315532720840757757878491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56420710294454343677171321 42315532720840757757878491)
  ·
    refine ⟨63473299081261136636817737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42315532720840757757878491 63473299081261136636817737)
    ·
      refine ⟨47604974310945852477613303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63473299081261136636817737 47604974310945852477613303)
      ·
        refine ⟨71407461466418778716419955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47604974310945852477613303 71407461466418778716419955)
        ·
          refine ⟨107111192199628168074629933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71407461466418778716419955 107111192199628168074629933)
          ·
            refine ⟨40166697074860563027986225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107111192199628168074629933 40166697074860563027986225)
            ·
              refine ⟨30125022806145422270989669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40166697074860563027986225 30125022806145422270989669)
              ·
                refine ⟨5648441776152266675810563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30125022806145422270989669 5648441776152266675810563)
                ·
                  refine ⟨8472662664228400013715845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5648441776152266675810563 8472662664228400013715845)
                  ·
                    refine ⟨1588624249542825002571721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8472662664228400013715845 1588624249542825002571721)
                    ·
                      refine ⟨1191468187157118751928791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588624249542825002571721 1191468187157118751928791)
                      ·
                        rfl

theorem cell23_2320376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_2320376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320376 prefixEnd_2320376 := by exact prefixLift 2320376
  have htrace : WordTrace (prefixWord ++ tailWord_2320376) baseStart_2320376 baseEnd_2320376 := by
    simpa [prefixWord, tailWord_2320376, baseEnd_2320376] using wordTrace_append hprefix tailTrace_2320376
  have hstable : (prefixWord ++ tailWord_2320376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320376).length < 2 ^ (prefixWord ++ tailWord_2320376).sum := by decide
  have hdescent : baseEnd_2320376 < baseStart_2320376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320409 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 3]
def baseStart_2320409 : Nat := 118140960795 + 2320409 * 2 ^ 59
def prefixEnd_2320409 : Nat := 4983230072969 + 3 ^ 40 * 2320409 * 2
def baseEnd_2320409 : Nat := 1191485132018717122816139

theorem tailTrace_2320409 : CollatzResearch.WordTrace tailWord_2320409 prefixEnd_2320409 1191485132018717122816139 := by
  unfold tailWord_2320409
  simp only [CollatzResearch.WordTrace]
  refine ⟨84632269050561962151708281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56421512700374641434472187 84632269050561962151708281)
  ·
    refine ⟨63474201787921471613781211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84632269050561962151708281 63474201787921471613781211)
    ·
      refine ⟨95211302681882207420671817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63474201787921471613781211 95211302681882207420671817)
      ·
        refine ⟨71408477011411655565503863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95211302681882207420671817 71408477011411655565503863)
        ·
          refine ⟨107112715517117483348255795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71408477011411655565503863 107112715517117483348255795)
          ·
            refine ⟨160669073275676225022383693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107112715517117483348255795 160669073275676225022383693)
            ·
              refine ⟨60250902478378584383393885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160669073275676225022383693 60250902478378584383393885)
              ·
                refine ⟨22594088429391969143772707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60250902478378584383393885 22594088429391969143772707)
                ·
                  refine ⟨33891132644087953715659061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22594088429391969143772707 33891132644087953715659061)
                  ·
                    refine ⟨3177293685383245660843037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33891132644087953715659061 3177293685383245660843037)
                    ·
                      refine ⟨1191485132018717122816139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3177293685383245660843037 1191485132018717122816139)
                      ·
                        rfl

theorem cell23_2320409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_2320409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320409 prefixEnd_2320409 := by exact prefixLift 2320409
  have htrace : WordTrace (prefixWord ++ tailWord_2320409) baseStart_2320409 baseEnd_2320409 := by
    simpa [prefixWord, tailWord_2320409, baseEnd_2320409] using wordTrace_append hprefix tailTrace_2320409
  have hstable : (prefixWord ++ tailWord_2320409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320409).length < 2 ^ (prefixWord ++ tailWord_2320409).sum := by decide
  have hdescent : baseEnd_2320409 < baseStart_2320409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320410 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2]
def baseStart_2320410 : Nat := 118140960795 + 2320410 * 2 ^ 59
def prefixEnd_2320410 : Nat := 4983230072969 + 3 ^ 40 * 2320410 * 2
def baseEnd_2320410 : Nat := 1191485645499371618903635

theorem tailTrace_2320410 : CollatzResearch.WordTrace tailWord_2320410 prefixEnd_2320410 1191485645499371618903635 := by
  unfold tailWord_2320410
  simp only [CollatzResearch.WordTrace]
  refine ⟨21158076380889584830623671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56421537015705559548329789 21158076380889584830623671)
  ·
    refine ⟨31737114571334377245935507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21158076380889584830623671 31737114571334377245935507)
    ·
      refine ⟨47605671857001565868903261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31737114571334377245935507 47605671857001565868903261)
      ·
        refine ⟨17852126946375587200838723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47605671857001565868903261 17852126946375587200838723)
        ·
          refine ⟨26778190419563380801258085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17852126946375587200838723 26778190419563380801258085)
          ·
            refine ⟨5020910703668133900235891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26778190419563380801258085 5020910703668133900235891)
            ·
              refine ⟨7531366055502200850353837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020910703668133900235891 7531366055502200850353837)
              ·
                refine ⟨2824262270813325318882689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7531366055502200850353837 2824262270813325318882689)
                ·
                  refine ⟨2118196703109993989162017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824262270813325318882689 2118196703109993989162017)
                  ·
                    refine ⟨1588647527332495491871513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2118196703109993989162017 1588647527332495491871513)
                    ·
                      refine ⟨1191485645499371618903635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588647527332495491871513 1191485645499371618903635)
                      ·
                        rfl

theorem cell23_2320410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_2320410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320410 prefixEnd_2320410 := by exact prefixLift 2320410
  have htrace : WordTrace (prefixWord ++ tailWord_2320410) baseStart_2320410 baseEnd_2320410 := by
    simpa [prefixWord, tailWord_2320410, baseEnd_2320410] using wordTrace_append hprefix tailTrace_2320410
  have hstable : (prefixWord ++ tailWord_2320410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320410).length < 2 ^ (prefixWord ++ tailWord_2320410).sum := by decide
  have hdescent : baseEnd_2320410 < baseStart_2320410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320439 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_2320439 : Nat := 118140960795 + 2320439 * 2 ^ 59
def prefixEnd_2320439 : Nat := 4983230072969 + 3 ^ 40 * 2320439 * 2
def baseEnd_2320439 : Nat := 1191500536438352005441001

theorem tailTrace_2320439 : CollatzResearch.WordTrace tailWord_2320439 prefixEnd_2320439 1191500536438352005441001 := by
  unfold tailWord_2320439
  simp only [CollatzResearch.WordTrace]
  refine ⟨84633363240453277275300371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56422242160302184850200247 84633363240453277275300371)
  ·
    refine ⟨126950044860679915912950557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84633363240453277275300371 126950044860679915912950557)
    ·
      refine ⟨47606266822754968467356459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126950044860679915912950557 47606266822754968467356459)
      ·
        refine ⟨71409400234132452701034689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47606266822754968467356459 71409400234132452701034689)
        ·
          refine ⟨53557050175599339525776017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71409400234132452701034689 53557050175599339525776017)
          ·
            refine ⟨40167787631699504644332013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53557050175599339525776017 40167787631699504644332013)
            ·
              refine ⟨15062920361887314241624505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40167787631699504644332013 15062920361887314241624505)
              ·
                refine ⟨11297190271415485681218379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15062920361887314241624505 11297190271415485681218379)
                ·
                  refine ⟨16945785407123228521827569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11297190271415485681218379 16945785407123228521827569)
                  ·
                    refine ⟨12709339055342421391370677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16945785407123228521827569 12709339055342421391370677)
                    ·
                      refine ⟨1191500536438352005441001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12709339055342421391370677 1191500536438352005441001)
                      ·
                        rfl

theorem cell23_2320439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_2320439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320439 prefixEnd_2320439 := by exact prefixLift 2320439
  have htrace : WordTrace (prefixWord ++ tailWord_2320439) baseStart_2320439 baseEnd_2320439 := by
    simpa [prefixWord, tailWord_2320439, baseEnd_2320439] using wordTrace_append hprefix tailTrace_2320439
  have hstable : (prefixWord ++ tailWord_2320439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320439).length < 2 ^ (prefixWord ++ tailWord_2320439).sum := by decide
  have hdescent : baseEnd_2320439 < baseStart_2320439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320479 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_2320479 : Nat := 118140960795 + 2320479 * 2 ^ 59
def prefixEnd_2320479 : Nat := 4983230072969 + 3 ^ 40 * 2320479 * 2
def baseEnd_2320479 : Nat := 1191521075664531848940817

theorem tailTrace_2320479 : CollatzResearch.WordTrace tailWord_2320479 prefixEnd_2320479 1191521075664531848940817 := by
  unfold tailWord_2320479
  simp only [CollatzResearch.WordTrace]
  refine ⟨84634822160308364106756491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56423214773538909404504327 84634822160308364106756491)
  ·
    refine ⟨126952233240462546160134737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84634822160308364106756491 126952233240462546160134737)
    ·
      refine ⟨95214174930346909620101053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126952233240462546160134737 95214174930346909620101053)
      ·
        refine ⟨35705315598880091107537895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95214174930346909620101053 35705315598880091107537895)
        ·
          refine ⟨53557973398320136661306843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35705315598880091107537895 53557973398320136661306843)
          ·
            refine ⟨80336960097480204991960265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53557973398320136661306843 80336960097480204991960265)
            ·
              refine ⟨60252720073110153743970199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80336960097480204991960265 60252720073110153743970199)
              ·
                refine ⟨90379080109665230615955299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60252720073110153743970199 90379080109665230615955299)
                ·
                  refine ⟨135568620164497845923932949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90379080109665230615955299 135568620164497845923932949)
                  ·
                    refine ⟨6354779070210836527684357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 135568620164497845923932949 6354779070210836527684357)
                    ·
                      refine ⟨1191521075664531848940817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6354779070210836527684357 1191521075664531848940817)
                      ·
                        rfl

theorem cell23_2320479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_2320479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320479 prefixEnd_2320479 := by exact prefixLift 2320479
  have htrace : WordTrace (prefixWord ++ tailWord_2320479) baseStart_2320479 baseEnd_2320479 := by
    simpa [prefixWord, tailWord_2320479, baseEnd_2320479] using wordTrace_append hprefix tailTrace_2320479
  have hstable : (prefixWord ++ tailWord_2320479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320479).length < 2 ^ (prefixWord ++ tailWord_2320479).sum := by decide
  have hdescent : baseEnd_2320479 < baseStart_2320479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320489 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 8]
def baseStart_2320489 : Nat := 118140960795 + 2320489 * 2 ^ 59
def prefixEnd_2320489 : Nat := 4983230072969 + 3 ^ 40 * 2320489 * 2
def baseEnd_2320489 : Nat := 132391801163452978868419

theorem tailTrace_2320489 : CollatzResearch.WordTrace tailWord_2320489 prefixEnd_2320489 132391801163452978868419 := by
  unfold tailWord_2320489
  simp only [CollatzResearch.WordTrace]
  refine ⟨84635186890272135814620521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56423457926848090543080347 84635186890272135814620521)
  ·
    refine ⟨63476390167704101860965391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84635186890272135814620521 63476390167704101860965391)
    ·
      refine ⟨95214585251556152791448087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63476390167704101860965391 95214585251556152791448087)
      ·
        refine ⟨142821877877334229187172131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95214585251556152791448087 142821877877334229187172131)
        ·
          refine ⟨214232816816001343780758197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142821877877334229187172131 214232816816001343780758197)
          ·
            refine ⟨20084326576500125979446081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214232816816001343780758197 20084326576500125979446081)
            ·
              refine ⟨15063244932375094484584561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20084326576500125979446081 15063244932375094484584561)
              ·
                refine ⟨11297433699281320863438421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15063244932375094484584561 11297433699281320863438421)
                ·
                  refine ⟨132391801163452978868419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11297433699281320863438421 132391801163452978868419)
                  ·
                    rfl

theorem cell23_2320489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 8].length) (baseStart_2320489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320489 prefixEnd_2320489 := by exact prefixLift 2320489
  have htrace : WordTrace (prefixWord ++ tailWord_2320489) baseStart_2320489 baseEnd_2320489 := by
    simpa [prefixWord, tailWord_2320489, baseEnd_2320489] using wordTrace_append hprefix tailTrace_2320489
  have hstable : (prefixWord ++ tailWord_2320489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320489).length < 2 ^ (prefixWord ++ tailWord_2320489).sum := by decide
  have hdescent : baseEnd_2320489 < baseStart_2320489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320533 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_2320533 : Nat := 118140960795 + 2320533 * 2 ^ 59
def prefixEnd_2320533 : Nat := 4983230072969 + 3 ^ 40 * 2320533 * 2
def baseEnd_2320533 : Nat := 1191548803619874637665569

theorem tailTrace_2320533 : CollatzResearch.WordTrace tailWord_2320533 prefixEnd_2320533 1191548803619874637665569 := by
  unfold tailWord_2320533
  simp only [CollatzResearch.WordTrace]
  refine ⟨84636791702112731329222253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56424527801408487552814835 84636791702112731329222253)
  ·
    refine ⟨31738796888292274248458345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84636791702112731329222253 31738796888292274248458345)
    ·
      refine ⟨23804097666219205686343759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31738796888292274248458345 23804097666219205686343759)
      ·
        refine ⟨35706146499328808529515639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23804097666219205686343759 35706146499328808529515639)
        ·
          refine ⟨53559219748993212794273459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35706146499328808529515639 53559219748993212794273459)
          ·
            refine ⟨80338829623489819191410189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53559219748993212794273459 80338829623489819191410189)
            ·
              refine ⟨30127061108808682196778821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80338829623489819191410189 30127061108808682196778821)
              ·
                refine ⟨5648823957901627911896029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30127061108808682196778821 5648823957901627911896029)
                ·
                  refine ⟨2118308984213110466961011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5648823957901627911896029 2118308984213110466961011)
                  ·
                    refine ⟨3177463476319665700441517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2118308984213110466961011 3177463476319665700441517)
                    ·
                      refine ⟨1191548803619874637665569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3177463476319665700441517 1191548803619874637665569)
                      ·
                        rfl

theorem cell23_2320533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_2320533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320533 prefixEnd_2320533 := by exact prefixLift 2320533
  have htrace : WordTrace (prefixWord ++ tailWord_2320533) baseStart_2320533 baseEnd_2320533 := by
    simpa [prefixWord, tailWord_2320533, baseEnd_2320533] using wordTrace_append hprefix tailTrace_2320533
  have hstable : (prefixWord ++ tailWord_2320533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320533).length < 2 ^ (prefixWord ++ tailWord_2320533).sum := by decide
  have hdescent : baseEnd_2320533 < baseStart_2320533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320586 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_2320586 : Nat := 118140960795 + 2320586 * 2 ^ 59
def prefixEnd_2320586 : Nat := 4983230072969 + 3 ^ 40 * 2320586 * 2
def baseEnd_2320586 : Nat := 1191576018094562930302825

theorem tailTrace_2320586 : CollatzResearch.WordTrace tailWord_2320586 prefixEnd_2320586 1191576018094562930302825 := by
  unfold tailWord_2320586
  simp only [CollatzResearch.WordTrace]
  refine ⟨21159681192730180345225403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56425816513947147587267741 21159681192730180345225403)
  ·
    refine ⟨31739521789095270517838105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21159681192730180345225403 31739521789095270517838105)
    ·
      refine ⟨23804641341821452888378579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31739521789095270517838105 23804641341821452888378579)
      ·
        refine ⟨35706962012732179332567869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23804641341821452888378579 35706962012732179332567869)
        ·
          refine ⟨13390110754774567249712951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35706962012732179332567869 13390110754774567249712951)
          ·
            refine ⟨20085166132161850874569427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13390110754774567249712951 20085166132161850874569427)
            ·
              refine ⟨30127749198242776311854141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20085166132161850874569427 30127749198242776311854141)
              ·
                refine ⟨11297905949341041116945303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30127749198242776311854141 11297905949341041116945303)
                ·
                  refine ⟨16946858924011561675417955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11297905949341041116945303 16946858924011561675417955)
                  ·
                    refine ⟨25420288386017342513126933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16946858924011561675417955 25420288386017342513126933)
                    ·
                      refine ⟨1191576018094562930302825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25420288386017342513126933 1191576018094562930302825)
                      ·
                        rfl

theorem cell23_2320586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_2320586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320586 prefixEnd_2320586 := by exact prefixLift 2320586
  have htrace : WordTrace (prefixWord ++ tailWord_2320586) baseStart_2320586 baseEnd_2320586 := by
    simpa [prefixWord, tailWord_2320586, baseEnd_2320586] using wordTrace_append hprefix tailTrace_2320586
  have hstable : (prefixWord ++ tailWord_2320586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320586).length < 2 ^ (prefixWord ++ tailWord_2320586).sum := by decide
  have hdescent : baseEnd_2320586 < baseStart_2320586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320590 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_2320590 : Nat := 118140960795 + 2320590 * 2 ^ 59
def prefixEnd_2320590 : Nat := 4983230072969 + 3 ^ 40 * 2320590 * 2
def baseEnd_2320590 : Nat := 1191578072017180914652807

theorem tailTrace_2320590 : CollatzResearch.WordTrace tailWord_2320590 prefixEnd_2320590 1191578072017180914652807 := by
  unfold tailWord_2320590
  simp only [CollatzResearch.WordTrace]
  refine ⟨10579858832863278758005903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56425913775270820042698149 10579858832863278758005903)
  ·
    refine ⟨15869788249294918137008855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10579858832863278758005903 15869788249294918137008855)
    ·
      refine ⟨23804682373942377205513283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15869788249294918137008855 23804682373942377205513283)
      ·
        refine ⟨35707023560913565808269925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23804682373942377205513283 35707023560913565808269925)
        ·
          refine ⟨6695066917671293589050611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35707023560913565808269925 6695066917671293589050611)
          ·
            refine ⟨10042600376506940383575917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6695066917671293589050611 10042600376506940383575917)
            ·
              refine ⟨3765975141190102643840969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10042600376506940383575917 3765975141190102643840969)
              ·
                refine ⟨2824481355892576982880727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3765975141190102643840969 2824481355892576982880727)
                ·
                  refine ⟨4236722033838865474321091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824481355892576982880727 4236722033838865474321091)
                  ·
                    refine ⟨6355083050758298211481637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4236722033838865474321091 6355083050758298211481637)
                    ·
                      refine ⟨1191578072017180914652807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6355083050758298211481637 1191578072017180914652807)
                      ·
                        rfl

theorem cell23_2320590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_2320590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320590 prefixEnd_2320590 := by exact prefixLift 2320590
  have htrace : WordTrace (prefixWord ++ tailWord_2320590) baseStart_2320590 baseEnd_2320590 := by
    simpa [prefixWord, tailWord_2320590, baseEnd_2320590] using wordTrace_append hprefix tailTrace_2320590
  have hstable : (prefixWord ++ tailWord_2320590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320590).length < 2 ^ (prefixWord ++ tailWord_2320590).sum := by decide
  have hdescent : baseEnd_2320590 < baseStart_2320590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320604 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2320604 : Nat := 118140960795 + 2320604 * 2 ^ 59
def prefixEnd_2320604 : Nat := 4983230072969 + 3 ^ 40 * 2320604 * 2
def baseEnd_2320604 : Nat := 397195086915447953292581

theorem tailTrace_2320604 : CollatzResearch.WordTrace tailWord_2320604 prefixEnd_2320604 397195086915447953292581 := by
  unfold tailWord_2320604
  simp only [CollatzResearch.WordTrace]
  refine ⟨42319690642427755227528433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56426254189903673636704577 42319690642427755227528433)
  ·
    refine ⟨31739767981820816420646325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42319690642427755227528433 31739767981820816420646325)
    ·
      refine ⟨2975603248295701539435593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31739767981820816420646325 2975603248295701539435593)
      ·
        refine ⟨2231702436221776154576695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2975603248295701539435593 2231702436221776154576695)
        ·
          refine ⟨3347553654332664231865043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231702436221776154576695 3347553654332664231865043)
          ·
            refine ⟨5021330481498996347797565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347553654332664231865043 5021330481498996347797565)
            ·
              refine ⟨1882998930562123630424087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5021330481498996347797565 1882998930562123630424087)
              ·
                refine ⟨2824498395843185445636131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882998930562123630424087 2824498395843185445636131)
                ·
                  refine ⟨4236747593764778168454197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824498395843185445636131 4236747593764778168454197)
                  ·
                    refine ⟨397195086915447953292581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4236747593764778168454197 397195086915447953292581)
                    ·
                      rfl

theorem cell23_2320604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2320604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320604 prefixEnd_2320604 := by exact prefixLift 2320604
  have htrace : WordTrace (prefixWord ++ tailWord_2320604) baseStart_2320604 baseEnd_2320604 := by
    simpa [prefixWord, tailWord_2320604, baseEnd_2320604] using wordTrace_append hprefix tailTrace_2320604
  have hstable : (prefixWord ++ tailWord_2320604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320604).length < 2 ^ (prefixWord ++ tailWord_2320604).sum := by decide
  have hdescent : baseEnd_2320604 < baseStart_2320604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320607 : List Nat := [1, 1, 2, 3, 2, 1, 1, 7, 1, 2, 2]
def baseStart_2320607 : Nat := 118140960795 + 2320607 * 2 ^ 59
def prefixEnd_2320607 : Nat := 4983230072969 + 3 ^ 40 * 2320607 * 2
def baseEnd_2320607 : Nat := 1191586801188307348140229

theorem tailTrace_2320607 : CollatzResearch.WordTrace tailWord_2320607 prefixEnd_2320607 1191586801188307348140229 := by
  unfold tailWord_2320607
  simp only [CollatzResearch.WordTrace]
  refine ⟨84639490703844641967416075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56426327135896427978277383 84639490703844641967416075)
  ·
    refine ⟨126959236055766962951124113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84639490703844641967416075 126959236055766962951124113)
    ·
      refine ⟨95219427041825222213343085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126959236055766962951124113 95219427041825222213343085)
      ·
        refine ⟨35707285140684458330003657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95219427041825222213343085 35707285140684458330003657)
        ·
          refine ⟨26780463855513343747502743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35707285140684458330003657 26780463855513343747502743)
          ·
            refine ⟨40170695783270015621254115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26780463855513343747502743 40170695783270015621254115)
            ·
              refine ⟨60256043674905023431881173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40170695783270015621254115 60256043674905023431881173)
              ·
                refine ⟨1412251023630586486684715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60256043674905023431881173 1412251023630586486684715)
                ·
                  refine ⟨2118376535445879730027073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412251023630586486684715 2118376535445879730027073)
                  ·
                    refine ⟨1588782401584409797520305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2118376535445879730027073 1588782401584409797520305)
                    ·
                      refine ⟨1191586801188307348140229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588782401584409797520305 1191586801188307348140229)
                      ·
                        rfl

theorem cell23_2320607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_2320607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320607 prefixEnd_2320607 := by exact prefixLift 2320607
  have htrace : WordTrace (prefixWord ++ tailWord_2320607) baseStart_2320607 baseEnd_2320607 := by
    simpa [prefixWord, tailWord_2320607, baseEnd_2320607] using wordTrace_append hprefix tailTrace_2320607
  have hstable : (prefixWord ++ tailWord_2320607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320607).length < 2 ^ (prefixWord ++ tailWord_2320607).sum := by decide
  have hdescent : baseEnd_2320607 < baseStart_2320607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320640 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 2, 1, 3]
def baseStart_2320640 : Nat := 118140960795 + 2320640 * 2 ^ 59
def prefixEnd_2320640 : Nat := 4983230072969 + 3 ^ 40 * 2320640 * 2
def baseEnd_2320640 : Nat := 1191603746049905719027577

theorem tailTrace_2320640 : CollatzResearch.WordTrace tailWord_2320640 prefixEnd_2320640 1191603746049905719027577 := by
  unfold tailWord_2320640
  simp only [CollatzResearch.WordTrace]
  refine ⟨42320347156362544301683687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56427129541816725735578249 42320347156362544301683687)
  ·
    refine ⟨63480520734543816452525531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42320347156362544301683687 63480520734543816452525531)
    ·
      refine ⟨95220781101815724678788297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63480520734543816452525531 95220781101815724678788297)
      ·
        refine ⟨71415585826361793509091223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95220781101815724678788297 71415585826361793509091223)
        ·
          refine ⟨107123378739542690263636835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71415585826361793509091223 107123378739542690263636835)
          ·
            refine ⟨160685068109314035395455253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107123378739542690263636835 160685068109314035395455253)
            ·
              refine ⟨7532112567624095409161965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 160685068109314035395455253 7532112567624095409161965)
              ·
                refine ⟨2824542212859035778435737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7532112567624095409161965 2824542212859035778435737)
                ·
                  refine ⟨2118406659644276833826803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824542212859035778435737 2118406659644276833826803)
                  ·
                    refine ⟨3177609989466415250740205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2118406659644276833826803 3177609989466415250740205)
                    ·
                      refine ⟨1191603746049905719027577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3177609989466415250740205 1191603746049905719027577)
                      ·
                        rfl

theorem cell23_2320640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_2320640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320640 prefixEnd_2320640 := by exact prefixLift 2320640
  have htrace : WordTrace (prefixWord ++ tailWord_2320640) baseStart_2320640 baseEnd_2320640 := by
    simpa [prefixWord, tailWord_2320640, baseEnd_2320640] using wordTrace_append hprefix tailTrace_2320640
  have hstable : (prefixWord ++ tailWord_2320640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320640).length < 2 ^ (prefixWord ++ tailWord_2320640).sum := by decide
  have hdescent : baseEnd_2320640 < baseStart_2320640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320650 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_2320650 : Nat := 118140960795 + 2320650 * 2 ^ 59
def prefixEnd_2320650 : Nat := 4983230072969 + 3 ^ 40 * 2320650 * 2
def baseEnd_2320650 : Nat := 1191608880856450679902531

theorem tailTrace_2320650 : CollatzResearch.WordTrace tailWord_2320650 prefixEnd_2320650 1191608880856450679902531 := by
  unfold tailWord_2320650
  simp only [CollatzResearch.WordTrace]
  refine ⟨21160264760672215077807851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56427372695125906874154269 21160264760672215077807851)
  ·
    refine ⟨31740397141008322616711777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21160264760672215077807851 31740397141008322616711777)
    ·
      refine ⟨23805297855756241962533833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31740397141008322616711777 23805297855756241962533833)
      ·
        refine ⟨17853973391817181471900375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23805297855756241962533833 17853973391817181471900375)
        ·
          refine ⟨26780960087725772207850563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17853973391817181471900375 26780960087725772207850563)
          ·
            refine ⟨40171440131588658311775845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26780960087725772207850563 40171440131588658311775845)
            ·
              refine ⟨7532145024672873433457971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40171440131588658311775845 7532145024672873433457971)
              ·
                refine ⟨11298217537009310150186957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7532145024672873433457971 11298217537009310150186957)
                ·
                  refine ⟨4236831576378491306320109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11298217537009310150186957 4236831576378491306320109)
                  ·
                    refine ⟨1588811841141934239870041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4236831576378491306320109 1588811841141934239870041)
                    ·
                      refine ⟨1191608880856450679902531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588811841141934239870041 1191608880856450679902531)
                      ·
                        rfl

theorem cell23_2320650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_2320650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320650 prefixEnd_2320650 := by exact prefixLift 2320650
  have htrace : WordTrace (prefixWord ++ tailWord_2320650) baseStart_2320650 baseEnd_2320650 := by
    simpa [prefixWord, tailWord_2320650, baseEnd_2320650] using wordTrace_append hprefix tailTrace_2320650
  have hstable : (prefixWord ++ tailWord_2320650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320650).length < 2 ^ (prefixWord ++ tailWord_2320650).sum := by decide
  have hdescent : baseEnd_2320650 < baseStart_2320650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320667 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 1, 3, 2]
def baseStart_2320667 : Nat := 118140960795 + 2320667 * 2 ^ 59
def prefixEnd_2320667 : Nat := 4983230072969 + 3 ^ 40 * 2320667 * 2
def baseEnd_2320667 : Nat := 1191617610027577113389953

theorem tailTrace_2320667 : CollatzResearch.WordTrace tailWord_2320667 prefixEnd_2320667 1191617610027577113389953 := by
  unfold tailWord_2320667
  simp only [CollatzResearch.WordTrace]
  refine ⟨84641679083627272214600255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56427786055751514809733503 84641679083627272214600255)
  ·
    refine ⟨126962518625440908321900383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84641679083627272214600255 126962518625440908321900383)
    ·
      refine ⟨190443777938161362482850575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126962518625440908321900383 190443777938161362482850575)
      ·
        refine ⟨285665666907242043724275863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190443777938161362482850575 285665666907242043724275863)
        ·
          refine ⟨428498500360863065586413795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285665666907242043724275863 428498500360863065586413795)
          ·
            refine ⟨642747750541294598379620693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428498500360863065586413795 642747750541294598379620693)
            ·
              refine ⟨1883050050413949018690295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 642747750541294598379620693 1883050050413949018690295)
              ·
                refine ⟨2824575075620923528035443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883050050413949018690295 2824575075620923528035443)
                ·
                  refine ⟨4236862613431385292053165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824575075620923528035443 4236862613431385292053165)
                  ·
                    refine ⟨1588823480036769484519937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4236862613431385292053165 1588823480036769484519937)
                    ·
                      refine ⟨1191617610027577113389953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588823480036769484519937 1191617610027577113389953)
                      ·
                        rfl

theorem cell23_2320667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 3, 2].length) (baseStart_2320667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320667 prefixEnd_2320667 := by exact prefixLift 2320667
  have htrace : WordTrace (prefixWord ++ tailWord_2320667) baseStart_2320667 baseEnd_2320667 := by
    simpa [prefixWord, tailWord_2320667, baseEnd_2320667] using wordTrace_append hprefix tailTrace_2320667
  have hstable : (prefixWord ++ tailWord_2320667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320667).length < 2 ^ (prefixWord ++ tailWord_2320667).sum := by decide
  have hdescent : baseEnd_2320667 < baseStart_2320667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320674 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_2320674 : Nat := 118140960795 + 2320674 * 2 ^ 59
def prefixEnd_2320674 : Nat := 4983230072969 + 3 ^ 40 * 2320674 * 2
def baseEnd_2320674 : Nat := 1191621204392158586002421

theorem tailTrace_2320674 : CollatzResearch.WordTrace tailWord_2320674 prefixEnd_2320674 1191621204392158586002421 := by
  unfold tailWord_2320674
  simp only [CollatzResearch.WordTrace]
  refine ⟨21160483598650478102526269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56427956263067941606736717 21160483598650478102526269)
  ·
    refine ⟨7935181349493929288447351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21160483598650478102526269 7935181349493929288447351)
    ·
      refine ⟨11902772024240893932671027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7935181349493929288447351 11902772024240893932671027)
      ·
        refine ⟨17854158036361340899006541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11902772024240893932671027 17854158036361340899006541)
        ·
          refine ⟨6695309263635502837127453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17854158036361340899006541 6695309263635502837127453)
          ·
            refine ⟨2510740973863313563922795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6695309263635502837127453 2510740973863313563922795)
            ·
              refine ⟨3766111460794970345884193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510740973863313563922795 3766111460794970345884193)
              ·
                refine ⟨2824583595596227759413145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766111460794970345884193 2824583595596227759413145)
                ·
                  refine ⟨2118437696697170819559859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824583595596227759413145 2118437696697170819559859)
                  ·
                    refine ⟨3177656545045756229339789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2118437696697170819559859 3177656545045756229339789)
                    ·
                      refine ⟨1191621204392158586002421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3177656545045756229339789 1191621204392158586002421)
                      ·
                        rfl

theorem cell23_2320674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_2320674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320674 prefixEnd_2320674 := by exact prefixLift 2320674
  have htrace : WordTrace (prefixWord ++ tailWord_2320674) baseStart_2320674 baseEnd_2320674 := by
    simpa [prefixWord, tailWord_2320674, baseEnd_2320674] using wordTrace_append hprefix tailTrace_2320674
  have hstable : (prefixWord ++ tailWord_2320674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320674).length < 2 ^ (prefixWord ++ tailWord_2320674).sum := by decide
  have hdescent : baseEnd_2320674 < baseStart_2320674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320693 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2320693 : Nat := 118140960795 + 2320693 * 2 ^ 59
def prefixEnd_2320693 : Nat := 4983230072969 + 3 ^ 40 * 2320693 * 2
def baseEnd_2320693 : Nat := 1191630960524594011664833

theorem tailTrace_2320693 : CollatzResearch.WordTrace tailWord_2320693 prefixEnd_2320693 1191630960524594011664833 := by
  unfold tailWord_2320693
  simp only [CollatzResearch.WordTrace]
  refine ⟨84642627381533078655046733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56428418254355385770031155 84642627381533078655046733)
  ·
    refine ⟨31740985268074904495642525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84642627381533078655046733 31740985268074904495642525)
    ·
      refine ⟨11902869475528089185865947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31740985268074904495642525 11902869475528089185865947)
      ·
        refine ⟨17854304213292133778798921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11902869475528089185865947 17854304213292133778798921)
        ·
          refine ⟨13390728159969100334099191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17854304213292133778798921 13390728159969100334099191)
          ·
            refine ⟨20086092239953650501148787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13390728159969100334099191 20086092239953650501148787)
            ·
              refine ⟨30129138359930475751723181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20086092239953650501148787 30129138359930475751723181)
              ·
                refine ⟨11298426884973928406896193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30129138359930475751723181 11298426884973928406896193)
                ·
                  refine ⟨8473820163730446305172145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11298426884973928406896193 8473820163730446305172145)
                  ·
                    refine ⟨6355365122797834728879109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8473820163730446305172145 6355365122797834728879109)
                    ·
                      refine ⟨1191630960524594011664833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6355365122797834728879109 1191630960524594011664833)
                      ·
                        rfl

theorem cell23_2320693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2320693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320693 prefixEnd_2320693 := by exact prefixLift 2320693
  have htrace : WordTrace (prefixWord ++ tailWord_2320693) baseStart_2320693 baseEnd_2320693 := by
    simpa [prefixWord, tailWord_2320693, baseEnd_2320693] using wordTrace_append hprefix tailTrace_2320693
  have hstable : (prefixWord ++ tailWord_2320693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320693).length < 2 ^ (prefixWord ++ tailWord_2320693).sum := by decide
  have hdescent : baseEnd_2320693 < baseStart_2320693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320697 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2320697 : Nat := 118140960795 + 2320697 * 2 ^ 59
def prefixEnd_2320697 : Nat := 4983230072969 + 3 ^ 40 * 2320697 * 2
def baseEnd_2320697 : Nat := 1191633014447211996014815

theorem tailTrace_2320697 : CollatzResearch.WordTrace tailWord_2320697 prefixEnd_2320697 1191633014447211996014815 := by
  unfold tailWord_2320697
  simp only [CollatzResearch.WordTrace]
  refine ⟨84642773273518587338192345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56428515515679058225461563 84642773273518587338192345)
  ·
    refine ⟨63482079955138940503644259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84642773273518587338192345 63482079955138940503644259)
    ·
      refine ⟨95223119932708410755466389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63482079955138940503644259 95223119932708410755466389)
      ·
        refine ⟨4463583746845706754162487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95223119932708410755466389 4463583746845706754162487)
        ·
          refine ⟨6695375620268560131243731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4463583746845706754162487 6695375620268560131243731)
          ·
            refine ⟨10043063430402840196865597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6695375620268560131243731 10043063430402840196865597)
            ·
              refine ⟨3766148786401065073824599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10043063430402840196865597 3766148786401065073824599)
              ·
                refine ⟨5649223179601597610736899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766148786401065073824599 5649223179601597610736899)
                ·
                  refine ⟨8473834769402396416105349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5649223179601597610736899 8473834769402396416105349)
                  ·
                    refine ⟨1588844019262949328019753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8473834769402396416105349 1588844019262949328019753)
                    ·
                      refine ⟨1191633014447211996014815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588844019262949328019753 1191633014447211996014815)
                      ·
                        rfl

theorem cell23_2320697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2320697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320697 prefixEnd_2320697 := by exact prefixLift 2320697
  have htrace : WordTrace (prefixWord ++ tailWord_2320697) baseStart_2320697 baseEnd_2320697 := by
    simpa [prefixWord, tailWord_2320697, baseEnd_2320697] using wordTrace_append hprefix tailTrace_2320697
  have hstable : (prefixWord ++ tailWord_2320697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320697).length < 2 ^ (prefixWord ++ tailWord_2320697).sum := by decide
  have hdescent : baseEnd_2320697 < baseStart_2320697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320720 : List Nat := [2, 1, 1, 1, 1, 6, 3, 3, 5]
def baseStart_2320720 : Nat := 118140960795 + 2320720 * 2 ^ 59
def prefixEnd_2320720 : Nat := 4983230072969 + 3 ^ 40 * 2320720 * 2
def baseEnd_2320720 : Nat := 132404980500251711780801

theorem tailTrace_2320720 : CollatzResearch.WordTrace tailWord_2320720 prefixEnd_2320720 132404980500251711780801 := by
  unfold tailWord_2320720
  simp only [CollatzResearch.WordTrace]
  refine ⟨42321806076217631133139807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56429074768290174844186409 42321806076217631133139807)
  ·
    refine ⟨63482709114326446699709711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42321806076217631133139807 63482709114326446699709711)
    ·
      refine ⟨95224063671489670049564567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63482709114326446699709711 95224063671489670049564567)
      ·
        refine ⟨142836095507234505074346851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95224063671489670049564567 142836095507234505074346851)
        ·
          refine ⟨214254143260851757611520277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142836095507234505074346851 214254143260851757611520277)
          ·
            refine ⟨10043162965352426138040013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 214254143260851757611520277 10043162965352426138040013)
            ·
              refine ⟨3766186112007159801765005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10043162965352426138040013 3766186112007159801765005)
              ·
                refine ⟨1412319792002684925661877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3766186112007159801765005 1412319792002684925661877)
                ·
                  refine ⟨132404980500251711780801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1412319792002684925661877 132404980500251711780801)
                  ·
                    rfl

theorem cell23_2320720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 5].length) (baseStart_2320720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320720 prefixEnd_2320720 := by exact prefixLift 2320720
  have htrace : WordTrace (prefixWord ++ tailWord_2320720) baseStart_2320720 baseEnd_2320720 := by
    simpa [prefixWord, tailWord_2320720, baseEnd_2320720] using wordTrace_append hprefix tailTrace_2320720
  have hstable : (prefixWord ++ tailWord_2320720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320720).length < 2 ^ (prefixWord ++ tailWord_2320720).sum := by decide
  have hdescent : baseEnd_2320720 < baseStart_2320720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320740 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_2320740 : Nat := 118140960795 + 2320740 * 2 ^ 59
def prefixEnd_2320740 : Nat := 4983230072969 + 3 ^ 40 * 2320740 * 2
def baseEnd_2320740 : Nat := 1191655094115355327777117

theorem tailTrace_2320740 : CollatzResearch.WordTrace tailWord_2320740 prefixEnd_2320740 1191655094115355327777117 := by
  unfold tailWord_2320740
  simp only [CollatzResearch.WordTrace]
  refine ⟨42322170806181402841003837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56429561074908537121338449 42322170806181402841003837)
  ·
    refine ⟨15870814052318026065376439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42322170806181402841003837 15870814052318026065376439)
    ·
      refine ⟨23806221078477039098064659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15870814052318026065376439 23806221078477039098064659)
      ·
        refine ⟨35709331617715558647096989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23806221078477039098064659 35709331617715558647096989)
        ·
          refine ⟨13390999356643334492661371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35709331617715558647096989 13390999356643334492661371)
          ·
            refine ⟨20086499034965001738992057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13390999356643334492661371 20086499034965001738992057)
            ·
              refine ⟨15064874276223751304244043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20086499034965001738992057 15064874276223751304244043)
              ·
                refine ⟨22597311414335626956366065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15064874276223751304244043 22597311414335626956366065)
                ·
                  refine ⟨16947983560751720217274549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22597311414335626956366065 16947983560751720217274549)
                  ·
                    refine ⟨1588873458820473770369489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16947983560751720217274549 1588873458820473770369489)
                    ·
                      refine ⟨1191655094115355327777117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588873458820473770369489 1191655094115355327777117)
                      ·
                        rfl

theorem cell23_2320740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_2320740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320740 prefixEnd_2320740 := by exact prefixLift 2320740
  have htrace : WordTrace (prefixWord ++ tailWord_2320740) baseStart_2320740 baseEnd_2320740 := by
    simpa [prefixWord, tailWord_2320740, baseEnd_2320740] using wordTrace_append hprefix tailTrace_2320740
  have hstable : (prefixWord ++ tailWord_2320740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320740).length < 2 ^ (prefixWord ++ tailWord_2320740).sum := by decide
  have hdescent : baseEnd_2320740 < baseStart_2320740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320743 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2320743 : Nat := 118140960795 + 2320743 * 2 ^ 59
def prefixEnd_2320743 : Nat := 4983230072969 + 3 ^ 40 * 2320743 * 2
def baseEnd_2320743 : Nat := 1191656634557318816039603

theorem tailTrace_2320743 : CollatzResearch.WordTrace tailWord_2320743 prefixEnd_2320743 1191656634557318816039603 := by
  unfold tailWord_2320743
  simp only [CollatzResearch.WordTrace]
  refine ⟨84644451031351937194366883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56429634020901291462911255 84644451031351937194366883)
  ·
    refine ⟨126966676547027905791550325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84644451031351937194366883 126966676547027905791550325)
    ·
      refine ⟨11903125926283866167957843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126966676547027905791550325 11903125926283866167957843)
      ·
        refine ⟨17854688889425799251936765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11903125926283866167957843 17854688889425799251936765)
        ·
          refine ⟨6695508333534674719476287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17854688889425799251936765 6695508333534674719476287)
          ·
            refine ⟨10043262500302012079214431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6695508333534674719476287 10043262500302012079214431)
            ·
              refine ⟨15064893750453018118821647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10043262500302012079214431 15064893750453018118821647)
              ·
                refine ⟨22597340625679527178232471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15064893750453018118821647 22597340625679527178232471)
                ·
                  refine ⟨33896010938519290767348707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22597340625679527178232471 33896010938519290767348707)
                  ·
                    refine ⟨50844016407778936151023061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33896010938519290767348707 50844016407778936151023061)
                    ·
                      refine ⟨1191656634557318816039603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50844016407778936151023061 1191656634557318816039603)
                      ·
                        rfl

theorem cell23_2320743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2320743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320743 prefixEnd_2320743 := by exact prefixLift 2320743
  have htrace : WordTrace (prefixWord ++ tailWord_2320743) baseStart_2320743 baseEnd_2320743 := by
    simpa [prefixWord, tailWord_2320743, baseEnd_2320743] using wordTrace_append hprefix tailTrace_2320743
  have hstable : (prefixWord ++ tailWord_2320743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320743).length < 2 ^ (prefixWord ++ tailWord_2320743).sum := by decide
  have hdescent : baseEnd_2320743 < baseStart_2320743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320748 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 2, 2, 2]
def baseStart_2320748 : Nat := 118140960795 + 2320748 * 2 ^ 59
def prefixEnd_2320748 : Nat := 4983230072969 + 3 ^ 40 * 2320748 * 2
def baseEnd_2320748 : Nat := 1191659201960591296477081

theorem tailTrace_2320748 : CollatzResearch.WordTrace tailWord_2320748 prefixEnd_2320748 1191659201960591296477081 := by
  unfold tailWord_2320748
  simp only [CollatzResearch.WordTrace]
  refine ⟨42322316698166911524149449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56429755597555882032199265 42322316698166911524149449)
  ·
    refine ⟨31741737523625183643112087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42322316698166911524149449 31741737523625183643112087)
    ·
      refine ⟨47612606285437775464668131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31741737523625183643112087 47612606285437775464668131)
      ·
        refine ⟨71418909428156663197002197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47612606285437775464668131 71418909428156663197002197)
        ·
          refine ⟨1673880689722421793679739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 71418909428156663197002197 1673880689722421793679739)
          ·
            refine ⟨2510821034583632690519609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673880689722421793679739 2510821034583632690519609)
            ·
              refine ⟨1883115775937724517889707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2510821034583632690519609 1883115775937724517889707)
              ·
                refine ⟨2824673663906586776834561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883115775937724517889707 2824673663906586776834561)
                ·
                  refine ⟨2118505247929940082625921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824673663906586776834561 2118505247929940082625921)
                  ·
                    refine ⟨1588878935947455061969441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2118505247929940082625921 1588878935947455061969441)
                    ·
                      refine ⟨1191659201960591296477081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1588878935947455061969441 1191659201960591296477081)
                      ·
                        rfl

theorem cell23_2320748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_2320748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320748 prefixEnd_2320748 := by exact prefixLift 2320748
  have htrace : WordTrace (prefixWord ++ tailWord_2320748) baseStart_2320748 baseEnd_2320748 := by
    simpa [prefixWord, tailWord_2320748, baseEnd_2320748] using wordTrace_append hprefix tailTrace_2320748
  have hstable : (prefixWord ++ tailWord_2320748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320748).length < 2 ^ (prefixWord ++ tailWord_2320748).sum := by decide
  have hdescent : baseEnd_2320748 < baseStart_2320748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320753 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_2320753 : Nat := 118140960795 + 2320753 * 2 ^ 59
def prefixEnd_2320753 : Nat := 4983230072969 + 3 ^ 40 * 2320753 * 2
def baseEnd_2320753 : Nat := 1191661769363863776914557

theorem tailTrace_2320753 : CollatzResearch.WordTrace tailWord_2320753 prefixEnd_2320753 1191661769363863776914557 := by
  unfold tailWord_2320753
  simp only [CollatzResearch.WordTrace]
  refine ⟨84644815761315708902230913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56429877174210472601487275 84644815761315708902230913)
  ·
    refine ⟨63483611820986781676673185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84644815761315708902230913 63483611820986781676673185)
    ·
      refine ⟨47612708865740086257504889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63483611820986781676673185 47612708865740086257504889)
      ·
        refine ⟨35709531649305064693128667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47612708865740086257504889 35709531649305064693128667)
        ·
          refine ⟨53564297473957597039693001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35709531649305064693128667 53564297473957597039693001)
          ·
            refine ⟨40173223105468197779769751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53564297473957597039693001 40173223105468197779769751)
            ·
              refine ⟨60259834658202296669654627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40173223105468197779769751 60259834658202296669654627)
              ·
                refine ⟨90389751987303445004481941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60259834658202296669654627 90389751987303445004481941)
                ·
                  refine ⟨4237019624404848984585091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90389751987303445004481941 4237019624404848984585091)
                  ·
                    refine ⟨6355529436607273476877637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4237019624404848984585091 6355529436607273476877637)
                    ·
                      refine ⟨1191661769363863776914557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6355529436607273476877637 1191661769363863776914557)
                      ·
                        rfl

theorem cell23_2320753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_2320753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320753 prefixEnd_2320753 := by exact prefixLift 2320753
  have htrace : WordTrace (prefixWord ++ tailWord_2320753) baseStart_2320753 baseEnd_2320753 := by
    simpa [prefixWord, tailWord_2320753, baseEnd_2320753] using wordTrace_append hprefix tailTrace_2320753
  have hstable : (prefixWord ++ tailWord_2320753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320753).length < 2 ^ (prefixWord ++ tailWord_2320753).sum := by decide
  have hdescent : baseEnd_2320753 < baseStart_2320753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320844 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 6]
def baseStart_2320844 : Nat := 118140960795 + 2320844 * 2 ^ 59
def prefixEnd_2320844 : Nat := 4983230072969 + 3 ^ 40 * 2320844 * 2
def baseEnd_2320844 : Nat := 132412055122602546764071

theorem tailTrace_2320844 : CollatzResearch.WordTrace tailWord_2320844 prefixEnd_2320844 132412055122602546764071 := by
  unfold tailWord_2320844
  simp only [CollatzResearch.WordTrace]
  refine ⟨42324067401993015721896793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56432089869324020962529057 42324067401993015721896793)
  ·
    refine ⟨31743050551494761791422595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42324067401993015721896793 31743050551494761791422595)
    ·
      refine ⟨47614575827242142687133893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31743050551494761791422595 47614575827242142687133893)
      ·
        refine ⟨8927732967607901753837605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47614575827242142687133893 8927732967607901753837605)
        ·
          refine ⟨1673949931426481578844551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8927732967607901753837605 1673949931426481578844551)
          ·
            refine ⟨2510924897139722368266827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673949931426481578844551 2510924897139722368266827)
            ·
              refine ⟨3766387345709583552400241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510924897139722368266827 3766387345709583552400241)
              ·
                refine ⟨2824790509282187664300181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766387345709583552400241 2824790509282187664300181)
                ·
                  refine ⟨132412055122602546764071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2824790509282187664300181 132412055122602546764071)
                  ·
                    rfl

theorem cell23_2320844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_2320844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320844 prefixEnd_2320844 := by exact prefixLift 2320844
  have htrace : WordTrace (prefixWord ++ tailWord_2320844) baseStart_2320844 baseEnd_2320844 := by
    simpa [prefixWord, tailWord_2320844, baseEnd_2320844] using wordTrace_append hprefix tailTrace_2320844
  have hstable : (prefixWord ++ tailWord_2320844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320844).length < 2 ^ (prefixWord ++ tailWord_2320844).sum := by decide
  have hdescent : baseEnd_2320844 < baseStart_2320844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320883 : List Nat := [1, 1, 1, 2, 2, 2, 5, 9]
def baseStart_2320883 : Nat := 118140960795 + 2320883 * 2 ^ 59
def prefixEnd_2320883 : Nat := 4983230072969 + 3 ^ 40 * 2320883 * 2
def baseEnd_2320883 : Nat := 44138093401812898825517

theorem tailTrace_2320883 : CollatzResearch.WordTrace tailWord_2320883 prefixEnd_2320883 44138093401812898825517 := by
  unfold tailWord_2320883
  simp only [CollatzResearch.WordTrace]
  refine ⟨84649557250844741104463303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56433038167229827402975535 84649557250844741104463303)
  ·
    refine ⟨126974335876267111656694955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84649557250844741104463303 126974335876267111656694955)
    ·
      refine ⟨190461503814400667485042433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126974335876267111656694955 190461503814400667485042433)
      ·
        refine ⟨142846127860800500613781825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190461503814400667485042433 142846127860800500613781825)
        ·
          refine ⟨107134595895600375460336369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142846127860800500613781825 107134595895600375460336369)
          ·
            refine ⟨80350946921700281595252277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107134595895600375460336369 80350946921700281595252277)
            ·
              refine ⟨7532901273909401399554901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80350946921700281595252277 7532901273909401399554901)
              ·
                refine ⟨44138093401812898825517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7532901273909401399554901 44138093401812898825517)
                ·
                  rfl

theorem cell23_2320883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 9].length) (baseStart_2320883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320883 prefixEnd_2320883 := by exact prefixLift 2320883
  have htrace : WordTrace (prefixWord ++ tailWord_2320883) baseStart_2320883 baseEnd_2320883 := by
    simpa [prefixWord, tailWord_2320883, baseEnd_2320883] using wordTrace_append hprefix tailTrace_2320883
  have hstable : (prefixWord ++ tailWord_2320883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320883).length < 2 ^ (prefixWord ++ tailWord_2320883).sum := by decide
  have hdescent : baseEnd_2320883 < baseStart_2320883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320897 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2320897 : Nat := 118140960795 + 2320897 * 2 ^ 59
def prefixEnd_2320897 : Nat := 4983230072969 + 3 ^ 40 * 2320897 * 2
def baseEnd_2320897 : Nat := 1191735710578111213513895

theorem tailTrace_2320897 : CollatzResearch.WordTrace tailWord_2320897 prefixEnd_2320897 1191735710578111213513895 := by
  unfold tailWord_2320897
  simp only [CollatzResearch.WordTrace]
  refine ⟨84650067872794021495472945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56433378581862680996981963 84650067872794021495472945)
  ·
    refine ⟨63487550904595516121604709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84650067872794021495472945 63487550904595516121604709)
    ·
      refine ⟨11903915794611659272800883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63487550904595516121604709 11903915794611659272800883)
      ·
        refine ⟨17855873691917488909201325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11903915794611659272800883 17855873691917488909201325)
        ·
          refine ⟨6695952634469058340950497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17855873691917488909201325 6695952634469058340950497)
          ·
            refine ⟨5021964475851793755712873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6695952634469058340950497 5021964475851793755712873)
            ·
              refine ⟨3766473356888845316784655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5021964475851793755712873 3766473356888845316784655)
              ·
                refine ⟨5649710035333267975176983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766473356888845316784655 5649710035333267975176983)
                ·
                  refine ⟨8474565052999901962765475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5649710035333267975176983 8474565052999901962765475)
                  ·
                    refine ⟨12711847579499852944148213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8474565052999901962765475 12711847579499852944148213)
                    ·
                      refine ⟨1191735710578111213513895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12711847579499852944148213 1191735710578111213513895)
                      ·
                        rfl

theorem cell23_2320897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2320897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320897 prefixEnd_2320897 := by exact prefixLift 2320897
  have htrace : WordTrace (prefixWord ++ tailWord_2320897) baseStart_2320897 baseEnd_2320897 := by
    simpa [prefixWord, tailWord_2320897, baseEnd_2320897] using wordTrace_append hprefix tailTrace_2320897
  have hstable : (prefixWord ++ tailWord_2320897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320897).length < 2 ^ (prefixWord ++ tailWord_2320897).sum := by decide
  have hdescent : baseEnd_2320897 < baseStart_2320897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320900 : List Nat := [2, 3, 2, 3, 1, 1, 11]
def baseStart_2320900 : Nat := 118140960795 + 2320900 * 2 ^ 59
def prefixEnd_2320900 : Nat := 4983230072969 + 3 ^ 40 * 2320900 * 2
def baseEnd_2320900 : Nat := 14712805568149070392301

theorem tailTrace_2320900 : CollatzResearch.WordTrace tailWord_2320900 prefixEnd_2320900 14712805568149070392301 := by
  unfold tailWord_2320900
  simp only [CollatzResearch.WordTrace]
  refine ⟨42325088645891576503916077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56433451527855435338554769 42325088645891576503916077)
  ·
    refine ⟨15871908242209341188968529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42325088645891576503916077 15871908242209341188968529)
    ·
      refine ⟨11903931181657005891726397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15871908242209341188968529 11903931181657005891726397)
      ·
        refine ⟨4463974193121377209397399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11903931181657005891726397 4463974193121377209397399)
        ·
          refine ⟨6695961289682065814096099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4463974193121377209397399 6695961289682065814096099)
          ·
            refine ⟨10043941934523098721144149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6695961289682065814096099 10043941934523098721144149)
            ·
              refine ⟨14712805568149070392301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10043941934523098721144149 14712805568149070392301)
              ·
                rfl

theorem cell23_2320900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 11].length) (baseStart_2320900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320900 prefixEnd_2320900 := by exact prefixLift 2320900
  have htrace : WordTrace (prefixWord ++ tailWord_2320900) baseStart_2320900 baseEnd_2320900 := by
    simpa [prefixWord, tailWord_2320900, baseEnd_2320900] using wordTrace_append hprefix tailTrace_2320900
  have hstable : (prefixWord ++ tailWord_2320900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320900).length < 2 ^ (prefixWord ++ tailWord_2320900).sum := by decide
  have hdescent : baseEnd_2320900 < baseStart_2320900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320948 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2320948 : Nat := 118140960795 + 2320948 * 2 ^ 59
def prefixEnd_2320948 : Nat := 4983230072969 + 3 ^ 40 * 2320948 * 2
def baseEnd_2320948 : Nat := 1191761898091490513976161

theorem tailTrace_2320948 : CollatzResearch.WordTrace tailWord_2320948 prefixEnd_2320948 1191761898091490513976161 := by
  unfold tailWord_2320948
  simp only [CollatzResearch.WordTrace]
  refine ⟨42325963997804628602789749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56434618663739504803719665 42325963997804628602789749)
  ·
    refine ⟨3968059124794183931511539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42325963997804628602789749 3968059124794183931511539)
    ·
      refine ⟨5952088687191275897267309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3968059124794183931511539 5952088687191275897267309)
      ·
        refine ⟨2232033257696728461475241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5952088687191275897267309 2232033257696728461475241)
        ·
          refine ⟨1674024943272546346106431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2232033257696728461475241 1674024943272546346106431)
          ·
            refine ⟨2511037414908819519159647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674024943272546346106431 2511037414908819519159647)
            ·
              refine ⟨3766556122363229278739471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511037414908819519159647 3766556122363229278739471)
              ·
                refine ⟨5649834183544843918109207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766556122363229278739471 5649834183544843918109207)
                ·
                  refine ⟨8474751275317265877163811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5649834183544843918109207 8474751275317265877163811)
                  ·
                    refine ⟨12712126912975898815745717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8474751275317265877163811 12712126912975898815745717)
                    ·
                      refine ⟨1191761898091490513976161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12712126912975898815745717 1191761898091490513976161)
                      ·
                        rfl

theorem cell23_2320948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2320948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320948 prefixEnd_2320948 := by exact prefixLift 2320948
  have htrace : WordTrace (prefixWord ++ tailWord_2320948) baseStart_2320948 baseEnd_2320948 := by
    simpa [prefixWord, tailWord_2320948, baseEnd_2320948] using wordTrace_append hprefix tailTrace_2320948
  have hstable : (prefixWord ++ tailWord_2320948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320948).length < 2 ^ (prefixWord ++ tailWord_2320948).sum := by decide
  have hdescent : baseEnd_2320948 < baseStart_2320948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2320961 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2320961 : Nat := 118140960795 + 2320961 * 2 ^ 59
def prefixEnd_2320961 : Nat := 4983230072969 + 3 ^ 40 * 2320961 * 2
def baseEnd_2320961 : Nat := 1191768573339998963113601

theorem tailTrace_2320961 : CollatzResearch.WordTrace tailWord_2320961 prefixEnd_2320961 1191768573339998963113601 := by
  unfold tailWord_2320961
  simp only [CollatzResearch.WordTrace]
  refine ⟨84652402144562160425802737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56434934763041440283868491 84652402144562160425802737)
  ·
    refine ⟨63489301608421620319352053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84652402144562160425802737 63489301608421620319352053)
    ·
      refine ⟨5952122025789526904939255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63489301608421620319352053 5952122025789526904939255)
      ·
        refine ⟨8928183038684290357408883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5952122025789526904939255 8928183038684290357408883)
        ·
          refine ⟨13392274558026435536113325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8928183038684290357408883 13392274558026435536113325)
          ·
            refine ⟨5022102959259913326042497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13392274558026435536113325 5022102959259913326042497)
            ·
              refine ⟨3766577219444934994531873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022102959259913326042497 3766577219444934994531873)
              ·
                refine ⟨2824932914583701245898905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766577219444934994531873 2824932914583701245898905)
                ·
                  refine ⟨2118699685937775934424179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824932914583701245898905 2118699685937775934424179)
                  ·
                    refine ⟨3178049528906663901636269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2118699685937775934424179 3178049528906663901636269)
                    ·
                      refine ⟨1191768573339998963113601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3178049528906663901636269 1191768573339998963113601)
                      ·
                        rfl

theorem cell23_2320961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2320961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2320961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2320961 prefixEnd_2320961 := by exact prefixLift 2320961
  have htrace : WordTrace (prefixWord ++ tailWord_2320961) baseStart_2320961 baseEnd_2320961 := by
    simpa [prefixWord, tailWord_2320961, baseEnd_2320961] using wordTrace_append hprefix tailTrace_2320961
  have hstable : (prefixWord ++ tailWord_2320961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2320961).length < 2 ^ (prefixWord ++ tailWord_2320961).sum := by decide
  have hdescent : baseEnd_2320961 < baseStart_2320961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2320961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321007 : List Nat := [1, 1, 2, 1, 3, 2, 3, 5, 5]
def baseStart_2321007 : Nat := 118140960795 + 2321007 * 2 ^ 59
def prefixEnd_2321007 : Nat := 4983230072969 + 3 ^ 40 * 2321007 * 2
def baseEnd_2321007 : Nat := 132421354827789531459821

theorem tailTrace_2321007 : CollatzResearch.WordTrace tailWord_2321007 prefixEnd_2321007 132421354827789531459821 := by
  unfold tailWord_2321007
  simp only [CollatzResearch.WordTrace]
  refine ⟨84654079902395510281977275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56436053268263673521318183 84654079902395510281977275)
  ·
    refine ⟨126981119853593265422965913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84654079902395510281977275 126981119853593265422965913)
    ·
      refine ⟨95235839890194949067224435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126981119853593265422965913 95235839890194949067224435)
      ·
        refine ⟨142853759835292423600836653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95235839890194949067224435 142853759835292423600836653)
        ·
          refine ⟨53570159938234658850313745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142853759835292423600836653 53570159938234658850313745)
          ·
            refine ⟨40177619953675994137735309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53570159938234658850313745 40177619953675994137735309)
            ·
              refine ⟨15066607482628497801650741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40177619953675994137735309 15066607482628497801650741)
              ·
                refine ⟨1412494451496421668904757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15066607482628497801650741 1412494451496421668904757)
                ·
                  refine ⟨132421354827789531459821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1412494451496421668904757 132421354827789531459821)
                  ·
                    rfl

theorem cell23_2321007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 5].length) (baseStart_2321007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321007 prefixEnd_2321007 := by exact prefixLift 2321007
  have htrace : WordTrace (prefixWord ++ tailWord_2321007) baseStart_2321007 baseEnd_2321007 := by
    simpa [prefixWord, tailWord_2321007, baseEnd_2321007] using wordTrace_append hprefix tailTrace_2321007
  have hstable : (prefixWord ++ tailWord_2321007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321007).length < 2 ^ (prefixWord ++ tailWord_2321007).sum := by decide
  have hdescent : baseEnd_2321007 < baseStart_2321007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321017 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 3]
def baseStart_2321017 : Nat := 118140960795 + 2321017 * 2 ^ 59
def prefixEnd_2321017 : Nat := 4983230072969 + 3 ^ 40 * 2321017 * 2
def baseEnd_2321017 : Nat := 1191797328256650744013343

theorem tailTrace_2321017 : CollatzResearch.WordTrace tailWord_2321017 prefixEnd_2321017 1191797328256650744013343 := by
  unfold tailWord_2321017
  simp only [CollatzResearch.WordTrace]
  refine ⟨84654444632359281989841305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56436296421572854659894203 84654444632359281989841305)
  ·
    refine ⟨63490833474269461492380979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84654444632359281989841305 63490833474269461492380979)
    ·
      refine ⟨95236250211404192238571469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63490833474269461492380979 95236250211404192238571469)
      ·
        refine ⟨35713593829276572089464301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95236250211404192238571469 35713593829276572089464301)
        ·
          refine ⟨13392597685978714533549113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35713593829276572089464301 13392597685978714533549113)
          ·
            refine ⟨10044448264484035900161835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13392597685978714533549113 10044448264484035900161835)
            ·
              refine ⟨15066672396726053850242753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10044448264484035900161835 15066672396726053850242753)
              ·
                refine ⟨11300004297544540387682065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15066672396726053850242753 11300004297544540387682065)
                ·
                  refine ⟨8475003223158405290761549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11300004297544540387682065 8475003223158405290761549)
                  ·
                    refine ⟨3178126208684401984035581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8475003223158405290761549 3178126208684401984035581)
                    ·
                      refine ⟨1191797328256650744013343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3178126208684401984035581 1191797328256650744013343)
                      ·
                        rfl

theorem cell23_2321017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_2321017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321017 prefixEnd_2321017 := by exact prefixLift 2321017
  have htrace : WordTrace (prefixWord ++ tailWord_2321017) baseStart_2321017 baseEnd_2321017 := by
    simpa [prefixWord, tailWord_2321017, baseEnd_2321017] using wordTrace_append hprefix tailTrace_2321017
  have hstable : (prefixWord ++ tailWord_2321017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321017).length < 2 ^ (prefixWord ++ tailWord_2321017).sum := by decide
  have hdescent : baseEnd_2321017 < baseStart_2321017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321027 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 1, 7, 2]
def baseStart_2321027 : Nat := 118140960795 + 2321027 * 2 ^ 59
def prefixEnd_2321027 : Nat := 4983230072969 + 3 ^ 40 * 2321027 * 2
def baseEnd_2321027 : Nat := 1191802463063195704888297

theorem tailTrace_2321027 : CollatzResearch.WordTrace tailWord_2321027 prefixEnd_2321027 1191802463063195704888297 := by
  unfold tailWord_2321027
  simp only [CollatzResearch.WordTrace]
  refine ⟨84654809362323053697705335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56436539574882035798470223 84654809362323053697705335)
  ·
    refine ⟨126982214043484580546558003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84654809362323053697705335 126982214043484580546558003)
    ·
      refine ⟨190473321065226870819837005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126982214043484580546558003 190473321065226870819837005)
      ·
        refine ⟨71427495399460076557438877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190473321065226870819837005 71427495399460076557438877)
        ·
          refine ⟨26785310774797528709039579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71427495399460076557438877 26785310774797528709039579)
          ·
            refine ⟨40177966162196293063559369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26785310774797528709039579 40177966162196293063559369)
            ·
              refine ⟨30133474621647219797669527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40177966162196293063559369 30133474621647219797669527)
              ·
                refine ⟨45200211932470829696504291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30133474621647219797669527 45200211932470829696504291)
                ·
                  refine ⟨67800317898706244544756437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45200211932470829696504291 67800317898706244544756437)
                  ·
                    refine ⟨1589069950750927606517729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 67800317898706244544756437 1589069950750927606517729)
                    ·
                      refine ⟨1191802463063195704888297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589069950750927606517729 1191802463063195704888297)
                      ·
                        rfl

theorem cell23_2321027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_2321027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321027 prefixEnd_2321027 := by exact prefixLift 2321027
  have htrace : WordTrace (prefixWord ++ tailWord_2321027) baseStart_2321027 baseEnd_2321027 := by
    simpa [prefixWord, tailWord_2321027, baseEnd_2321027] using wordTrace_append hprefix tailTrace_2321027
  have hstable : (prefixWord ++ tailWord_2321027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321027).length < 2 ^ (prefixWord ++ tailWord_2321027).sum := by decide
  have hdescent : baseEnd_2321027 < baseStart_2321027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321054 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2321054 : Nat := 118140960795 + 2321054 * 2 ^ 59
def prefixEnd_2321054 : Nat := 4983230072969 + 3 ^ 40 * 2321054 * 2
def baseEnd_2321054 : Nat := 397272109013622366416891

theorem tailTrace_2321054 : CollatzResearch.WordTrace tailWord_2321054 prefixEnd_2321054 397272109013622366416891 := by
  unfold tailWord_2321054
  simp only [CollatzResearch.WordTrace]
  refine ⟨10581974266653154663617277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56437196088816824872625477 10581974266653154663617277)
  ·
    refine ⟨3968240349994932998856479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10581974266653154663617277 3968240349994932998856479)
    ·
      refine ⟨5952360524992399498284719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3968240349994932998856479 5952360524992399498284719)
      ·
        refine ⟨8928540787488599247427079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5952360524992399498284719 8928540787488599247427079)
        ·
          refine ⟨13392811181232898871140619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8928540787488599247427079 13392811181232898871140619)
          ·
            refine ⟨20089216771849348306710929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13392811181232898871140619 20089216771849348306710929)
            ·
              refine ⟨15066912578887011230033197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20089216771849348306710929 15066912578887011230033197)
              ·
                refine ⟨5650092217082629211262449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15066912578887011230033197 5650092217082629211262449)
                ·
                  refine ⟨4237569162811971908446837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5650092217082629211262449 4237569162811971908446837)
                  ·
                    refine ⟨397272109013622366416891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4237569162811971908446837 397272109013622366416891)
                    ·
                      rfl

theorem cell23_2321054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2321054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321054 prefixEnd_2321054 := by exact prefixLift 2321054
  have htrace : WordTrace (prefixWord ++ tailWord_2321054) baseStart_2321054 baseEnd_2321054 := by
    simpa [prefixWord, tailWord_2321054, baseEnd_2321054] using wordTrace_append hprefix tailTrace_2321054
  have hstable : (prefixWord ++ tailWord_2321054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321054).length < 2 ^ (prefixWord ++ tailWord_2321054).sum := by decide
  have hdescent : baseEnd_2321054 < baseStart_2321054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321164 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_2321164 : Nat := 118140960795 + 2321164 * 2 ^ 59
def prefixEnd_2321164 : Nat := 4983230072969 + 3 ^ 40 * 2321164 * 2
def baseEnd_2321164 : Nat := 1191872809912861668875167

theorem tailTrace_2321164 : CollatzResearch.WordTrace tailWord_2321164 prefixEnd_2321164 1191872809912861668875167 := by
  unfold tailWord_2321164
  simp only [CollatzResearch.WordTrace]
  refine ⟨42329903081413363047721273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56439870775217817396961697 42329903081413363047721273)
  ·
    refine ⟨31747427311060022285790955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42329903081413363047721273 31747427311060022285790955)
    ·
      refine ⟨47621140966590033428686433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31747427311060022285790955 47621140966590033428686433)
      ·
        refine ⟨35715855724942525071514825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47621140966590033428686433 35715855724942525071514825)
        ·
          refine ⟨26786891793706893803636119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35715855724942525071514825 26786891793706893803636119)
          ·
            refine ⟨40180337690560340705454179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26786891793706893803636119 40180337690560340705454179)
            ·
              refine ⟨60270506535840511058181269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40180337690560340705454179 60270506535840511058181269)
              ·
                refine ⟨2825179993867523955852247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60270506535840511058181269 2825179993867523955852247)
                ·
                  refine ⟨4237769990801285933778371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825179993867523955852247 4237769990801285933778371)
                  ·
                    refine ⟨6356654986201928900667557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4237769990801285933778371 6356654986201928900667557)
                    ·
                      refine ⟨1191872809912861668875167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6356654986201928900667557 1191872809912861668875167)
                      ·
                        rfl

theorem cell23_2321164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_2321164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321164 prefixEnd_2321164 := by exact prefixLift 2321164
  have htrace : WordTrace (prefixWord ++ tailWord_2321164) baseStart_2321164 baseEnd_2321164 := by
    simpa [prefixWord, tailWord_2321164, baseEnd_2321164] using wordTrace_append hprefix tailTrace_2321164
  have hstable : (prefixWord ++ tailWord_2321164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321164).length < 2 ^ (prefixWord ++ tailWord_2321164).sum := by decide
  have hdescent : baseEnd_2321164 < baseStart_2321164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321175 : List Nat := [1, 1, 3, 4, 3, 1, 2, 3, 1, 1, 3]
def baseStart_2321175 : Nat := 118140960795 + 2321175 * 2 ^ 59
def prefixEnd_2321175 : Nat := 4983230072969 + 3 ^ 40 * 2321175 * 2
def baseEnd_2321175 : Nat := 1191878458200061125837617

theorem tailTrace_2321175 : CollatzResearch.WordTrace tailWord_2321175 prefixEnd_2321175 1191878458200061125837617 := by
  unfold tailWord_2321175
  simp only [CollatzResearch.WordTrace]
  refine ⟨84660207365786874974092979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56440138243857916649395319 84660207365786874974092979)
  ·
    refine ⟨126990311048680312461139469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84660207365786874974092979 126990311048680312461139469)
    ·
      refine ⟨47621366643255117172927301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126990311048680312461139469 47621366643255117172927301)
      ·
        refine ⟨8929006245610334469923869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47621366643255117172927301 8929006245610334469923869)
        ·
          refine ⟨3348377342103875426221451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8929006245610334469923869 3348377342103875426221451)
          ·
            refine ⟨5022566013155813139332177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348377342103875426221451 5022566013155813139332177)
            ·
              refine ⟨3766924509866859854499133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022566013155813139332177 3766924509866859854499133)
              ·
                refine ⟨1412596691200072445437175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3766924509866859854499133 1412596691200072445437175)
                ·
                  refine ⟨2118895036800108668155763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412596691200072445437175 2118895036800108668155763)
                  ·
                    refine ⟨3178342555200163002233645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2118895036800108668155763 3178342555200163002233645)
                    ·
                      refine ⟨1191878458200061125837617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3178342555200163002233645 1191878458200061125837617)
                      ·
                        rfl

theorem cell23_2321175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_2321175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321175 prefixEnd_2321175 := by exact prefixLift 2321175
  have htrace : WordTrace (prefixWord ++ tailWord_2321175) baseStart_2321175 baseEnd_2321175 := by
    simpa [prefixWord, tailWord_2321175, baseEnd_2321175] using wordTrace_append hprefix tailTrace_2321175
  have hstable : (prefixWord ++ tailWord_2321175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321175).length < 2 ^ (prefixWord ++ tailWord_2321175).sum := by decide
  have hdescent : baseEnd_2321175 < baseStart_2321175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321177 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_2321177 : Nat := 118140960795 + 2321177 * 2 ^ 59
def prefixEnd_2321177 : Nat := 4983230072969 + 3 ^ 40 * 2321177 * 2
def baseEnd_2321177 : Nat := 1191879485161370118012607

theorem tailTrace_2321177 : CollatzResearch.WordTrace tailWord_2321177 prefixEnd_2321177 1191879485161370118012607 := by
  unfold tailWord_2321177
  simp only [CollatzResearch.WordTrace]
  refine ⟨84660280311779629315665785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56440186874519752877110523 84660280311779629315665785)
  ·
    refine ⟨63495210233834721986749339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84660280311779629315665785 63495210233834721986749339)
    ·
      refine ⟨95242815350752082980124009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63495210233834721986749339 95242815350752082980124009)
      ·
        refine ⟨71432111513064062235093007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95242815350752082980124009 71432111513064062235093007)
        ·
          refine ⟨107148167269596093352639511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71432111513064062235093007 107148167269596093352639511)
          ·
            refine ⟨160722250904394140028959267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107148167269596093352639511 160722250904394140028959267)
            ·
              refine ⟨241083376356591210043438901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160722250904394140028959267 241083376356591210043438901)
              ·
                refine ⟨22601566533430425941572397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241083376356591210043438901 22601566533430425941572397)
                ·
                  refine ⟨8475587450036409728089649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22601566533430425941572397 8475587450036409728089649)
                  ·
                    refine ⟨6356690587527307296067237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8475587450036409728089649 6356690587527307296067237)
                    ·
                      refine ⟨1191879485161370118012607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6356690587527307296067237 1191879485161370118012607)
                      ·
                        rfl

theorem cell23_2321177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_2321177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321177 prefixEnd_2321177 := by exact prefixLift 2321177
  have htrace : WordTrace (prefixWord ++ tailWord_2321177) baseStart_2321177 baseEnd_2321177 := by
    simpa [prefixWord, tailWord_2321177, baseEnd_2321177] using wordTrace_append hprefix tailTrace_2321177
  have hstable : (prefixWord ++ tailWord_2321177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321177).length < 2 ^ (prefixWord ++ tailWord_2321177).sum := by decide
  have hdescent : baseEnd_2321177 < baseStart_2321177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321265 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 2, 1, 3]
def baseStart_2321265 : Nat := 118140960795 + 2321265 * 2 ^ 59
def prefixEnd_2321265 : Nat := 4983230072969 + 3 ^ 40 * 2321265 * 2
def baseEnd_2321265 : Nat := 1191924671458965773712203

theorem tailTrace_2321265 : CollatzResearch.WordTrace tailWord_2321265 prefixEnd_2321265 1191924671458965773712203 := by
  unfold tailWord_2321265
  simp only [CollatzResearch.WordTrace]
  refine ⟨84663489935460820344869249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56442326623640546896579499 84663489935460820344869249)
  ·
    refine ⟨63497617451595615258651937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84663489935460820344869249 63497617451595615258651937)
    ·
      refine ⟨47623213088696711443988953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63497617451595615258651937 47623213088696711443988953)
      ·
        refine ⟨35717409816522533582991715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47623213088696711443988953 35717409816522533582991715)
        ·
          refine ⟨53576114724783800374487573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35717409816522533582991715 53576114724783800374487573)
          ·
            refine ⟨2511380377724240642554105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53576114724783800374487573 2511380377724240642554105)
            ·
              refine ⟨1883535283293180481915579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2511380377724240642554105 1883535283293180481915579)
              ·
                refine ⟨2825302924939770722873369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883535283293180481915579 2825302924939770722873369)
                ·
                  refine ⟨2118977193704828042155027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2825302924939770722873369 2118977193704828042155027)
                  ·
                    refine ⟨3178465790557242063232541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2118977193704828042155027 3178465790557242063232541)
                    ·
                      refine ⟨1191924671458965773712203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3178465790557242063232541 1191924671458965773712203)
                      ·
                        rfl

theorem cell23_2321265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_2321265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321265 prefixEnd_2321265 := by exact prefixLift 2321265
  have htrace : WordTrace (prefixWord ++ tailWord_2321265) baseStart_2321265 baseEnd_2321265 := by
    simpa [prefixWord, tailWord_2321265, baseEnd_2321265] using wordTrace_append hprefix tailTrace_2321265
  have hstable : (prefixWord ++ tailWord_2321265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321265).length < 2 ^ (prefixWord ++ tailWord_2321265).sum := by decide
  have hdescent : baseEnd_2321265 < baseStart_2321265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321284 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2321284 : Nat := 118140960795 + 2321284 * 2 ^ 59
def prefixEnd_2321284 : Nat := 4983230072969 + 3 ^ 40 * 2321284 * 2
def baseEnd_2321284 : Nat := 1191934427591401199374615

theorem tailTrace_2321284 : CollatzResearch.WordTrace tailWord_2321284 prefixEnd_2321284 1191934427591401199374615 := by
  unfold tailWord_2321284
  simp only [CollatzResearch.WordTrace]
  refine ⟨42332091461195993294905453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56442788614927991059873937 42332091461195993294905453)
  ·
    refine ⟨15874534297948497485589545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42332091461195993294905453 15874534297948497485589545)
    ·
      refine ⟨11905900723461373114192159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15874534297948497485589545 11905900723461373114192159)
      ·
        refine ⟨17858851085192059671288239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11905900723461373114192159 17858851085192059671288239)
        ·
          refine ⟨26788276627788089506932359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17858851085192059671288239 26788276627788089506932359)
          ·
            refine ⟨40182414941682134260398539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26788276627788089506932359 40182414941682134260398539)
            ·
              refine ⟨60273622412523201390597809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40182414941682134260398539 60273622412523201390597809)
              ·
                refine ⟨45205216809392401042948357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60273622412523201390597809 45205216809392401042948357)
                ·
                  refine ⟨8475978151761075195552817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45205216809392401042948357 8475978151761075195552817)
                  ·
                    refine ⟨6356983613820806396664613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8475978151761075195552817 6356983613820806396664613)
                    ·
                      refine ⟨1191934427591401199374615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6356983613820806396664613 1191934427591401199374615)
                      ·
                        rfl

theorem cell23_2321284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2321284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321284 prefixEnd_2321284 := by exact prefixLift 2321284
  have htrace : WordTrace (prefixWord ++ tailWord_2321284) baseStart_2321284 baseEnd_2321284 := by
    simpa [prefixWord, tailWord_2321284, baseEnd_2321284] using wordTrace_append hprefix tailTrace_2321284
  have hstable : (prefixWord ++ tailWord_2321284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321284).length < 2 ^ (prefixWord ++ tailWord_2321284).sum := by decide
  have hdescent : baseEnd_2321284 < baseStart_2321284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321288 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_2321288 : Nat := 118140960795 + 2321288 * 2 ^ 59
def prefixEnd_2321288 : Nat := 4983230072969 + 3 ^ 40 * 2321288 * 2
def baseEnd_2321288 : Nat := 1191936481514019183724597

theorem tailTrace_2321288 : CollatzResearch.WordTrace tailWord_2321288 prefixEnd_2321288 1191936481514019183724597 := by
  unfold tailWord_2321288
  simp only [CollatzResearch.WordTrace]
  refine ⟨42332164407188747636478259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56442885876251663515304345 42332164407188747636478259)
  ·
    refine ⟨63498246610783121454717389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42332164407188747636478259 63498246610783121454717389)
    ·
      refine ⟨23811842479043670545519021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63498246610783121454717389 23811842479043670545519021)
      ·
        refine ⟨8929440929641376454569633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23811842479043670545519021 8929440929641376454569633)
        ·
          refine ⟨6697080697231032340927225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8929440929641376454569633 6697080697231032340927225)
          ·
            refine ⟨5022810522923274255695419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6697080697231032340927225 5022810522923274255695419)
            ·
              refine ⟨7534215784384911383543129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022810522923274255695419 7534215784384911383543129)
              ·
                refine ⟨5650661838288683537657347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7534215784384911383543129 5650661838288683537657347)
                ·
                  refine ⟨8475992757433025306486021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5650661838288683537657347 8475992757433025306486021)
                  ·
                    refine ⟨1589248642018692244966129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8475992757433025306486021 1589248642018692244966129)
                    ·
                      refine ⟨1191936481514019183724597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589248642018692244966129 1191936481514019183724597)
                      ·
                        rfl

theorem cell23_2321288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_2321288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321288 prefixEnd_2321288 := by exact prefixLift 2321288
  have htrace : WordTrace (prefixWord ++ tailWord_2321288) baseStart_2321288 baseEnd_2321288 := by
    simpa [prefixWord, tailWord_2321288, baseEnd_2321288] using wordTrace_append hprefix tailTrace_2321288
  have hstable : (prefixWord ++ tailWord_2321288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321288).length < 2 ^ (prefixWord ++ tailWord_2321288).sum := by decide
  have hdescent : baseEnd_2321288 < baseStart_2321288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321307 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 13]
def baseStart_2321307 : Nat := 118140960795 + 2321307 * 2 ^ 59
def prefixEnd_2321307 : Nat := 4983230072969 + 3 ^ 40 * 2321307 * 2
def baseEnd_2321307 : Nat := 397315412548818203129003

theorem tailTrace_2321307 : CollatzResearch.WordTrace tailWord_2321307 prefixEnd_2321307 397315412548818203129003 := by
  unfold tailWord_2321307
  simp only [CollatzResearch.WordTrace]
  refine ⟨84665021801308661517898175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56443347867539107678598783 84665021801308661517898175)
  ·
    refine ⟨126997532701962992276847263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84665021801308661517898175 126997532701962992276847263)
    ·
      refine ⟨190496299052944488415270895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126997532701962992276847263 190496299052944488415270895)
      ·
        refine ⟨285744448579416732622906343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190496299052944488415270895 285744448579416732622906343)
        ·
          refine ⟨428616672869125098934359515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285744448579416732622906343 428616672869125098934359515)
          ·
            refine ⟨642925009303687648401539273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428616672869125098934359515 642925009303687648401539273)
            ·
              refine ⟨482193756977765736301154455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642925009303687648401539273 482193756977765736301154455)
              ·
                refine ⟨723290635466648604451731683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482193756977765736301154455 723290635466648604451731683)
                ·
                  refine ⟨1084935953199972906677597525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723290635466648604451731683 1084935953199972906677597525)
                  ·
                    refine ⟨397315412548818203129003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 1084935953199972906677597525 397315412548818203129003)
                    ·
                      rfl

theorem cell23_2321307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 13].length) (baseStart_2321307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321307 prefixEnd_2321307 := by exact prefixLift 2321307
  have htrace : WordTrace (prefixWord ++ tailWord_2321307) baseStart_2321307 baseEnd_2321307 := by
    simpa [prefixWord, tailWord_2321307, baseEnd_2321307] using wordTrace_append hprefix tailTrace_2321307
  have hstable : (prefixWord ++ tailWord_2321307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321307).length < 2 ^ (prefixWord ++ tailWord_2321307).sum := by decide
  have hdescent : baseEnd_2321307 < baseStart_2321307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321341 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_2321341 : Nat := 118140960795 + 2321341 * 2 ^ 59
def prefixEnd_2321341 : Nat := 4983230072969 + 3 ^ 40 * 2321341 * 2
def baseEnd_2321341 : Nat := 397321231996235825453951

theorem tailTrace_2321341 : CollatzResearch.WordTrace tailWord_2321341 prefixEnd_2321341 397321231996235825453951 := by
  unfold tailWord_2321341
  simp only [CollatzResearch.WordTrace]
  refine ⟨84666261883185485324635877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56444174588790323549757251 84666261883185485324635877)
  ·
    refine ⟨15874924103097278498369227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84666261883185485324635877 15874924103097278498369227)
    ·
      refine ⟨23812386154645917747553841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15874924103097278498369227 23812386154645917747553841)
      ·
        refine ⟨17859289615984438310665381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23812386154645917747553841 17859289615984438310665381)
        ·
          refine ⟨3348616802997082183249759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17859289615984438310665381 3348616802997082183249759)
          ·
            refine ⟨5022925204495623274874639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348616802997082183249759 5022925204495623274874639)
            ·
              refine ⟨7534387806743434912311959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022925204495623274874639 7534387806743434912311959)
              ·
                refine ⟨11301581710115152368467939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7534387806743434912311959 11301581710115152368467939)
                ·
                  refine ⟨16952372565172728552701909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11301581710115152368467939 16952372565172728552701909)
                  ·
                    refine ⟨397321231996235825453951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16952372565172728552701909 397321231996235825453951)
                    ·
                      rfl

theorem cell23_2321341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_2321341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321341 prefixEnd_2321341 := by exact prefixLift 2321341
  have htrace : WordTrace (prefixWord ++ tailWord_2321341) baseStart_2321341 baseEnd_2321341 := by
    simpa [prefixWord, tailWord_2321341, baseEnd_2321341] using wordTrace_append hprefix tailTrace_2321341
  have hstable : (prefixWord ++ tailWord_2321341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321341).length < 2 ^ (prefixWord ++ tailWord_2321341).sum := by decide
  have hdescent : baseEnd_2321341 < baseStart_2321341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321361 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 4, 4, 2]
def baseStart_2321361 : Nat := 118140960795 + 2321361 * 2 ^ 59
def prefixEnd_2321361 : Nat := 4983230072969 + 3 ^ 40 * 2321361 * 2
def baseEnd_2321361 : Nat := 1191973965601797398111761

theorem tailTrace_2321361 : CollatzResearch.WordTrace tailWord_2321361 prefixEnd_2321361 1191973965601797398111761 := by
  unfold tailWord_2321361
  simp only [CollatzResearch.WordTrace]
  refine ⟨84666991343113028740363937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56444660895408685826909291 84666991343113028740363937)
  ·
    refine ⟨63500243507334771555272953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84666991343113028740363937 63500243507334771555272953)
    ·
      refine ⟨47625182630501078666454715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63500243507334771555272953 47625182630501078666454715)
      ·
        refine ⟨71437773945751617999682073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47625182630501078666454715 71437773945751617999682073)
        ·
          refine ⟨53578330459313713499761555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71437773945751617999682073 53578330459313713499761555)
          ·
            refine ⟨80367495688970570249642333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53578330459313713499761555 80367495688970570249642333)
            ·
              refine ⟨30137810883363963843615875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80367495688970570249642333 30137810883363963843615875)
              ·
                refine ⟨45206716325045945765423813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30137810883363963843615875 45206716325045945765423813)
                ·
                  refine ⟨8476259310946114831016965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45206716325045945765423813 8476259310946114831016965)
                  ·
                    refine ⟨1589298620802396530815681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8476259310946114831016965 1589298620802396530815681)
                    ·
                      refine ⟨1191973965601797398111761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589298620802396530815681 1191973965601797398111761)
                      ·
                        rfl

theorem cell23_2321361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_2321361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321361 prefixEnd_2321361 := by exact prefixLift 2321361
  have htrace : WordTrace (prefixWord ++ tailWord_2321361) baseStart_2321361 baseEnd_2321361 := by
    simpa [prefixWord, tailWord_2321361, baseEnd_2321361] using wordTrace_append hprefix tailTrace_2321361
  have hstable : (prefixWord ++ tailWord_2321361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321361).length < 2 ^ (prefixWord ++ tailWord_2321361).sum := by decide
  have hdescent : baseEnd_2321361 < baseStart_2321361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321378 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2321378 : Nat := 118140960795 + 2321378 * 2 ^ 59
def prefixEnd_2321378 : Nat := 4983230072969 + 3 ^ 40 * 2321378 * 2
def baseEnd_2321378 : Nat := 1191982694772923831599183

theorem tailTrace_2321378 : CollatzResearch.WordTrace tailWord_2321378 prefixEnd_2321378 1191982694772923831599183 := by
  unfold tailWord_2321378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21166902846012860160933197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56445074256034293762488525 21166902846012860160933197)
  ·
    refine ⟨7937588567254822560349949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21166902846012860160933197 7937588567254822560349949)
    ·
      refine ⟨2976595712720558460131231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7937588567254822560349949 2976595712720558460131231)
      ·
        refine ⟨4464893569080837690196847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2976595712720558460131231 4464893569080837690196847)
        ·
          refine ⟨6697340353621256535295271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4464893569080837690196847 6697340353621256535295271)
          ·
            refine ⟨10046010530431884802942907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6697340353621256535295271 10046010530431884802942907)
            ·
              refine ⟨15069015795647827204414361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10046010530431884802942907 15069015795647827204414361)
              ·
                refine ⟨11301761846735870403310771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15069015795647827204414361 11301761846735870403310771)
                ·
                  refine ⟨16952642770103805604966157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11301761846735870403310771 16952642770103805604966157)
                  ·
                    refine ⟨6357241038788927101862309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16952642770103805604966157 6357241038788927101862309)
                    ·
                      refine ⟨1191982694772923831599183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6357241038788927101862309 1191982694772923831599183)
                      ·
                        rfl

theorem cell23_2321378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2321378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321378 prefixEnd_2321378 := by exact prefixLift 2321378
  have htrace : WordTrace (prefixWord ++ tailWord_2321378) baseStart_2321378 baseEnd_2321378 := by
    simpa [prefixWord, tailWord_2321378, baseEnd_2321378] using wordTrace_append hprefix tailTrace_2321378
  have hstable : (prefixWord ++ tailWord_2321378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321378).length < 2 ^ (prefixWord ++ tailWord_2321378).sum := by decide
  have hdescent : baseEnd_2321378 < baseStart_2321378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321396 : List Nat := [2, 6, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2321396 : Nat := 118140960795 + 2321396 * 2 ^ 59
def prefixEnd_2321396 : Nat := 4983230072969 + 3 ^ 40 * 2321396 * 2
def baseEnd_2321396 : Nat := 132443548602744973463789

theorem tailTrace_2321396 : CollatzResearch.WordTrace tailWord_2321396 prefixEnd_2321396 132443548602744973463789 := by
  unfold tailWord_2321396
  simp only [CollatzResearch.WordTrace]
  refine ⟨42334133948993114858944021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56445511931990819811925361 42334133948993114858944021)
  ·
    refine ⟨1984412528859052259013001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42334133948993114858944021 1984412528859052259013001)
    ·
      refine ⟨1488309396644289194259751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1984412528859052259013001 1488309396644289194259751)
      ·
        refine ⟨2232464094966433791389627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488309396644289194259751 2232464094966433791389627)
        ·
          refine ⟨3348696142449650687084441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232464094966433791389627 3348696142449650687084441)
          ·
            refine ⟨2511522106837238015313331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3348696142449650687084441 2511522106837238015313331)
            ·
              refine ⟨3767283160255857022969997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511522106837238015313331 3767283160255857022969997)
              ·
                refine ⟨1412731185095946383613749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3767283160255857022969997 1412731185095946383613749)
                ·
                  refine ⟨132443548602744973463789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1412731185095946383613749 132443548602744973463789)
                  ·
                    rfl

theorem cell23_2321396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2321396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321396 prefixEnd_2321396 := by exact prefixLift 2321396
  have htrace : WordTrace (prefixWord ++ tailWord_2321396) baseStart_2321396 baseEnd_2321396 := by
    simpa [prefixWord, tailWord_2321396, baseEnd_2321396] using wordTrace_append hprefix tailTrace_2321396
  have hstable : (prefixWord ++ tailWord_2321396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321396).length < 2 ^ (prefixWord ++ tailWord_2321396).sum := by decide
  have hdescent : baseEnd_2321396 < baseStart_2321396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321398 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2321398 : Nat := 118140960795 + 2321398 * 2 ^ 59
def prefixEnd_2321398 : Nat := 4983230072969 + 3 ^ 40 * 2321398 * 2
def baseEnd_2321398 : Nat := 1191992964386013753349091

theorem tailTrace_2321398 : CollatzResearch.WordTrace tailWord_2321398 prefixEnd_2321398 1191992964386013753349091 := by
  unfold tailWord_2321398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5291771302748686503716303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56445560562652656039640565 5291771302748686503716303)
  ·
    refine ⟨7937656954123029755574455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5291771302748686503716303 7937656954123029755574455)
    ·
      refine ⟨11906485431184544633361683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7937656954123029755574455 11906485431184544633361683)
      ·
        refine ⟨17859728146776816950042525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11906485431184544633361683 17859728146776816950042525)
        ·
          refine ⟨6697398055041306356265947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17859728146776816950042525 6697398055041306356265947)
          ·
            refine ⟨10046097082561959534398921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6697398055041306356265947 10046097082561959534398921)
            ·
              refine ⟨7534572811921469650799191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10046097082561959534398921 7534572811921469650799191)
              ·
                refine ⟨11301859217882204476198787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7534572811921469650799191 11301859217882204476198787)
                ·
                  refine ⟨16952788826823306714298181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11301859217882204476198787 16952788826823306714298181)
                  ·
                    refine ⟨3178647905029370008930909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16952788826823306714298181 3178647905029370008930909)
                    ·
                      refine ⟨1191992964386013753349091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3178647905029370008930909 1191992964386013753349091)
                      ·
                        rfl

theorem cell23_2321398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2321398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321398 prefixEnd_2321398 := by exact prefixLift 2321398
  have htrace : WordTrace (prefixWord ++ tailWord_2321398) baseStart_2321398 baseEnd_2321398 := by
    simpa [prefixWord, tailWord_2321398, baseEnd_2321398] using wordTrace_append hprefix tailTrace_2321398
  have hstable : (prefixWord ++ tailWord_2321398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321398).length < 2 ^ (prefixWord ++ tailWord_2321398).sum := by decide
  have hdescent : baseEnd_2321398 < baseStart_2321398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321422 : List Nat := [4, 1, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_2321422 : Nat := 118140960795 + 2321422 * 2 ^ 59
def prefixEnd_2321422 : Nat := 4983230072969 + 3 ^ 40 * 2321422 * 2
def baseEnd_2321422 : Nat := 397335095973907219816327

theorem tailTrace_2321422 : CollatzResearch.WordTrace tailWord_2321422 prefixEnd_2321422 397335095973907219816327 := by
  unfold tailWord_2321422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10583652024486504519791815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56446144130594690772223013 10583652024486504519791815)
  ·
    refine ⟨15875478036729756779687723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10583652024486504519791815 15875478036729756779687723)
    ·
      refine ⟨23813217055094635169531585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15875478036729756779687723 23813217055094635169531585)
      ·
        refine ⟨17859912791320976377148689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23813217055094635169531585 17859912791320976377148689)
        ·
          refine ⟨13394934593490732282861517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17859912791320976377148689 13394934593490732282861517)
          ·
            refine ⟨5023100472559024606073069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13394934593490732282861517 5023100472559024606073069)
            ·
              refine ⟨1883662677209634227277401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5023100472559024606073069 1883662677209634227277401)
              ·
                refine ⟨1412747007907225670458051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1883662677209634227277401 1412747007907225670458051)
                ·
                  refine ⟨2119120511860838505687077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412747007907225670458051 2119120511860838505687077)
                  ·
                    refine ⟨397335095973907219816327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119120511860838505687077 397335095973907219816327)
                    ·
                      rfl

theorem cell23_2321422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_2321422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321422 prefixEnd_2321422 := by exact prefixLift 2321422
  have htrace : WordTrace (prefixWord ++ tailWord_2321422) baseStart_2321422 baseEnd_2321422 := by
    simpa [prefixWord, tailWord_2321422, baseEnd_2321422] using wordTrace_append hprefix tailTrace_2321422
  have hstable : (prefixWord ++ tailWord_2321422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321422).length < 2 ^ (prefixWord ++ tailWord_2321422).sum := by decide
  have hdescent : baseEnd_2321422 < baseStart_2321422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321451 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 4]
def baseStart_2321451 : Nat := 118140960795 + 2321451 * 2 ^ 59
def prefixEnd_2321451 : Nat := 4983230072969 + 3 ^ 40 * 2321451 * 2
def baseEnd_2321451 : Nat := 1192020178860702045986347

theorem tailTrace_2321451 : CollatzResearch.WordTrace tailWord_2321451 prefixEnd_2321451 1192020178860702045986347 := by
  unfold tailWord_2321451
  simp only [CollatzResearch.WordTrace]
  refine ⟨84670273912786974111140207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56446849275191316074093471 84670273912786974111140207)
  ·
    refine ⟨127005410869180461166710311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84670273912786974111140207 127005410869180461166710311)
    ·
      refine ⟨190508116303770691750065467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127005410869180461166710311 190508116303770691750065467)
      ·
        refine ⟨285762174455656037625098201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190508116303770691750065467 285762174455656037625098201)
        ·
          refine ⟨214321630841742028218823651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285762174455656037625098201 214321630841742028218823651)
          ·
            refine ⟨321482446262613042328235477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214321630841742028218823651 321482446262613042328235477)
            ·
              refine ⟨7534744834279993179568019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 321482446262613042328235477 7534744834279993179568019)
              ·
                refine ⟨11302117251419989769352029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7534744834279993179568019 11302117251419989769352029)
                ·
                  refine ⟨4238293969282496163507011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11302117251419989769352029 4238293969282496163507011)
                  ·
                    refine ⟨6357440953923744245260517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4238293969282496163507011 6357440953923744245260517)
                    ·
                      refine ⟨1192020178860702045986347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6357440953923744245260517 1192020178860702045986347)
                      ·
                        rfl

theorem cell23_2321451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 4].length) (baseStart_2321451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321451 prefixEnd_2321451 := by exact prefixLift 2321451
  have htrace : WordTrace (prefixWord ++ tailWord_2321451) baseStart_2321451 baseEnd_2321451 := by
    simpa [prefixWord, tailWord_2321451, baseEnd_2321451] using wordTrace_append hprefix tailTrace_2321451
  have hstable : (prefixWord ++ tailWord_2321451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321451).length < 2 ^ (prefixWord ++ tailWord_2321451).sum := by decide
  have hdescent : baseEnd_2321451 < baseStart_2321451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321465 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 1, 5]
def baseStart_2321465 : Nat := 118140960795 + 2321465 * 2 ^ 59
def prefixEnd_2321465 : Nat := 4983230072969 + 3 ^ 40 * 2321465 * 2
def baseEnd_2321465 : Nat := 397342455863288330403761

theorem tailTrace_2321465 : CollatzResearch.WordTrace tailWord_2321465 prefixEnd_2321465 397342455863288330403761 := by
  unfold tailWord_2321465
  simp only [CollatzResearch.WordTrace]
  refine ⟨84670784534736254502149849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56447189689824169668099899 84670784534736254502149849)
  ·
    refine ⟨63503088401052190876612387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84670784534736254502149849 63503088401052190876612387)
    ·
      refine ⟨95254632601578286314918581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63503088401052190876612387 95254632601578286314918581)
      ·
        refine ⟨8930121806397964342023617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95254632601578286314918581 8930121806397964342023617)
        ·
          refine ⟨6697591354798473256517713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8930121806397964342023617 6697591354798473256517713)
          ·
            refine ⟨5023193516098854942388285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6697591354798473256517713 5023193516098854942388285)
            ·
              refine ⟨1883697568537070603395607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5023193516098854942388285 1883697568537070603395607)
              ·
                refine ⟨2825546352805605905093411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883697568537070603395607 2825546352805605905093411)
                ·
                  refine ⟨4238319529208408857640117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825546352805605905093411 4238319529208408857640117)
                  ·
                    refine ⟨397342455863288330403761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4238319529208408857640117 397342455863288330403761)
                    ·
                      rfl

theorem cell23_2321465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 5].length) (baseStart_2321465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321465 prefixEnd_2321465 := by exact prefixLift 2321465
  have htrace : WordTrace (prefixWord ++ tailWord_2321465) baseStart_2321465 baseEnd_2321465 := by
    simpa [prefixWord, tailWord_2321465, baseEnd_2321465] using wordTrace_append hprefix tailTrace_2321465
  have hstable : (prefixWord ++ tailWord_2321465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321465).length < 2 ^ (prefixWord ++ tailWord_2321465).sum := by decide
  have hdescent : baseEnd_2321465 < baseStart_2321465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321479 : List Nat := [1, 1, 4, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_2321479 : Nat := 118140960795 + 2321479 * 2 ^ 59
def prefixEnd_2321479 : Nat := 4983230072969 + 3 ^ 40 * 2321479 * 2
def baseEnd_2321479 : Nat := 1192034556319027936436219

theorem tailTrace_2321479 : CollatzResearch.WordTrace tailWord_2321479 prefixEnd_2321479 1192034556319027936436219 := by
  unfold tailWord_2321479
  simp only [CollatzResearch.WordTrace]
  refine ⟨84671295156685534893159491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56447530104457023262106327 84671295156685534893159491)
  ·
    refine ⟨127006942735028302339739237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84671295156685534893159491 127006942735028302339739237)
    ·
      refine ⟨23813801762817806688701107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127006942735028302339739237 23813801762817806688701107)
      ·
        refine ⟨35720702644226710033051661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23813801762817806688701107 35720702644226710033051661)
        ·
          refine ⟨13395263491585016262394373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35720702644226710033051661 13395263491585016262394373)
          ·
            refine ⟨2511611904672190549198945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13395263491585016262394373 2511611904672190549198945)
            ·
              refine ⟨1883708928504142911899209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2511611904672190549198945 1883708928504142911899209)
              ·
                refine ⟨1412781696378107183924407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1883708928504142911899209 1412781696378107183924407)
                ·
                  refine ⟨2119172544567160775886611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412781696378107183924407 2119172544567160775886611)
                  ·
                    refine ⟨3178758816850741163829917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2119172544567160775886611 3178758816850741163829917)
                    ·
                      refine ⟨1192034556319027936436219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3178758816850741163829917 1192034556319027936436219)
                      ·
                        rfl

theorem cell23_2321479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_2321479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321479 prefixEnd_2321479 := by exact prefixLift 2321479
  have htrace : WordTrace (prefixWord ++ tailWord_2321479) baseStart_2321479 baseEnd_2321479 := by
    simpa [prefixWord, tailWord_2321479, baseEnd_2321479] using wordTrace_append hprefix tailTrace_2321479
  have hstable : (prefixWord ++ tailWord_2321479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321479).length < 2 ^ (prefixWord ++ tailWord_2321479).sum := by decide
  have hdescent : baseEnd_2321479 < baseStart_2321479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321502 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2321502 : Nat := 118140960795 + 2321502 * 2 ^ 59
def prefixEnd_2321502 : Nat := 4983230072969 + 3 ^ 40 * 2321502 * 2
def baseEnd_2321502 : Nat := 1192046366374081346448613

theorem tailTrace_2321502 : CollatzResearch.WordTrace tailWord_2321502 prefixEnd_2321502 1192046366374081346448613 := by
  unfold tailWord_2321502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10584016754450276227655845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56448089357068139880831173 10584016754450276227655845)
  ·
    refine ⟨1984503141459426792685471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10584016754450276227655845 1984503141459426792685471)
    ·
      refine ⟨2976754712189140189028207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1984503141459426792685471 2976754712189140189028207)
      ·
        refine ⟨4465132068283710283542311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2976754712189140189028207 4465132068283710283542311)
        ·
          refine ⟨6697698102425565425313467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4465132068283710283542311 6697698102425565425313467)
          ·
            refine ⟨10046547153638348137970201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6697698102425565425313467 10046547153638348137970201)
            ·
              refine ⟨7534910365228761103477651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10046547153638348137970201 7534910365228761103477651)
              ·
                refine ⟨11302365547843141655216477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7534910365228761103477651 11302365547843141655216477)
                ·
                  refine ⟨4238387080441178120706179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11302365547843141655216477 4238387080441178120706179)
                  ·
                    refine ⟨6357580620661767181059269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4238387080441178120706179 6357580620661767181059269)
                    ·
                      refine ⟨1192046366374081346448613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6357580620661767181059269 1192046366374081346448613)
                      ·
                        rfl

theorem cell23_2321502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2321502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321502 prefixEnd_2321502 := by exact prefixLift 2321502
  have htrace : WordTrace (prefixWord ++ tailWord_2321502) baseStart_2321502 baseEnd_2321502 := by
    simpa [prefixWord, tailWord_2321502, baseEnd_2321502] using wordTrace_append hprefix tailTrace_2321502
  have hstable : (prefixWord ++ tailWord_2321502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321502).length < 2 ^ (prefixWord ++ tailWord_2321502).sum := by decide
  have hdescent : baseEnd_2321502 < baseStart_2321502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321562 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2321562 : Nat := 118140960795 + 2321562 * 2 ^ 59
def prefixEnd_2321562 : Nat := 4983230072969 + 3 ^ 40 * 2321562 * 2
def baseEnd_2321562 : Nat := 1192077175213351111698337

theorem tailTrace_2321562 : CollatzResearch.WordTrace tailWord_2321562 prefixEnd_2321562 1192077175213351111698337 := by
  unfold tailWord_2321562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21168580603846210017107735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56449548276923226712287293 21168580603846210017107735)
  ·
    refine ⟨31752870905769315025661603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21168580603846210017107735 31752870905769315025661603)
    ·
      refine ⟨47629306358653972538492405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31752870905769315025661603 47629306358653972538492405)
      ·
        refine ⟨4465247471123809925483663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47629306358653972538492405 4465247471123809925483663)
        ·
          refine ⟨6697871206685714888225495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4465247471123809925483663 6697871206685714888225495)
          ·
            refine ⟨10046806810028572332338243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6697871206685714888225495 10046806810028572332338243)
            ·
              refine ⟨15070210215042858498507365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10046806810028572332338243 15070210215042858498507365)
              ·
                refine ⟨2825664415320535968470131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15070210215042858498507365 2825664415320535968470131)
                ·
                  refine ⟨4238496622980803952705197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825664415320535968470131 4238496622980803952705197)
                  ·
                    refine ⟨1589436233617801482264449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4238496622980803952705197 1589436233617801482264449)
                    ·
                      refine ⟨1192077175213351111698337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589436233617801482264449 1192077175213351111698337)
                      ·
                        rfl

theorem cell23_2321562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2321562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321562 prefixEnd_2321562 := by exact prefixLift 2321562
  have htrace : WordTrace (prefixWord ++ tailWord_2321562) baseStart_2321562 baseEnd_2321562 := by
    simpa [prefixWord, tailWord_2321562, baseEnd_2321562] using wordTrace_append hprefix tailTrace_2321562
  have hstable : (prefixWord ++ tailWord_2321562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321562).length < 2 ^ (prefixWord ++ tailWord_2321562).sum := by decide
  have hdescent : baseEnd_2321562 < baseStart_2321562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321571 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 4]
def baseStart_2321571 : Nat := 118140960795 + 2321571 * 2 ^ 59
def prefixEnd_2321571 : Nat := 4983230072969 + 3 ^ 40 * 2321571 * 2
def baseEnd_2321571 : Nat := 1192081796539241576485795

theorem tailTrace_2321571 : CollatzResearch.WordTrace tailWord_2321571 prefixEnd_2321571 1192081796539241576485795 := by
  unfold tailWord_2321571
  simp only [CollatzResearch.WordTrace]
  refine ⟨84674650672352234605508567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56449767114901489737005711 84674650672352234605508567)
  ·
    refine ⟨127011976008528351908262851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84674650672352234605508567 127011976008528351908262851)
    ·
      refine ⟨190517964012792527862394277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127011976008528351908262851 190517964012792527862394277)
      ·
        refine ⟨35722118252398598974198927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190517964012792527862394277 35722118252398598974198927)
        ·
          refine ⟨53583177378597898461298391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35722118252398598974198927 53583177378597898461298391)
          ·
            refine ⟨80374766067896847691947587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53583177378597898461298391 80374766067896847691947587)
            ·
              refine ⟨120562149101845271537921381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80374766067896847691947587 120562149101845271537921381)
              ·
                refine ⟨22605402956595988413360259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120562149101845271537921381 22605402956595988413360259)
                ·
                  refine ⟨33908104434893982620040389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22605402956595988413360259 33908104434893982620040389)
                  ·
                    refine ⟨6357769581542621741257573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33908104434893982620040389 6357769581542621741257573)
                    ·
                      refine ⟨1192081796539241576485795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6357769581542621741257573 1192081796539241576485795)
                      ·
                        rfl

theorem cell23_2321571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_2321571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321571 prefixEnd_2321571 := by exact prefixLift 2321571
  have htrace : WordTrace (prefixWord ++ tailWord_2321571) baseStart_2321571 baseEnd_2321571 := by
    simpa [prefixWord, tailWord_2321571, baseEnd_2321571] using wordTrace_append hprefix tailTrace_2321571
  have hstable : (prefixWord ++ tailWord_2321571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321571).length < 2 ^ (prefixWord ++ tailWord_2321571).sum := by decide
  have hdescent : baseEnd_2321571 < baseStart_2321571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321591 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_2321591 : Nat := 118140960795 + 2321591 * 2 ^ 59
def prefixEnd_2321591 : Nat := 4983230072969 + 3 ^ 40 * 2321591 * 2
def baseEnd_2321591 : Nat := 1192092066152331498235703

theorem tailTrace_2321591 : CollatzResearch.WordTrace tailWord_2321591 prefixEnd_2321591 1192092066152331498235703 := by
  unfold tailWord_2321591
  simp only [CollatzResearch.WordTrace]
  refine ⟨84675380132279778021236627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56450253421519852014157751 84675380132279778021236627)
  ·
    refine ⟨127013070198419667031854941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84675380132279778021236627 127013070198419667031854941)
    ·
      refine ⟨47629901324407375136945603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127013070198419667031854941 47629901324407375136945603)
      ·
        refine ⟨71444851986611062705418405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47629901324407375136945603 71444851986611062705418405)
        ·
          refine ⟨13395909747489574257265951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71444851986611062705418405 13395909747489574257265951)
          ·
            refine ⟨20093864621234361385898927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13395909747489574257265951 20093864621234361385898927)
            ·
              refine ⟨30140796931851542078848391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20093864621234361385898927 30140796931851542078848391)
              ·
                refine ⟨45211195397777313118272587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30140796931851542078848391 45211195397777313118272587)
                ·
                  refine ⟨67816793096665969677408881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45211195397777313118272587 67816793096665969677408881)
                  ·
                    refine ⟨50862594822499477258056661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67816793096665969677408881 50862594822499477258056661)
                    ·
                      refine ⟨1192092066152331498235703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50862594822499477258056661 1192092066152331498235703)
                      ·
                        rfl

theorem cell23_2321591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_2321591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321591 prefixEnd_2321591 := by exact prefixLift 2321591
  have htrace : WordTrace (prefixWord ++ tailWord_2321591) baseStart_2321591 baseEnd_2321591 := by
    simpa [prefixWord, tailWord_2321591, baseEnd_2321591] using wordTrace_append hprefix tailTrace_2321591
  have hstable : (prefixWord ++ tailWord_2321591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321591).length < 2 ^ (prefixWord ++ tailWord_2321591).sum := by decide
  have hdescent : baseEnd_2321591 < baseStart_2321591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321608 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_2321608 : Nat := 118140960795 + 2321608 * 2 ^ 59
def prefixEnd_2321608 : Nat := 4983230072969 + 3 ^ 40 * 2321608 * 2
def baseEnd_2321608 : Nat := 1192100795323457931723125

theorem tailTrace_2321608 : CollatzResearch.WordTrace tailWord_2321608 prefixEnd_2321608 1192100795323457931723125 := by
  unfold tailWord_2321608
  simp only [CollatzResearch.WordTrace]
  refine ⟨42338000086609094962302739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56450666782145459949736985 42338000086609094962302739)
  ·
    refine ⟨63507000129913642443454109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42338000086609094962302739 63507000129913642443454109)
    ·
      refine ⟨23815125048717615916295291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63507000129913642443454109 23815125048717615916295291)
      ·
        refine ⟨35722687573076423874442937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23815125048717615916295291 35722687573076423874442937)
        ·
          refine ⟨26792015679807317905832203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35722687573076423874442937 26792015679807317905832203)
          ·
            refine ⟨40188023519710976858748305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26792015679807317905832203 40188023519710976858748305)
            ·
              refine ⟨30141017639783232644061229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40188023519710976858748305 30141017639783232644061229)
              ·
                refine ⟨11302881614918712241522961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30141017639783232644061229 11302881614918712241522961)
                ·
                  refine ⟨8477161211189034181142221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11302881614918712241522961 8477161211189034181142221)
                  ·
                    refine ⟨3178935454195887817928333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8477161211189034181142221 3178935454195887817928333)
                    ·
                      refine ⟨1192100795323457931723125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3178935454195887817928333 1192100795323457931723125)
                      ·
                        rfl

theorem cell23_2321608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_2321608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321608 prefixEnd_2321608 := by exact prefixLift 2321608
  have htrace : WordTrace (prefixWord ++ tailWord_2321608) baseStart_2321608 baseEnd_2321608 := by
    simpa [prefixWord, tailWord_2321608, baseEnd_2321608] using wordTrace_append hprefix tailTrace_2321608
  have hstable : (prefixWord ++ tailWord_2321608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321608).length < 2 ^ (prefixWord ++ tailWord_2321608).sum := by decide
  have hdescent : baseEnd_2321608 < baseStart_2321608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321611 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 1, 7]
def baseStart_2321611 : Nat := 118140960795 + 2321611 * 2 ^ 59
def prefixEnd_2321611 : Nat := 4983230072969 + 3 ^ 40 * 2321611 * 2
def baseEnd_2321611 : Nat := 397367445255140473328537

theorem tailTrace_2321611 : CollatzResearch.WordTrace tailWord_2321611 prefixEnd_2321611 397367445255140473328537 := by
  unfold tailWord_2321611
  simp only [CollatzResearch.WordTrace]
  refine ⟨84676109592207321436964687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56450739728138214291309791 84676109592207321436964687)
  ·
    refine ⟨127014164388310982155447031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84676109592207321436964687 127014164388310982155447031)
    ·
      refine ⟨190521246582466473233170547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127014164388310982155447031 190521246582466473233170547)
      ·
        refine ⟨285781869873699709849755821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190521246582466473233170547 285781869873699709849755821)
        ·
          refine ⟨107168201202637391193658433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285781869873699709849755821 107168201202637391193658433)
          ·
            refine ⟨80376150901978043395243825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107168201202637391193658433 80376150901978043395243825)
            ·
              refine ⟨60282113176483532546432869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80376150901978043395243825 60282113176483532546432869)
              ·
                refine ⟨11302896220590662352456163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60282113176483532546432869 11302896220590662352456163)
                ·
                  refine ⟨16954344330885993528684245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11302896220590662352456163 16954344330885993528684245)
                  ·
                    refine ⟨397367445255140473328537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16954344330885993528684245 397367445255140473328537)
                    ·
                      rfl

theorem cell23_2321611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 7].length) (baseStart_2321611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321611 prefixEnd_2321611 := by exact prefixLift 2321611
  have htrace : WordTrace (prefixWord ++ tailWord_2321611) baseStart_2321611 baseEnd_2321611 := by
    simpa [prefixWord, tailWord_2321611, baseEnd_2321611] using wordTrace_append hprefix tailTrace_2321611
  have hstable : (prefixWord ++ tailWord_2321611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321611).length < 2 ^ (prefixWord ++ tailWord_2321611).sum := by decide
  have hdescent : baseEnd_2321611 < baseStart_2321611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321613 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_2321613 : Nat := 118140960795 + 2321613 * 2 ^ 59
def prefixEnd_2321613 : Nat := 4983230072969 + 3 ^ 40 * 2321613 * 2
def baseEnd_2321613 : Nat := 1192103362726730412160603

theorem tailTrace_2321613 : CollatzResearch.WordTrace tailWord_2321613 prefixEnd_2321613 1192103362726730412160603 := by
  unfold tailWord_2321613
  simp only [CollatzResearch.WordTrace]
  refine ⟨84676182538200075778537493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56450788358800050519024995 84676182538200075778537493)
  ·
    refine ⟨3969196056478128552118945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84676182538200075778537493 3969196056478128552118945)
    ·
      refine ⟨2976897042358596414089209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3969196056478128552118945 2976897042358596414089209)
      ·
        refine ⟨2232672781768947310566907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2976897042358596414089209 2232672781768947310566907)
        ·
          refine ⟨3349009172653420965850361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232672781768947310566907 3349009172653420965850361)
          ·
            refine ⟨2511756879490065724387771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3349009172653420965850361 2511756879490065724387771)
            ·
              refine ⟨3767635319235098586581657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511756879490065724387771 3767635319235098586581657)
              ·
                refine ⟨2825726489426323939936243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3767635319235098586581657 2825726489426323939936243)
                ·
                  refine ⟨4238589734139485909904365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825726489426323939936243 4238589734139485909904365)
                  ·
                    refine ⟨1589471150302307216214137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4238589734139485909904365 1589471150302307216214137)
                    ·
                      refine ⟨1192103362726730412160603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589471150302307216214137 1192103362726730412160603)
                      ·
                        rfl

theorem cell23_2321613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_2321613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321613 prefixEnd_2321613 := by exact prefixLift 2321613
  have htrace : WordTrace (prefixWord ++ tailWord_2321613) baseStart_2321613 baseEnd_2321613 := by
    simpa [prefixWord, tailWord_2321613, baseEnd_2321613] using wordTrace_append hprefix tailTrace_2321613
  have hstable : (prefixWord ++ tailWord_2321613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321613).length < 2 ^ (prefixWord ++ tailWord_2321613).sum := by decide
  have hdescent : baseEnd_2321613 < baseStart_2321613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321645 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2321645 : Nat := 118140960795 + 2321645 * 2 ^ 59
def prefixEnd_2321645 : Nat := 4983230072969 + 3 ^ 40 * 2321645 * 2
def baseEnd_2321645 : Nat := 397373264702558095653485

theorem tailTrace_2321645 : CollatzResearch.WordTrace tailWord_2321645 prefixEnd_2321645 397373264702558095653485 := by
  unfold tailWord_2321645
  simp only [CollatzResearch.WordTrace]
  refine ⟨84677349674084145243702389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56451566449389430162468259 84677349674084145243702389)
  ·
    refine ⟨7938501531945388616597099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84677349674084145243702389 7938501531945388616597099)
    ·
      refine ⟨11907752297918082924895649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7938501531945388616597099 11907752297918082924895649)
      ·
        refine ⟨8930814223438562193671737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11907752297918082924895649 8930814223438562193671737)
        ·
          refine ⟨6698110667578921645253803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8930814223438562193671737 6698110667578921645253803)
          ·
            refine ⟨10047166001368382467880705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6698110667578921645253803 10047166001368382467880705)
            ·
              refine ⟨7535374501026286850910529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10047166001368382467880705 7535374501026286850910529)
              ·
                refine ⟨5651530875769715138182897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7535374501026286850910529 5651530875769715138182897)
                ·
                  refine ⟨4238648156827286353637173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5651530875769715138182897 4238648156827286353637173)
                  ·
                    refine ⟨397373264702558095653485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4238648156827286353637173 397373264702558095653485)
                    ·
                      rfl

theorem cell23_2321645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2321645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321645 prefixEnd_2321645 := by exact prefixLift 2321645
  have htrace : WordTrace (prefixWord ++ tailWord_2321645) baseStart_2321645 baseEnd_2321645 := by
    simpa [prefixWord, tailWord_2321645, baseEnd_2321645] using wordTrace_append hprefix tailTrace_2321645
  have hstable : (prefixWord ++ tailWord_2321645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321645).length < 2 ^ (prefixWord ++ tailWord_2321645).sum := by decide
  have hdescent : baseEnd_2321645 < baseStart_2321645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321665 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_2321665 : Nat := 118140960795 + 2321665 * 2 ^ 59
def prefixEnd_2321665 : Nat := 4983230072969 + 3 ^ 40 * 2321665 * 2
def baseEnd_2321665 : Nat := 1192130063720764208710363

theorem tailTrace_2321665 : CollatzResearch.WordTrace tailWord_2321665 prefixEnd_2321665 1192130063720764208710363 := by
  unfold tailWord_2321665
  simp only [CollatzResearch.WordTrace]
  refine ⟨84678079134011688659430449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56452052756007792439620299 84678079134011688659430449)
  ·
    refine ⟨63508559350508766494572837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84678079134011688659430449 63508559350508766494572837)
    ·
      refine ⟨11907854878220393717732407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63508559350508766494572837 11907854878220393717732407)
      ·
        refine ⟨17861782317330590576598611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11907854878220393717732407 17861782317330590576598611)
        ·
          refine ⟨26792673475995885864897917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17861782317330590576598611 26792673475995885864897917)
          ·
            refine ⟨10047252553498457199336719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26792673475995885864897917 10047252553498457199336719)
            ·
              refine ⟨15070878830247685799005079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10047252553498457199336719 15070878830247685799005079)
              ·
                refine ⟨22606318245371528698507619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15070878830247685799005079 22606318245371528698507619)
                ·
                  refine ⟨33909477368057293047761429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22606318245371528698507619 33909477368057293047761429)
                  ·
                    refine ⟨1589506751627685611613817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33909477368057293047761429 1589506751627685611613817)
                    ·
                      refine ⟨1192130063720764208710363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589506751627685611613817 1192130063720764208710363)
                      ·
                        rfl

theorem cell23_2321665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_2321665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321665 prefixEnd_2321665 := by exact prefixLift 2321665
  have htrace : WordTrace (prefixWord ++ tailWord_2321665) baseStart_2321665 baseEnd_2321665 := by
    simpa [prefixWord, tailWord_2321665, baseEnd_2321665] using wordTrace_append hprefix tailTrace_2321665
  have hstable : (prefixWord ++ tailWord_2321665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321665).length < 2 ^ (prefixWord ++ tailWord_2321665).sum := by decide
  have hdescent : baseEnd_2321665 < baseStart_2321665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321675 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 3, 4]
def baseStart_2321675 : Nat := 118140960795 + 2321675 * 2 ^ 59
def prefixEnd_2321675 : Nat := 4983230072969 + 3 ^ 40 * 2321675 * 2
def baseEnd_2321675 : Nat := 397378399509103056528439

theorem tailTrace_2321675 : CollatzResearch.WordTrace tailWord_2321675 prefixEnd_2321675 397378399509103056528439 := by
  unfold tailWord_2321675
  simp only [CollatzResearch.WordTrace]
  refine ⟨84678443863975460367294479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56452295909316973578196319 84678443863975460367294479)
  ·
    refine ⟨127017665795963190550941719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84678443863975460367294479 127017665795963190550941719)
    ·
      refine ⟨190526498693944785826412579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127017665795963190550941719 190526498693944785826412579)
      ·
        refine ⟨285789748040917178739618869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190526498693944785826412579 285789748040917178739618869)
        ·
          refine ⟨26792788878835985506839269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285789748040917178739618869 26792788878835985506839269)
          ·
            refine ⟨5023647914781747282532363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26792788878835985506839269 5023647914781747282532363)
            ·
              refine ⟨7535471872172620923798545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5023647914781747282532363 7535471872172620923798545)
              ·
                refine ⟨5651603904129465692848909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7535471872172620923798545 5651603904129465692848909)
                ·
                  refine ⟨2119351464048549634818341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5651603904129465692848909 2119351464048549634818341)
                  ·
                    refine ⟨397378399509103056528439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119351464048549634818341 397378399509103056528439)
                    ·
                      rfl

theorem cell23_2321675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 4].length) (baseStart_2321675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321675 prefixEnd_2321675 := by exact prefixLift 2321675
  have htrace : WordTrace (prefixWord ++ tailWord_2321675) baseStart_2321675 baseEnd_2321675 := by
    simpa [prefixWord, tailWord_2321675, baseEnd_2321675] using wordTrace_append hprefix tailTrace_2321675
  have hstable : (prefixWord ++ tailWord_2321675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321675).length < 2 ^ (prefixWord ++ tailWord_2321675).sum := by decide
  have hdescent : baseEnd_2321675 < baseStart_2321675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321692 : List Nat := [2, 2, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_2321692 : Nat := 118140960795 + 2321692 * 2 ^ 59
def prefixEnd_2321692 : Nat := 4983230072969 + 3 ^ 40 * 2321692 * 2
def baseEnd_2321692 : Nat := 397381309232811867690913

theorem tailTrace_2321692 : CollatzResearch.WordTrace tailWord_2321692 prefixEnd_2321692 397381309232811867690913 := by
  unfold tailWord_2321692
  simp only [CollatzResearch.WordTrace]
  refine ⟨42339531952456936135331665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56452709269942581513775553 42339531952456936135331665)
  ·
    refine ⟨31754648964342702101498749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42339531952456936135331665 31754648964342702101498749)
    ·
      refine ⟨11907993361628513288062031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31754648964342702101498749 11907993361628513288062031)
      ·
        refine ⟨17861990042442769932093047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11907993361628513288062031 17861990042442769932093047)
        ·
          refine ⟨26792985063664154898139571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17861990042442769932093047 26792985063664154898139571)
          ·
            refine ⟨40189477595496232347209357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26792985063664154898139571 40189477595496232347209357)
            ·
              refine ⟨15071054098311087130203509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40189477595496232347209357 15071054098311087130203509)
              ·
                refine ⟨1412911321716664418456579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15071054098311087130203509 1412911321716664418456579)
                ·
                  refine ⟨2119366982574996627684869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412911321716664418456579 2119366982574996627684869)
                  ·
                    refine ⟨397381309232811867690913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119366982574996627684869 397381309232811867690913)
                    ·
                      rfl

theorem cell23_2321692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_2321692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321692 prefixEnd_2321692 := by exact prefixLift 2321692
  have htrace : WordTrace (prefixWord ++ tailWord_2321692) baseStart_2321692 baseEnd_2321692 := by
    simpa [prefixWord, tailWord_2321692, baseEnd_2321692] using wordTrace_append hprefix tailTrace_2321692
  have hstable : (prefixWord ++ tailWord_2321692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321692).length < 2 ^ (prefixWord ++ tailWord_2321692).sum := by decide
  have hdescent : baseEnd_2321692 < baseStart_2321692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321709 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2321709 : Nat := 118140960795 + 2321709 * 2 ^ 59
def prefixEnd_2321709 : Nat := 4983230072969 + 3 ^ 40 * 2321709 * 2
def baseEnd_2321709 : Nat := 397384218956520678853387

theorem tailTrace_2321709 : CollatzResearch.WordTrace tailWord_2321709 prefixEnd_2321709 397384218956520678853387 := by
  unfold tailWord_2321709
  simp only [CollatzResearch.WordTrace]
  refine ⟨84679683945852284174032181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56453122630568189449354787 84679683945852284174032181)
  ·
    refine ⟨7938720369923651641315517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84679683945852284174032181 7938720369923651641315517)
    ·
      refine ⟨2977020138721369365493319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7938720369923651641315517 2977020138721369365493319)
      ·
        refine ⟨4465530208082054048239979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2977020138721369365493319 4465530208082054048239979)
        ·
          refine ⟨6698295312123081072359969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4465530208082054048239979 6698295312123081072359969)
          ·
            refine ⟨5023721484092310804269977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6698295312123081072359969 5023721484092310804269977)
            ·
              refine ⟨3767791113069233103202483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5023721484092310804269977 3767791113069233103202483)
              ·
                refine ⟨5651686669603849654803725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767791113069233103202483 5651686669603849654803725)
                ·
                  refine ⟨2119382501101443620551397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5651686669603849654803725 2119382501101443620551397)
                  ·
                    refine ⟨397384218956520678853387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119382501101443620551397 397384218956520678853387)
                    ·
                      rfl

theorem cell23_2321709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2321709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321709 prefixEnd_2321709 := by exact prefixLift 2321709
  have htrace : WordTrace (prefixWord ++ tailWord_2321709) baseStart_2321709 baseEnd_2321709 := by
    simpa [prefixWord, tailWord_2321709, baseEnd_2321709] using wordTrace_append hprefix tailTrace_2321709
  have hstable : (prefixWord ++ tailWord_2321709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321709).length < 2 ^ (prefixWord ++ tailWord_2321709).sum := by decide
  have hdescent : baseEnd_2321709 < baseStart_2321709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321735 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 1, 5]
def baseStart_2321735 : Nat := 118140960795 + 2321735 * 2 ^ 59
def prefixEnd_2321735 : Nat := 4983230072969 + 3 ^ 40 * 2321735 * 2
def baseEnd_2321735 : Nat := 397388669122192978278347

theorem tailTrace_2321735 : CollatzResearch.WordTrace tailWord_2321735 prefixEnd_2321735 397388669122192978278347 := by
  unfold tailWord_2321735
  simp only [CollatzResearch.WordTrace]
  refine ⟨84680632243758090614478659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56453754829172060409652439 84680632243758090614478659)
  ·
    refine ⟨127020948365637135921717989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84680632243758090614478659 127020948365637135921717989)
    ·
      refine ⟨23816427818556962985322123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127020948365637135921717989 23816427818556962985322123)
      ·
        refine ⟨35724641727835444477983185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23816427818556962985322123 35724641727835444477983185)
        ·
          refine ⟨26793481295876583358487389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35724641727835444477983185 26793481295876583358487389)
          ·
            refine ⟨10047555485953718759432771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26793481295876583358487389 10047555485953718759432771)
            ·
              refine ⟨15071333228930578139149157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10047555485953718759432771 15071333228930578139149157)
              ·
                refine ⟨2825874980424483401090467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15071333228930578139149157 2825874980424483401090467)
                ·
                  refine ⟨4238812470636725101635701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825874980424483401090467 4238812470636725101635701)
                  ·
                    refine ⟨397388669122192978278347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4238812470636725101635701 397388669122192978278347)
                    ·
                      rfl

theorem cell23_2321735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_2321735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321735 prefixEnd_2321735 := by exact prefixLift 2321735
  have htrace : WordTrace (prefixWord ++ tailWord_2321735) baseStart_2321735 baseEnd_2321735 := by
    simpa [prefixWord, tailWord_2321735, baseEnd_2321735] using wordTrace_append hprefix tailTrace_2321735
  have hstable : (prefixWord ++ tailWord_2321735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321735).length < 2 ^ (prefixWord ++ tailWord_2321735).sum := by decide
  have hdescent : baseEnd_2321735 < baseStart_2321735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321738 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_2321738 : Nat := 118140960795 + 2321738 * 2 ^ 59
def prefixEnd_2321738 : Nat := 4983230072969 + 3 ^ 40 * 2321738 * 2
def baseEnd_2321738 : Nat := 1192167547808542423097527

theorem tailTrace_2321738 : CollatzResearch.WordTrace tailWord_2321738 prefixEnd_2321738 1192167547808542423097527 := by
  unfold tailWord_2321738
  simp only [CollatzResearch.WordTrace]
  refine ⟨21170185415686805531709467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56453827775164814751225245 21170185415686805531709467)
  ·
    refine ⟨31755278123530208297564201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21170185415686805531709467 31755278123530208297564201)
    ·
      refine ⟨23816458592647656223173151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31755278123530208297564201 23816458592647656223173151)
      ·
        refine ⟨35724687888971484334759727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23816458592647656223173151 35724687888971484334759727)
        ·
          refine ⟨53587031833457226502139591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35724687888971484334759727 53587031833457226502139591)
          ·
            refine ⟨80380547750185839753209387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53587031833457226502139591 80380547750185839753209387)
            ·
              refine ⟨120570821625278759629814081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80380547750185839753209387 120570821625278759629814081)
              ·
                refine ⟨90428116218959069722360561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120570821625278759629814081 90428116218959069722360561)
                ·
                  refine ⟨67821087164219302291770421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90428116218959069722360561 67821087164219302291770421)
                  ·
                    refine ⟨6358226921645559589853477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67821087164219302291770421 6358226921645559589853477)
                    ·
                      refine ⟨1192167547808542423097527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6358226921645559589853477 1192167547808542423097527)
                      ·
                        rfl

theorem cell23_2321738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_2321738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321738 prefixEnd_2321738 := by exact prefixLift 2321738
  have htrace : WordTrace (prefixWord ++ tailWord_2321738) baseStart_2321738 baseEnd_2321738 := by
    simpa [prefixWord, tailWord_2321738, baseEnd_2321738] using wordTrace_append hprefix tailTrace_2321738
  have hstable : (prefixWord ++ tailWord_2321738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321738).length < 2 ^ (prefixWord ++ tailWord_2321738).sum := by decide
  have hdescent : baseEnd_2321738 < baseStart_2321738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321742 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_2321742 : Nat := 118140960795 + 2321742 * 2 ^ 59
def prefixEnd_2321742 : Nat := 4983230072969 + 3 ^ 40 * 2321742 * 2
def baseEnd_2321742 : Nat := 1192169601731160407447509

theorem tailTrace_2321742 : CollatzResearch.WordTrace tailWord_2321742 prefixEnd_2321742 1192169601731160407447509 := by
  unfold tailWord_2321742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10585110944341591351247935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56453925036488487206655653 10585110944341591351247935)
  ·
    refine ⟨15877666416512387026871903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10585110944341591351247935 15877666416512387026871903)
    ·
      refine ⟨23816499624768580540307855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15877666416512387026871903 23816499624768580540307855)
      ·
        refine ⟨35724749437152870810461783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23816499624768580540307855 35724749437152870810461783)
        ·
          refine ⟨53587124155729306215692675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35724749437152870810461783 53587124155729306215692675)
          ·
            refine ⟨80380686233593959323539013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53587124155729306215692675 80380686233593959323539013)
            ·
              refine ⟨15071378668798867373163565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80380686233593959323539013 15071378668798867373163565)
              ·
                refine ⟨5651767000799575264936337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15071378668798867373163565 5651767000799575264936337)
                ·
                  refine ⟨4238825250599681448702253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5651767000799575264936337 4238825250599681448702253)
                  ·
                    refine ⟨1589559468974880543263345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4238825250599681448702253 1589559468974880543263345)
                    ·
                      refine ⟨1192169601731160407447509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589559468974880543263345 1192169601731160407447509)
                      ·
                        rfl

theorem cell23_2321742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_2321742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321742 prefixEnd_2321742 := by exact prefixLift 2321742
  have htrace : WordTrace (prefixWord ++ tailWord_2321742) baseStart_2321742 baseEnd_2321742 := by
    simpa [prefixWord, tailWord_2321742, baseEnd_2321742] using wordTrace_append hprefix tailTrace_2321742
  have hstable : (prefixWord ++ tailWord_2321742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321742).length < 2 ^ (prefixWord ++ tailWord_2321742).sum := by decide
  have hdescent : baseEnd_2321742 < baseStart_2321742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321765 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_2321765 : Nat := 118140960795 + 2321765 * 2 ^ 59
def prefixEnd_2321765 : Nat := 4983230072969 + 3 ^ 40 * 2321765 * 2
def baseEnd_2321765 : Nat := 397393803928737939153301

theorem tailTrace_2321765 : CollatzResearch.WordTrace tailWord_2321765 prefixEnd_2321765 397393803928737939153301 := by
  unfold tailWord_2321765
  simp only [CollatzResearch.WordTrace]
  refine ⟨84681726433649405738070749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56454484289099603825380499 84681726433649405738070749)
  ·
    refine ⟨31755647412618527151776531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84681726433649405738070749 31755647412618527151776531)
    ·
      refine ⟨47633471118927790727664797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31755647412618527151776531 47633471118927790727664797)
      ·
        refine ⟨17862551669597921522874299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47633471118927790727664797 17862551669597921522874299)
        ·
          refine ⟨26793827504396882284311449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17862551669597921522874299 26793827504396882284311449)
          ·
            refine ⟨20095370628297661713233587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26793827504396882284311449 20095370628297661713233587)
            ·
              refine ⟨30143055942446492569850381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20095370628297661713233587 30143055942446492569850381)
              ·
                refine ⟨11303645978417434713693893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30143055942446492569850381 11303645978417434713693893)
                ·
                  refine ⟨2119433620953269008817605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11303645978417434713693893 2119433620953269008817605)
                  ·
                    refine ⟨397393803928737939153301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119433620953269008817605 397393803928737939153301)
                    ·
                      rfl

theorem cell23_2321765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_2321765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321765 prefixEnd_2321765 := by exact prefixLift 2321765
  have htrace : WordTrace (prefixWord ++ tailWord_2321765) baseStart_2321765 baseEnd_2321765 := by
    simpa [prefixWord, tailWord_2321765, baseEnd_2321765] using wordTrace_append hprefix tailTrace_2321765
  have hstable : (prefixWord ++ tailWord_2321765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321765).length < 2 ^ (prefixWord ++ tailWord_2321765).sum := by decide
  have hdescent : baseEnd_2321765 < baseStart_2321765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321775 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 3]
def baseStart_2321775 : Nat := 118140960795 + 2321775 * 2 ^ 59
def prefixEnd_2321775 : Nat := 4983230072969 + 3 ^ 40 * 2321775 * 2
def baseEnd_2321775 : Nat := 1192186546592758778334857

theorem tailTrace_2321775 : CollatzResearch.WordTrace tailWord_2321775 prefixEnd_2321775 1192186546592758778334857 := by
  unfold tailWord_2321775
  simp only [CollatzResearch.WordTrace]
  refine ⟨84682091163613177445934779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56454727442408784963956519 84682091163613177445934779)
  ·
    refine ⟨127023136745419766168902169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84682091163613177445934779 127023136745419766168902169)
    ·
      refine ⟨95267352559064824626676627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127023136745419766168902169 95267352559064824626676627)
      ·
        refine ⟨142901028838597236940014941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95267352559064824626676627 142901028838597236940014941)
        ·
          refine ⟨53587885814473963852505603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142901028838597236940014941 53587885814473963852505603)
          ·
            refine ⟨80381828721710945778758405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53587885814473963852505603 80381828721710945778758405)
            ·
              refine ⟨15071592885320802333517201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80381828721710945778758405 15071592885320802333517201)
              ·
                refine ⟨11303694663990601750137901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15071592885320802333517201 11303694663990601750137901)
                ·
                  refine ⟨4238885498996475656301713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11303694663990601750137901 4238885498996475656301713)
                  ·
                    refine ⟨3179164124247356742226285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4238885498996475656301713 3179164124247356742226285)
                    ·
                      refine ⟨1192186546592758778334857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3179164124247356742226285 1192186546592758778334857)
                      ·
                        rfl

theorem cell23_2321775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_2321775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321775 prefixEnd_2321775 := by exact prefixLift 2321775
  have htrace : WordTrace (prefixWord ++ tailWord_2321775) baseStart_2321775 baseEnd_2321775 := by
    simpa [prefixWord, tailWord_2321775, baseEnd_2321775] using wordTrace_append hprefix tailTrace_2321775
  have hstable : (prefixWord ++ tailWord_2321775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321775).length < 2 ^ (prefixWord ++ tailWord_2321775).sum := by decide
  have hdescent : baseEnd_2321775 < baseStart_2321775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321806 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2321806 : Nat := 118140960795 + 2321806 * 2 ^ 59
def prefixEnd_2321806 : Nat := 4983230072969 + 3 ^ 40 * 2321806 * 2
def baseEnd_2321806 : Nat := 1192202464493048157047215

theorem tailTrace_2321806 : CollatzResearch.WordTrace tailWord_2321806 prefixEnd_2321806 1192202464493048157047215 := by
  unfold tailWord_2321806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10585402728312608717539159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56455481217667246493542181 10585402728312608717539159)
  ·
    refine ⟨15878104092468913076308739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10585402728312608717539159 15878104092468913076308739)
    ·
      refine ⟨23817156138703369614463109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15878104092468913076308739 23817156138703369614463109)
      ·
        refine ⟨4465716776006881802711833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23817156138703369614463109 4465716776006881802711833)
        ·
          refine ⟨3349287582005161352033875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4465716776006881802711833 3349287582005161352033875)
          ·
            refine ⟨5023931373007742028050813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3349287582005161352033875 5023931373007742028050813)
            ·
              refine ⟨1883974264877903260519055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5023931373007742028050813 1883974264877903260519055)
              ·
                refine ⟨2825961397316854890778583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883974264877903260519055 2825961397316854890778583)
                ·
                  refine ⟨4238942095975282336167875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825961397316854890778583 4238942095975282336167875)
                  ·
                    refine ⟨6358413143962923504251813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4238942095975282336167875 6358413143962923504251813)
                    ·
                      refine ⟨1192202464493048157047215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6358413143962923504251813 1192202464493048157047215)
                      ·
                        rfl

theorem cell23_2321806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2321806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321806 prefixEnd_2321806 := by exact prefixLift 2321806
  have htrace : WordTrace (prefixWord ++ tailWord_2321806) baseStart_2321806 baseEnd_2321806 := by
    simpa [prefixWord, tailWord_2321806, baseEnd_2321806] using wordTrace_append hprefix tailTrace_2321806
  have hstable : (prefixWord ++ tailWord_2321806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321806).length < 2 ^ (prefixWord ++ tailWord_2321806).sum := by decide
  have hdescent : baseEnd_2321806 < baseStart_2321806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321823 : List Nat := [1, 1, 2, 5, 1, 2, 4, 2, 1, 2, 2]
def baseStart_2321823 : Nat := 118140960795 + 2321823 * 2 ^ 59
def prefixEnd_2321823 : Nat := 4983230072969 + 3 ^ 40 * 2321823 * 2
def baseEnd_2321823 : Nat := 1192211193664174590534637

theorem tailTrace_2321823 : CollatzResearch.WordTrace tailWord_2321823 prefixEnd_2321823 1192211193664174590534637 := by
  unfold tailWord_2321823
  simp only [CollatzResearch.WordTrace]
  refine ⟨84683841867439281643682123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56455894578292854429121415 84683841867439281643682123)
  ·
    refine ⟨127025762801158922465523185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84683841867439281643682123 127025762801158922465523185)
    ·
      refine ⟨95269322100869191849142389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127025762801158922465523185 95269322100869191849142389)
      ·
        refine ⟨8931498946956486735857099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95269322100869191849142389 8931498946956486735857099)
        ·
          refine ⟨13397248420434730103785649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8931498946956486735857099 13397248420434730103785649)
          ·
            refine ⟨10047936315326047577839237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13397248420434730103785649 10047936315326047577839237)
            ·
              refine ⟨1883988059123633920844857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10047936315326047577839237 1883988059123633920844857)
              ·
                refine ⟨1412991044342725440633643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1883988059123633920844857 1412991044342725440633643)
                ·
                  refine ⟨2119486566514088160950465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412991044342725440633643 2119486566514088160950465)
                  ·
                    refine ⟨1589614924885566120712849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2119486566514088160950465 1589614924885566120712849)
                    ·
                      refine ⟨1192211193664174590534637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589614924885566120712849 1192211193664174590534637)
                      ·
                        rfl

theorem cell23_2321823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_2321823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321823 prefixEnd_2321823 := by exact prefixLift 2321823
  have htrace : WordTrace (prefixWord ++ tailWord_2321823) baseStart_2321823 baseEnd_2321823 := by
    simpa [prefixWord, tailWord_2321823, baseEnd_2321823] using wordTrace_append hprefix tailTrace_2321823
  have hstable : (prefixWord ++ tailWord_2321823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321823).length < 2 ^ (prefixWord ++ tailWord_2321823).sum := by decide
  have hdescent : baseEnd_2321823 < baseStart_2321823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321866 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_2321866 : Nat := 118140960795 + 2321866 * 2 ^ 59
def prefixEnd_2321866 : Nat := 4983230072969 + 3 ^ 40 * 2321866 * 2
def baseEnd_2321866 : Nat := 1192233273332317922296939

theorem tailTrace_2321866 : CollatzResearch.WordTrace tailWord_2321866 prefixEnd_2321866 1192233273332317922296939 := by
  unfold tailWord_2321866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21171352551570874996874363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56456940137522333324998301 21171352551570874996874363)
  ·
    refine ⟨31757028827356312495311545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21171352551570874996874363 31757028827356312495311545)
    ·
      refine ⟨23817771620517234371483659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31757028827356312495311545 23817771620517234371483659)
      ·
        refine ⟨35726657430775851557225489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23817771620517234371483659 35726657430775851557225489)
        ·
          refine ⟨26794993073081888667919117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35726657430775851557225489 26794993073081888667919117)
          ·
            refine ⟨10048122402405708250469669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26794993073081888667919117 10048122402405708250469669)
            ·
              refine ⟨1884022950451070296963063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10048122402405708250469669 1884022950451070296963063)
              ·
                refine ⟨2826034425676605445444595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884022950451070296963063 2826034425676605445444595)
                ·
                  refine ⟨4239051638514908168166893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826034425676605445444595 4239051638514908168166893)
                  ·
                    refine ⟨1589644364443090563062585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4239051638514908168166893 1589644364443090563062585)
                    ·
                      refine ⟨1192233273332317922296939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589644364443090563062585 1192233273332317922296939)
                      ·
                        rfl

theorem cell23_2321866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_2321866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321866 prefixEnd_2321866 := by exact prefixLift 2321866
  have htrace : WordTrace (prefixWord ++ tailWord_2321866) baseStart_2321866 baseEnd_2321866 := by
    simpa [prefixWord, tailWord_2321866, baseEnd_2321866] using wordTrace_append hprefix tailTrace_2321866
  have hstable : (prefixWord ++ tailWord_2321866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321866).length < 2 ^ (prefixWord ++ tailWord_2321866).sum := by decide
  have hdescent : baseEnd_2321866 < baseStart_2321866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321925 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_2321925 : Nat := 118140960795 + 2321925 * 2 ^ 59
def prefixEnd_2321925 : Nat := 4983230072969 + 3 ^ 40 * 2321925 * 2
def baseEnd_2321925 : Nat := 1192263568690933191459167

theorem tailTrace_2321925 : CollatzResearch.WordTrace tailWord_2321925 prefixEnd_2321925 1192263568690933191459167 := by
  unfold tailWord_2321925
  simp only [CollatzResearch.WordTrace]
  refine ⟨84687562113069753063895229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56458374742046502042596819 84687562113069753063895229)
  ·
    refine ⟨31757835792401157398960711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84687562113069753063895229 31757835792401157398960711)
    ·
      refine ⟨47636753688601736098441067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31757835792401157398960711 47636753688601736098441067)
      ·
        refine ⟨71455130532902604147661601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47636753688601736098441067 71455130532902604147661601)
        ·
          refine ⟨53591347899676953110746201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71455130532902604147661601 53591347899676953110746201)
          ·
            refine ⟨40193510924757714833059651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53591347899676953110746201 40193510924757714833059651)
            ·
              refine ⟨60290266387136572249589477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40193510924757714833059651 60290266387136572249589477)
              ·
                refine ⟨11304424947588107296798027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60290266387136572249589477 11304424947588107296798027)
                ·
                  refine ⟨16956637421382160945197041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11304424947588107296798027 16956637421382160945197041)
                  ·
                    refine ⟨12717478066036620708897781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16956637421382160945197041 12717478066036620708897781)
                    ·
                      refine ⟨1192263568690933191459167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12717478066036620708897781 1192263568690933191459167)
                      ·
                        rfl

theorem cell23_2321925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_2321925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321925 prefixEnd_2321925 := by exact prefixLift 2321925
  have htrace : WordTrace (prefixWord ++ tailWord_2321925) baseStart_2321925 baseEnd_2321925 := by
    simpa [prefixWord, tailWord_2321925, baseEnd_2321925] using wordTrace_append hprefix tailTrace_2321925
  have hstable : (prefixWord ++ tailWord_2321925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321925).length < 2 ^ (prefixWord ++ tailWord_2321925).sum := by decide
  have hdescent : baseEnd_2321925 < baseStart_2321925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321995 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 6]
def baseStart_2321995 : Nat := 118140960795 + 2321995 * 2 ^ 59
def prefixEnd_2321995 : Nat := 4983230072969 + 3 ^ 40 * 2321995 * 2
def baseEnd_2321995 : Nat := 1192299512336747917583845

theorem tailTrace_2321995 : CollatzResearch.WordTrace tailWord_2321995 prefixEnd_2321995 1192299512336747917583845 := by
  unfold tailWord_2321995
  simp only [CollatzResearch.WordTrace]
  refine ⟨84690115222816155018943439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56460076815210770012628959 84690115222816155018943439)
  ·
    refine ⟨127035172834224232528415159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84690115222816155018943439 127035172834224232528415159)
    ·
      refine ⟨190552759251336348792622739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127035172834224232528415159 190552759251336348792622739)
      ·
        refine ⟨285829138877004523188934109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190552759251336348792622739 285829138877004523188934109)
        ·
          refine ⟨107185927078876696195850291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285829138877004523188934109 107185927078876696195850291)
          ·
            refine ⟨160778890618315044293775437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107185927078876696195850291 160778890618315044293775437)
            ·
              refine ⟨60292083981868141610165789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160778890618315044293775437 60292083981868141610165789)
              ·
                refine ⟨22609531493200553103812171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60292083981868141610165789 22609531493200553103812171)
                ·
                  refine ⟨33914297239800829655718257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22609531493200553103812171 33914297239800829655718257)
                  ·
                    refine ⟨25435722929850622241788693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33914297239800829655718257 25435722929850622241788693)
                    ·
                      refine ⟨1192299512336747917583845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25435722929850622241788693 1192299512336747917583845)
                      ·
                        rfl

theorem cell23_2321995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_2321995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321995 prefixEnd_2321995 := by exact prefixLift 2321995
  have htrace : WordTrace (prefixWord ++ tailWord_2321995) baseStart_2321995 baseEnd_2321995 := by
    simpa [prefixWord, tailWord_2321995, baseEnd_2321995] using wordTrace_append hprefix tailTrace_2321995
  have hstable : (prefixWord ++ tailWord_2321995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321995).length < 2 ^ (prefixWord ++ tailWord_2321995).sum := by decide
  have hdescent : baseEnd_2321995 < baseStart_2321995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2321996 : List Nat := [2, 2, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_2321996 : Nat := 118140960795 + 2321996 * 2 ^ 59
def prefixEnd_2321996 : Nat := 4983230072969 + 3 ^ 40 * 2321996 * 2
def baseEnd_2321996 : Nat := 397433341939134137890447

theorem tailTrace_2321996 : CollatzResearch.WordTrace tailWord_2321996 prefixEnd_2321996 397433341939134137890447 := by
  unfold tailWord_2321996
  simp only [CollatzResearch.WordTrace]
  refine ⟨42345075847906266094864921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56460101130541688126486561 42345075847906266094864921)
  ·
    refine ⟨31758806885929699571148691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42345075847906266094864921 31758806885929699571148691)
    ·
      refine ⟨47638210328894549356723037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31758806885929699571148691 47638210328894549356723037)
      ·
        refine ⟨17864328873335456008771139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47638210328894549356723037 17864328873335456008771139)
        ·
          refine ⟨26796493310003184013156709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17864328873335456008771139 26796493310003184013156709)
          ·
            refine ⟨5024342495625597002466883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26796493310003184013156709 5024342495625597002466883)
            ·
              refine ⟨7536513743438395503700325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024342495625597002466883 7536513743438395503700325)
              ·
                refine ⟨1413096326894699156943811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7536513743438395503700325 1413096326894699156943811)
                ·
                  refine ⟨2119644490342048735415717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413096326894699156943811 2119644490342048735415717)
                  ·
                    refine ⟨397433341939134137890447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119644490342048735415717 397433341939134137890447)
                    ·
                      rfl

theorem cell23_2321996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_2321996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2321996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2321996 prefixEnd_2321996 := by exact prefixLift 2321996
  have htrace : WordTrace (prefixWord ++ tailWord_2321996) baseStart_2321996 baseEnd_2321996 := by
    simpa [prefixWord, tailWord_2321996, baseEnd_2321996] using wordTrace_append hprefix tailTrace_2321996
  have hstable : (prefixWord ++ tailWord_2321996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2321996).length < 2 ^ (prefixWord ++ tailWord_2321996).sum := by decide
  have hdescent : baseEnd_2321996 < baseStart_2321996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2321996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322013 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2322013 : Nat := 118140960795 + 2322013 * 2 ^ 59
def prefixEnd_2322013 : Nat := 4983230072969 + 3 ^ 40 * 2322013 * 2
def baseEnd_2322013 : Nat := 397436251662842949052921

theorem tailTrace_2322013 : CollatzResearch.WordTrace tailWord_2322013 prefixEnd_2322013 397436251662842949052921 := by
  unfold tailWord_2322013
  simp only [CollatzResearch.WordTrace]
  refine ⟨84690771736750944093098693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56460514491167296062065795 84690771736750944093098693)
  ·
    refine ⟨15879519700640802017456005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84690771736750944093098693 15879519700640802017456005)
    ·
      refine ⟨2977409943870150378273001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15879519700640802017456005 2977409943870150378273001)
      ·
        refine ⟨2233057457902612783704751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2977409943870150378273001 2233057457902612783704751)
        ·
          refine ⟨3349586186853919175557127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233057457902612783704751 3349586186853919175557127)
          ·
            refine ⟨5024379280280878763335691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3349586186853919175557127 5024379280280878763335691)
            ·
              refine ⟨7536568920421318145003537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024379280280878763335691 7536568920421318145003537)
              ·
                refine ⟨5652426690315988608752653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7536568920421318145003537 5652426690315988608752653)
                ·
                  refine ⟨2119660008868495728282245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5652426690315988608752653 2119660008868495728282245)
                  ·
                    refine ⟨397436251662842949052921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119660008868495728282245 397436251662842949052921)
                    ·
                      rfl

theorem cell23_2322013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2322013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322013 prefixEnd_2322013 := by exact prefixLift 2322013
  have htrace : WordTrace (prefixWord ++ tailWord_2322013) baseStart_2322013 baseEnd_2322013 := by
    simpa [prefixWord, tailWord_2322013, baseEnd_2322013] using wordTrace_append hprefix tailTrace_2322013
  have hstable : (prefixWord ++ tailWord_2322013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322013).length < 2 ^ (prefixWord ++ tailWord_2322013).sum := by decide
  have hdescent : baseEnd_2322013 < baseStart_2322013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322019 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 3]
def baseStart_2322019 : Nat := 118140960795 + 2322019 * 2 ^ 59
def prefixEnd_2322019 : Nat := 4983230072969 + 3 ^ 40 * 2322019 * 2
def baseEnd_2322019 : Nat := 1192311835872455823683735

theorem tailTrace_2322019 : CollatzResearch.WordTrace tailWord_2322019 prefixEnd_2322019 1192311835872455823683735 := by
  unfold tailWord_2322019
  simp only [CollatzResearch.WordTrace]
  refine ⟨84690990574729207117817111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56460660383152804745211407 84690990574729207117817111)
  ·
    refine ⟨127036485862093810676725667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84690990574729207117817111 127036485862093810676725667)
    ·
      refine ⟨190554728793140716015088501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127036485862093810676725667 190554728793140716015088501)
      ·
        refine ⟨17864505824356942126414547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190554728793140716015088501 17864505824356942126414547)
        ·
          refine ⟨26796758736535413189621821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17864505824356942126414547 26796758736535413189621821)
          ·
            refine ⟨10048784526200779946108183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26796758736535413189621821 10048784526200779946108183)
            ·
              refine ⟨15073176789301169919162275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10048784526200779946108183 15073176789301169919162275)
              ·
                refine ⟨22609765183951754878743413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15073176789301169919162275 22609765183951754878743413)
                ·
                  refine ⟨2119665485995477019882195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22609765183951754878743413 2119665485995477019882195)
                  ·
                    refine ⟨3179498228993215529823293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2119665485995477019882195 3179498228993215529823293)
                    ·
                      refine ⟨1192311835872455823683735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3179498228993215529823293 1192311835872455823683735)
                      ·
                        rfl

theorem cell23_2322019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_2322019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322019 prefixEnd_2322019 := by exact prefixLift 2322019
  have htrace : WordTrace (prefixWord ++ tailWord_2322019) baseStart_2322019 baseEnd_2322019 := by
    simpa [prefixWord, tailWord_2322019, baseEnd_2322019] using wordTrace_append hprefix tailTrace_2322019
  have hstable : (prefixWord ++ tailWord_2322019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322019).length < 2 ^ (prefixWord ++ tailWord_2322019).sum := by decide
  have hdescent : baseEnd_2322019 < baseStart_2322019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322035 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 10]
def baseStart_2322035 : Nat := 118140960795 + 2322035 * 2 ^ 59
def prefixEnd_2322035 : Nat := 4983230072969 + 3 ^ 40 * 2322035 * 2
def baseEnd_2322035 : Nat := 397440017187642587027887

theorem tailTrace_2322035 : CollatzResearch.WordTrace tailWord_2322035 prefixEnd_2322035 397440017187642587027887 := by
  unfold tailWord_2322035
  simp only [CollatzResearch.WordTrace]
  refine ⟨84691574142671241850399559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56461049428447494566933039 84691574142671241850399559)
  ·
    refine ⟨127037361214006862775599339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84691574142671241850399559 127037361214006862775599339)
    ·
      refine ⟨190556041821010294163399009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127037361214006862775599339 190556041821010294163399009)
      ·
        refine ⟨142917031365757720622549257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190556041821010294163399009 142917031365757720622549257)
        ·
          refine ⟨107187773524318290466911943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142917031365757720622549257 107187773524318290466911943)
          ·
            refine ⟨160781660286477435700367915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107187773524318290466911943 160781660286477435700367915)
            ·
              refine ⟨241172490429716153550551873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160781660286477435700367915 241172490429716153550551873)
              ·
                refine ⟨180879367822287115162913905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241172490429716153550551873 180879367822287115162913905)
                ·
                  refine ⟨135659525866715336372185429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180879367822287115162913905 135659525866715336372185429)
                  ·
                    refine ⟨397440017187642587027887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 135659525866715336372185429 397440017187642587027887)
                    ·
                      rfl

theorem cell23_2322035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 10].length) (baseStart_2322035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322035 prefixEnd_2322035 := by exact prefixLift 2322035
  have htrace : WordTrace (prefixWord ++ tailWord_2322035) baseStart_2322035 baseEnd_2322035 := by
    simpa [prefixWord, tailWord_2322035, baseEnd_2322035] using wordTrace_append hprefix tailTrace_2322035
  have hstable : (prefixWord ++ tailWord_2322035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322035).length < 2 ^ (prefixWord ++ tailWord_2322035).sum := by decide
  have hdescent : baseEnd_2322035 < baseStart_2322035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322042 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_2322042 : Nat := 118140960795 + 2322042 * 2 ^ 59
def prefixEnd_2322042 : Nat := 4983230072969 + 3 ^ 40 * 2322042 * 2
def baseEnd_2322042 : Nat := 1192323645927509233696129

theorem tailTrace_2322042 : CollatzResearch.WordTrace tailWord_2322042 prefixEnd_2322042 1192323645927509233696129 := by
  unfold tailWord_2322042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21172957363411470511476095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56461219635763921363936253 21172957363411470511476095)
  ·
    refine ⟨31759436045117205767214143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21172957363411470511476095 31759436045117205767214143)
    ·
      refine ⟨47639154067675808650821215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31759436045117205767214143 47639154067675808650821215)
      ·
        refine ⟨71458731101513712976231823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47639154067675808650821215 71458731101513712976231823)
        ·
          refine ⟨107188096652270569464347735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71458731101513712976231823 107188096652270569464347735)
          ·
            refine ⟨160782144978405854196521603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107188096652270569464347735 160782144978405854196521603)
            ·
              refine ⟨241173217467608781294782405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160782144978405854196521603 241173217467608781294782405)
              ·
                refine ⟨45219978275176646492771701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241173217467608781294782405 45219978275176646492771701)
                ·
                  refine ⟨4239372963297810608697347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45219978275176646492771701 4239372963297810608697347)
                  ·
                    refine ⟨6359059444946715913046021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4239372963297810608697347 6359059444946715913046021)
                    ·
                      refine ⟨1192323645927509233696129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6359059444946715913046021 1192323645927509233696129)
                      ·
                        rfl

theorem cell23_2322042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_2322042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322042 prefixEnd_2322042 := by exact prefixLift 2322042
  have htrace : WordTrace (prefixWord ++ tailWord_2322042) baseStart_2322042 baseEnd_2322042 := by
    simpa [prefixWord, tailWord_2322042, baseEnd_2322042] using wordTrace_append hprefix tailTrace_2322042
  have hstable : (prefixWord ++ tailWord_2322042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322042).length < 2 ^ (prefixWord ++ tailWord_2322042).sum := by decide
  have hdescent : baseEnd_2322042 < baseStart_2322042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322069 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2322069 : Nat := 118140960795 + 2322069 * 2 ^ 59
def prefixEnd_2322069 : Nat := 4983230072969 + 3 ^ 40 * 2322069 * 2
def baseEnd_2322069 : Nat := 397445836635060209352835

theorem tailTrace_2322069 : CollatzResearch.WordTrace tailWord_2322069 prefixEnd_2322069 397445836635060209352835 := by
  unfold tailWord_2322069
  simp only [CollatzResearch.WordTrace]
  refine ⟨84692814224548065657137261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56461876149698710438091507 84692814224548065657137261)
  ·
    refine ⟨31759805334205524621426473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84692814224548065657137261 31759805334205524621426473)
    ·
      refine ⟨23819854000654143466069855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31759805334205524621426473 23819854000654143466069855)
      ·
        refine ⟨35729781000981215199104783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23819854000654143466069855 35729781000981215199104783)
        ·
          refine ⟨53594671501471822798657175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35729781000981215199104783 53594671501471822798657175)
          ·
            refine ⟨80392007252207734197985763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53594671501471822798657175 80392007252207734197985763)
            ·
              refine ⟨120588010878311601296978645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80392007252207734197985763 120588010878311601296978645)
              ·
                refine ⟨2826281504960428155397937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 120588010878311601296978645 2826281504960428155397937)
                ·
                  refine ⟨2119711128720321116548453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2826281504960428155397937 2119711128720321116548453)
                  ·
                    refine ⟨397445836635060209352835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119711128720321116548453 397445836635060209352835)
                    ·
                      rfl

theorem cell23_2322069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2322069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322069 prefixEnd_2322069 := by exact prefixLift 2322069
  have htrace : WordTrace (prefixWord ++ tailWord_2322069) baseStart_2322069 baseEnd_2322069 := by
    simpa [prefixWord, tailWord_2322069, baseEnd_2322069] using wordTrace_append hprefix tailTrace_2322069
  have hstable : (prefixWord ++ tailWord_2322069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322069).length < 2 ^ (prefixWord ++ tailWord_2322069).sum := by decide
  have hdescent : baseEnd_2322069 < baseStart_2322069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322110 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_2322110 : Nat := 118140960795 + 2322110 * 2 ^ 59
def prefixEnd_2322110 : Nat := 4983230072969 + 3 ^ 40 * 2322110 * 2
def baseEnd_2322110 : Nat := 1192358562612014967645817

theorem tailTrace_2322110 : CollatzResearch.WordTrace tailWord_2322110 prefixEnd_2322110 1192358562612014967645817 := by
  unfold tailWord_2322110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10586788702174941207422473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56462873078266353106253189 10586788702174941207422473)
  ·
    refine ⟨7940091526631205905566855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10586788702174941207422473 7940091526631205905566855)
    ·
      refine ⟨11910137289946808858350283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7940091526631205905566855 11910137289946808858350283)
      ·
        refine ⟨17865205934920213287525425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11910137289946808858350283 17865205934920213287525425)
        ·
          refine ⟨13398904451190159965644069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17865205934920213287525425 13398904451190159965644069)
          ·
            refine ⟨2512294584598154993558263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13398904451190159965644069 2512294584598154993558263)
            ·
              refine ⟨3768441876897232490337395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512294584598154993558263 3768441876897232490337395)
              ·
                refine ⟨5652662815345848735506093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768441876897232490337395 5652662815345848735506093)
                ·
                  refine ⟨2119748555754693275814785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5652662815345848735506093 2119748555754693275814785)
                  ·
                    refine ⟨1589811416816019956861089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2119748555754693275814785 1589811416816019956861089)
                    ·
                      refine ⟨1192358562612014967645817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589811416816019956861089 1192358562612014967645817)
                      ·
                        rfl

theorem cell23_2322110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_2322110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322110 prefixEnd_2322110 := by exact prefixLift 2322110
  have htrace : WordTrace (prefixWord ++ tailWord_2322110) baseStart_2322110 baseEnd_2322110 := by
    simpa [prefixWord, tailWord_2322110, baseEnd_2322110] using wordTrace_append hprefix tailTrace_2322110
  have hstable : (prefixWord ++ tailWord_2322110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322110).length < 2 ^ (prefixWord ++ tailWord_2322110).sum := by decide
  have hdescent : baseEnd_2322110 < baseStart_2322110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322112 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 2, 7]
def baseStart_2322112 : Nat := 118140960795 + 2322112 * 2 ^ 59
def prefixEnd_2322112 : Nat := 4983230072969 + 3 ^ 40 * 2322112 * 2
def baseEnd_2322112 : Nat := 397453196524441319940269

theorem tailTrace_2322112 : CollatzResearch.WordTrace tailWord_2322112 prefixEnd_2322112 397453196524441319940269 := by
  unfold tailWord_2322112
  simp only [CollatzResearch.WordTrace]
  refine ⟨42347191281696142000476295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56462921708928189333968393 42347191281696142000476295)
  ·
    refine ⟨63520786922544213000714443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42347191281696142000476295 63520786922544213000714443)
    ·
      refine ⟨95281180383816319501071665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63520786922544213000714443 95281180383816319501071665)
      ·
        refine ⟨71460885287862239625803749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95281180383816319501071665 71460885287862239625803749)
        ·
          refine ⟨13398915991474169929838203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71460885287862239625803749 13398915991474169929838203)
          ·
            refine ⟨20098373987211254894757305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13398915991474169929838203 20098373987211254894757305)
            ·
              refine ⟨15073780490408441171067979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20098373987211254894757305 15073780490408441171067979)
              ·
                refine ⟨22610670735612661756601969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15073780490408441171067979 22610670735612661756601969)
                ·
                  refine ⟨16958003051709496317451477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22610670735612661756601969 16958003051709496317451477)
                  ·
                    refine ⟨397453196524441319940269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16958003051709496317451477 397453196524441319940269)
                    ·
                      rfl

theorem cell23_2322112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_2322112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322112 prefixEnd_2322112 := by exact prefixLift 2322112
  have htrace : WordTrace (prefixWord ++ tailWord_2322112) baseStart_2322112 baseEnd_2322112 := by
    simpa [prefixWord, tailWord_2322112, baseEnd_2322112] using wordTrace_append hprefix tailTrace_2322112
  have hstable : (prefixWord ++ tailWord_2322112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322112).length < 2 ^ (prefixWord ++ tailWord_2322112).sum := by decide
  have hdescent : baseEnd_2322112 < baseStart_2322112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322136 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 3, 3, 2]
def baseStart_2322136 : Nat := 118140960795 + 2322136 * 2 ^ 59
def prefixEnd_2322136 : Nat := 4983230072969 + 3 ^ 40 * 2322136 * 2
def baseEnd_2322136 : Nat := 1192371913109031865920697

theorem tailTrace_2322136 : CollatzResearch.WordTrace tailWord_2322136 prefixEnd_2322136 1192371913109031865920697 := by
  unfold tailWord_2322136
  simp only [CollatzResearch.WordTrace]
  refine ⟨42347628957652668049913131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56463505276870224066550841 42347628957652668049913131)
  ·
    refine ⟨63521443436479002074869697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42347628957652668049913131 63521443436479002074869697)
    ·
      refine ⟨47641082577359251556152273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63521443436479002074869697 47641082577359251556152273)
      ·
        refine ⟨35730811933019438667114205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47641082577359251556152273 35730811933019438667114205)
        ·
          refine ⟨13399054474882289500167827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35730811933019438667114205 13399054474882289500167827)
          ·
            refine ⟨20098581712323434250251741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13399054474882289500167827 20098581712323434250251741)
            ·
              refine ⟨7536968142121287843844403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20098581712323434250251741 7536968142121287843844403)
              ·
                refine ⟨11305452213181931765766605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7536968142121287843844403 11305452213181931765766605)
                ·
                  refine ⟨4239544579943224412162477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11305452213181931765766605 4239544579943224412162477)
                  ·
                    refine ⟨1589829217478709154560929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4239544579943224412162477 1589829217478709154560929)
                    ·
                      refine ⟨1192371913109031865920697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589829217478709154560929 1192371913109031865920697)
                      ·
                        rfl

theorem cell23_2322136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_2322136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322136 prefixEnd_2322136 := by exact prefixLift 2322136
  have htrace : WordTrace (prefixWord ++ tailWord_2322136) baseStart_2322136 baseEnd_2322136 := by
    simpa [prefixWord, tailWord_2322136, baseEnd_2322136] using wordTrace_append hprefix tailTrace_2322136
  have hstable : (prefixWord ++ tailWord_2322136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322136).length < 2 ^ (prefixWord ++ tailWord_2322136).sum := by decide
  have hdescent : baseEnd_2322136 < baseStart_2322136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322216 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2322216 : Nat := 118140960795 + 2322216 * 2 ^ 59
def prefixEnd_2322216 : Nat := 4983230072969 + 3 ^ 40 * 2322216 * 2
def baseEnd_2322216 : Nat := 1192412991561391552920329

theorem tailTrace_2322216 : CollatzResearch.WordTrace tailWord_2322216 prefixEnd_2322216 1192412991561391552920329 := by
  unfold tailWord_2322216
  simp only [CollatzResearch.WordTrace]
  refine ⟨42349087877507754881369251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56465450503343673175159001 42349087877507754881369251)
  ·
    refine ⟨63523631816261632322053877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42349087877507754881369251 63523631816261632322053877)
    ·
      refine ⟨5955340482774528030192551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63523631816261632322053877 5955340482774528030192551)
      ·
        refine ⟨8933010724161792045288827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5955340482774528030192551 8933010724161792045288827)
        ·
          refine ⟨13399516086242688067933241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8933010724161792045288827 13399516086242688067933241)
          ·
            refine ⟨10049637064682016050949931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13399516086242688067933241 10049637064682016050949931)
            ·
              refine ⟨15074455597023024076424897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10049637064682016050949931 15074455597023024076424897)
              ·
                refine ⟨11305841697767268057318673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15074455597023024076424897 11305841697767268057318673)
                ·
                  refine ⟨8479381273325451042989005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11305841697767268057318673 8479381273325451042989005)
                  ·
                    refine ⟨3179767977497044141120877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8479381273325451042989005 3179767977497044141120877)
                    ·
                      refine ⟨1192412991561391552920329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3179767977497044141120877 1192412991561391552920329)
                      ·
                        rfl

theorem cell23_2322216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2322216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322216 prefixEnd_2322216 := by exact prefixLift 2322216
  have htrace : WordTrace (prefixWord ++ tailWord_2322216) baseStart_2322216 baseEnd_2322216 := by
    simpa [prefixWord, tailWord_2322216, baseEnd_2322216] using wordTrace_append hprefix tailTrace_2322216
  have hstable : (prefixWord ++ tailWord_2322216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322216).length < 2 ^ (prefixWord ++ tailWord_2322216).sum := by decide
  have hdescent : baseEnd_2322216 < baseStart_2322216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322279 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 8]
def baseStart_2322279 : Nat := 118140960795 + 2322279 * 2 ^ 59
def prefixEnd_2322279 : Nat := 4983230072969 + 3 ^ 40 * 2322279 * 2
def baseEnd_2322279 : Nat := 132493926760291645159171

theorem tailTrace_2322279 : CollatzResearch.WordTrace tailWord_2322279 prefixEnd_2322279 132493926760291645159171 := by
  unfold tailWord_2322279
  simp only [CollatzResearch.WordTrace]
  refine ⟨84700473553787271522281891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56466982369191514348187927 84700473553787271522281891)
  ·
    refine ⟨127050710330680907283422837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84700473553787271522281891 127050710330680907283422837)
    ·
      refine ⟨11911004093501335057820891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127050710330680907283422837 11911004093501335057820891)
      ·
        refine ⟨17866506140252002586731337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11911004093501335057820891 17866506140252002586731337)
        ·
          refine ⟨13399879605189001940048503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17866506140252002586731337 13399879605189001940048503)
          ·
            refine ⟨20099819407783502910072755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13399879605189001940048503 20099819407783502910072755)
            ·
              refine ⟨30149729111675254365109133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20099819407783502910072755 30149729111675254365109133)
              ·
                refine ⟨11306148416878220386915925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30149729111675254365109133 11306148416878220386915925)
                ·
                  refine ⟨132493926760291645159171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11306148416878220386915925 132493926760291645159171)
                  ·
                    rfl

theorem cell23_2322279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 8].length) (baseStart_2322279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322279 prefixEnd_2322279 := by exact prefixLift 2322279
  have htrace : WordTrace (prefixWord ++ tailWord_2322279) baseStart_2322279 baseEnd_2322279 := by
    simpa [prefixWord, tailWord_2322279, baseEnd_2322279] using wordTrace_append hprefix tailTrace_2322279
  have hstable : (prefixWord ++ tailWord_2322279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322279).length < 2 ^ (prefixWord ++ tailWord_2322279).sum := by decide
  have hdescent : baseEnd_2322279 < baseStart_2322279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322334 : List Nat := [4, 3, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2322334 : Nat := 118140960795 + 2322334 * 2 ^ 59
def prefixEnd_2322334 : Nat := 4983230072969 + 3 ^ 40 * 2322334 * 2
def baseEnd_2322334 : Nat := 397491194092874030414929

theorem tailTrace_2322334 : CollatzResearch.WordTrace tailWord_2322334 prefixEnd_2322334 397491194092874030414929 := by
  unfold tailWord_2322334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10587809946073501989441757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56468319712392010610356037 10587809946073501989441757)
  ·
    refine ⟨3970428729777563246040659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10587809946073501989441757 3970428729777563246040659)
    ·
      refine ⟨5955643094666344869060989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3970428729777563246040659 5955643094666344869060989)
      ·
        refine ⟨2233366160499879325897871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5955643094666344869060989 2233366160499879325897871)
        ·
          refine ⟨3350049240749818988846807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233366160499879325897871 3350049240749818988846807)
          ·
            refine ⟨5025073861124728483270211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350049240749818988846807 5025073861124728483270211)
            ·
              refine ⟨7537610791687092724905317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025073861124728483270211 7537610791687092724905317)
              ·
                refine ⟨1413302023441329885919747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7537610791687092724905317 1413302023441329885919747)
                ·
                  refine ⟨2119953035161994828879621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413302023441329885919747 2119953035161994828879621)
                  ·
                    refine ⟨397491194092874030414929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119953035161994828879621 397491194092874030414929)
                    ·
                      rfl

theorem cell23_2322334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2322334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322334 prefixEnd_2322334 := by exact prefixLift 2322334
  have htrace : WordTrace (prefixWord ++ tailWord_2322334) baseStart_2322334 baseEnd_2322334 := by
    simpa [prefixWord, tailWord_2322334, baseEnd_2322334] using wordTrace_append hprefix tailTrace_2322334
  have hstable : (prefixWord ++ tailWord_2322334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322334).length < 2 ^ (prefixWord ++ tailWord_2322334).sum := by decide
  have hdescent : baseEnd_2322334 < baseStart_2322334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322339 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 5, 6]
def baseStart_2322339 : Nat := 118140960795 + 2322339 * 2 ^ 59
def prefixEnd_2322339 : Nat := 4983230072969 + 3 ^ 40 * 2322339 * 2
def baseEnd_2322339 : Nat := 397492049893964857227421

theorem tailTrace_2322339 : CollatzResearch.WordTrace tailWord_2322339 prefixEnd_2322339 397492049893964857227421 := by
  unfold tailWord_2322339
  simp only [CollatzResearch.WordTrace]
  refine ⟨84702661933569901769466071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56468441289046601179644047 84702661933569901769466071)
  ·
    refine ⟨127053992900354852654199107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84702661933569901769466071 127053992900354852654199107)
    ·
      refine ⟨190580989350532278981298661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127053992900354852654199107 190580989350532278981298661)
      ·
        refine ⟨35733935503224802308993499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190580989350532278981298661 35733935503224802308993499)
        ·
          refine ⟨53600903254837203463490249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35733935503224802308993499 53600903254837203463490249)
          ·
            refine ⟨40200677441127902597617687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53600903254837203463490249 40200677441127902597617687)
            ·
              refine ⟨60301016161691853896426531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40200677441127902597617687 60301016161691853896426531)
              ·
                refine ⟨90451524242537780844639797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60301016161691853896426531 90451524242537780844639797)
                ·
                  refine ⟨8479830397737916954184981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90451524242537780844639797 8479830397737916954184981)
                  ·
                    refine ⟨397492049893964857227421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8479830397737916954184981 397492049893964857227421)
                    ·
                      rfl

theorem cell23_2322339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 6].length) (baseStart_2322339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322339 prefixEnd_2322339 := by exact prefixLift 2322339
  have htrace : WordTrace (prefixWord ++ tailWord_2322339) baseStart_2322339 baseEnd_2322339 := by
    simpa [prefixWord, tailWord_2322339, baseEnd_2322339] using wordTrace_append hprefix tailTrace_2322339
  have hstable : (prefixWord ++ tailWord_2322339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322339).length < 2 ^ (prefixWord ++ tailWord_2322339).sum := by decide
  have hdescent : baseEnd_2322339 < baseStart_2322339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322363 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 5, 2, 2]
def baseStart_2322363 : Nat := 118140960795 + 2322363 * 2 ^ 59
def prefixEnd_2322363 : Nat := 4983230072969 + 3 ^ 40 * 2322363 * 2
def baseEnd_2322363 : Nat := 1192488473217602477782153

theorem tailTrace_2322363 : CollatzResearch.WordTrace tailWord_2322363 prefixEnd_2322363 1192488473217602477782153 := by
  unfold tailWord_2322363
  simp only [CollatzResearch.WordTrace]
  refine ⟨84703537285482953868339743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56469024856988635912226495 84703537285482953868339743)
  ·
    refine ⟨127055305928224430802509615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84703537285482953868339743 127055305928224430802509615)
    ·
      refine ⟨190582958892336646203764423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127055305928224430802509615 190582958892336646203764423)
      ·
        refine ⟨285874438338504969305646635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190582958892336646203764423 285874438338504969305646635)
        ·
          refine ⟨428811657507757453958469953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285874438338504969305646635 428811657507757453958469953)
          ·
            refine ⟨321608743130818090468852465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428811657507757453958469953 321608743130818090468852465)
            ·
              refine ⟨241206557348113567851639349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321608743130818090468852465 241206557348113567851639349)
              ·
                refine ⟨22613114751385646986091189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241206557348113567851639349 22613114751385646986091189)
                ·
                  refine ⟨2119979507942404404946049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22613114751385646986091189 2119979507942404404946049)
                  ·
                    refine ⟨1589984630956803303709537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2119979507942404404946049 1589984630956803303709537)
                    ·
                      refine ⟨1192488473217602477782153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1589984630956803303709537 1192488473217602477782153)
                      ·
                        rfl

theorem cell23_2322363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 2, 2].length) (baseStart_2322363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322363 prefixEnd_2322363 := by exact prefixLift 2322363
  have htrace : WordTrace (prefixWord ++ tailWord_2322363) baseStart_2322363 baseEnd_2322363 := by
    simpa [prefixWord, tailWord_2322363, baseEnd_2322363] using wordTrace_append hprefix tailTrace_2322363
  have hstable : (prefixWord ++ tailWord_2322363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322363).length < 2 ^ (prefixWord ++ tailWord_2322363).sum := by decide
  have hdescent : baseEnd_2322363 < baseStart_2322363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322380 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 1, 1, 4]
def baseStart_2322380 : Nat := 118140960795 + 2322380 * 2 ^ 59
def prefixEnd_2322380 : Nat := 4983230072969 + 3 ^ 40 * 2322380 * 2
def baseEnd_2322380 : Nat := 1192497202388728911269575

theorem tailTrace_2322380 : CollatzResearch.WordTrace tailWord_2322380 prefixEnd_2322380 1192497202388728911269575 := by
  unfold tailWord_2322380
  simp only [CollatzResearch.WordTrace]
  refine ⟨42352078663210682885854297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56469438217614243847805729 42352078663210682885854297)
  ·
    refine ⟨31764058997408012164390723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42352078663210682885854297 31764058997408012164390723)
    ·
      refine ⟨47646088496112018246586085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31764058997408012164390723 47646088496112018246586085)
      ·
        refine ⟨8933641593021003421234891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47646088496112018246586085 8933641593021003421234891)
        ·
          refine ⟨13400462389531505131852337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8933641593021003421234891 13400462389531505131852337)
          ·
            refine ⟨10050346792148628848889253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13400462389531505131852337 10050346792148628848889253)
            ·
              refine ⟨1884440023527867909166735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10050346792148628848889253 1884440023527867909166735)
              ·
                refine ⟨2826660035291801863750103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884440023527867909166735 2826660035291801863750103)
                ·
                  refine ⟨4239990052937702795625155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826660035291801863750103 4239990052937702795625155)
                  ·
                    refine ⟨6359985079406554193437733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4239990052937702795625155 6359985079406554193437733)
                    ·
                      refine ⟨1192497202388728911269575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6359985079406554193437733 1192497202388728911269575)
                      ·
                        rfl

theorem cell23_2322380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_2322380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322380 prefixEnd_2322380 := by exact prefixLift 2322380
  have htrace : WordTrace (prefixWord ++ tailWord_2322380) baseStart_2322380 baseEnd_2322380 := by
    simpa [prefixWord, tailWord_2322380, baseEnd_2322380] using wordTrace_append hprefix tailTrace_2322380
  have hstable : (prefixWord ++ tailWord_2322380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322380).length < 2 ^ (prefixWord ++ tailWord_2322380).sum := by decide
  have hdescent : baseEnd_2322380 < baseStart_2322380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322383 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 3]
def baseStart_2322383 : Nat := 118140960795 + 2322383 * 2 ^ 59
def prefixEnd_2322383 : Nat := 4983230072969 + 3 ^ 40 * 2322383 * 2
def baseEnd_2322383 : Nat := 1192498742830692399532061

theorem tailTrace_2322383 : CollatzResearch.WordTrace tailWord_2322383 prefixEnd_2322383 1192498742830692399532061 := by
  unfold tailWord_2322383
  simp only [CollatzResearch.WordTrace]
  refine ⟨84704266745410497284067803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56469511163606998189378535 84704266745410497284067803)
  ·
    refine ⟨127056400118115745926101705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84704266745410497284067803 127056400118115745926101705)
    ·
      refine ⟨95292300088586809444576279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127056400118115745926101705 95292300088586809444576279)
      ·
        refine ⟨142938450132880214166864419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95292300088586809444576279 142938450132880214166864419)
        ·
          refine ⟨214407675199320321250296629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142938450132880214166864419 214407675199320321250296629)
          ·
            refine ⟨20100719549936280117215309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214407675199320321250296629 20100719549936280117215309)
            ·
              refine ⟨7537769831226105043955741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20100719549936280117215309 7537769831226105043955741)
              ·
                refine ⟨2826663686709789391483403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7537769831226105043955741 2826663686709789391483403)
                ·
                  refine ⟨4239995530064684087225105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826663686709789391483403 4239995530064684087225105)
                  ·
                    refine ⟨3179996647548513065418829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4239995530064684087225105 3179996647548513065418829)
                    ·
                      refine ⟨1192498742830692399532061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3179996647548513065418829 1192498742830692399532061)
                      ·
                        rfl

theorem cell23_2322383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 3].length) (baseStart_2322383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322383 prefixEnd_2322383 := by exact prefixLift 2322383
  have htrace : WordTrace (prefixWord ++ tailWord_2322383) baseStart_2322383 baseEnd_2322383 := by
    simpa [prefixWord, tailWord_2322383, baseEnd_2322383] using wordTrace_append hprefix tailTrace_2322383
  have hstable : (prefixWord ++ tailWord_2322383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322383).length < 2 ^ (prefixWord ++ tailWord_2322383).sum := by decide
  have hdescent : baseEnd_2322383 < baseStart_2322383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322407 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 2, 4]
def baseStart_2322407 : Nat := 118140960795 + 2322407 * 2 ^ 59
def prefixEnd_2322407 : Nat := 4983230072969 + 3 ^ 40 * 2322407 * 2
def baseEnd_2322407 : Nat := 397503688788800101877317

theorem tailTrace_2322407 : CollatzResearch.WordTrace tailWord_2322407 prefixEnd_2322407 397503688788800101877317 := by
  unfold tailWord_2322407
  simp only [CollatzResearch.WordTrace]
  refine ⟨84705142097323549382941475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56470094731549032921960983 84705142097323549382941475)
  ·
    refine ⟨127057713145985324074412213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84705142097323549382941475 127057713145985324074412213)
    ·
      refine ⟨11911660607436124131976145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127057713145985324074412213 11911660607436124131976145)
      ·
        refine ⟨8933745455577093098982109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11911660607436124131976145 8933745455577093098982109)
        ·
          refine ⟨3350154545841409912118291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8933745455577093098982109 3350154545841409912118291)
          ·
            refine ⟨5025231818762114868177437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350154545841409912118291 5025231818762114868177437)
            ·
              refine ⟨1884461932035793075566539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5025231818762114868177437 1884461932035793075566539)
              ·
                refine ⟨2826692898053689613349809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884461932035793075566539 2826692898053689613349809)
                ·
                  refine ⟨2120019673540267210012357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2826692898053689613349809 2120019673540267210012357)
                  ·
                    refine ⟨397503688788800101877317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2120019673540267210012357 397503688788800101877317)
                    ·
                      rfl

theorem cell23_2322407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_2322407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322407 prefixEnd_2322407 := by exact prefixLift 2322407
  have htrace : WordTrace (prefixWord ++ tailWord_2322407) baseStart_2322407 baseEnd_2322407 := by
    simpa [prefixWord, tailWord_2322407, baseEnd_2322407] using wordTrace_append hprefix tailTrace_2322407
  have hstable : (prefixWord ++ tailWord_2322407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322407).length < 2 ^ (prefixWord ++ tailWord_2322407).sum := by decide
  have hdescent : baseEnd_2322407 < baseStart_2322407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322440 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_2322440 : Nat := 118140960795 + 2322440 * 2 ^ 59
def prefixEnd_2322440 : Nat := 4983230072969 + 3 ^ 40 * 2322440 * 2
def baseEnd_2322440 : Nat := 1192528011227998676519299

theorem tailTrace_2322440 : CollatzResearch.WordTrace tailWord_2322440 prefixEnd_2322440 1192528011227998676519299 := by
  unfold tailWord_2322440
  simp only [CollatzResearch.WordTrace]
  refine ⟨42353172853101998009446387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56470897137469330679261849 42353172853101998009446387)
  ·
    refine ⟨63529759279652997014169581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42353172853101998009446387 63529759279652997014169581)
    ·
      refine ⟨23823659729869873880313593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63529759279652997014169581 23823659729869873880313593)
      ·
        refine ⟨17867744797402405410235195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23823659729869873880313593 17867744797402405410235195)
        ·
          refine ⟨26801617196103608115352793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17867744797402405410235195 26801617196103608115352793)
          ·
            refine ⟨20101212897077706086514595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26801617196103608115352793 20101212897077706086514595)
            ·
              refine ⟨30151819345616559129771893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20101212897077706086514595 30151819345616559129771893)
              ·
                refine ⟨2826733063651552418416115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30151819345616559129771893 2826733063651552418416115)
                ·
                  refine ⟨4240099595477328627624173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826733063651552418416115 4240099595477328627624173)
                  ·
                    refine ⟨1590037348303998235359065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4240099595477328627624173 1590037348303998235359065)
                    ·
                      refine ⟨1192528011227998676519299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1590037348303998235359065 1192528011227998676519299)
                      ·
                        rfl

theorem cell23_2322440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_2322440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322440 prefixEnd_2322440 := by exact prefixLift 2322440
  have htrace : WordTrace (prefixWord ++ tailWord_2322440) baseStart_2322440 baseEnd_2322440 := by
    simpa [prefixWord, tailWord_2322440, baseEnd_2322440] using wordTrace_append hprefix tailTrace_2322440
  have hstable : (prefixWord ++ tailWord_2322440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322440).length < 2 ^ (prefixWord ++ tailWord_2322440).sum := by decide
  have hdescent : baseEnd_2322440 < baseStart_2322440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322456 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2322456 : Nat := 118140960795 + 2322456 * 2 ^ 59
def prefixEnd_2322456 : Nat := 4983230072969 + 3 ^ 40 * 2322456 * 2
def baseEnd_2322456 : Nat := 1192536226918470613919225

theorem tailTrace_2322456 : CollatzResearch.WordTrace tailWord_2322456 prefixEnd_2322456 1192536226918470613919225 := by
  unfold tailWord_2322456
  simp only [CollatzResearch.WordTrace]
  refine ⟨42353464637073015375737611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56471286182764020500983481 42353464637073015375737611)
  ·
    refine ⟨63530196955609523063606417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42353464637073015375737611 63530196955609523063606417)
    ·
      refine ⟨47647647716707142297704813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63530196955609523063606417 47647647716707142297704813)
      ·
        refine ⟨17867867893765178361639305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47647647716707142297704813 17867867893765178361639305)
        ·
          refine ⟨13400900920323883771229479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17867867893765178361639305 13400900920323883771229479)
          ·
            refine ⟨20101351380485825656844219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13400900920323883771229479 20101351380485825656844219)
            ·
              refine ⟨30152027070728738485266329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20101351380485825656844219 30152027070728738485266329)
              ·
                refine ⟨22614020303046553863949747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30152027070728738485266329 22614020303046553863949747)
                ·
                  refine ⟨33921030454569830795924621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22614020303046553863949747 33921030454569830795924621)
                  ·
                    refine ⟨12720386420463686548471733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33921030454569830795924621 12720386420463686548471733)
                    ·
                      refine ⟨1192536226918470613919225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12720386420463686548471733 1192536226918470613919225)
                      ·
                        rfl

theorem cell23_2322456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2322456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322456 prefixEnd_2322456 := by exact prefixLift 2322456
  have htrace : WordTrace (prefixWord ++ tailWord_2322456) baseStart_2322456 baseEnd_2322456 := by
    simpa [prefixWord, tailWord_2322456, baseEnd_2322456] using wordTrace_append hprefix tailTrace_2322456
  have hstable : (prefixWord ++ tailWord_2322456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322456).length < 2 ^ (prefixWord ++ tailWord_2322456).sum := by decide
  have hdescent : baseEnd_2322456 < baseStart_2322456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322474 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_2322474 : Nat := 118140960795 + 2322474 * 2 ^ 59
def prefixEnd_2322474 : Nat := 4983230072969 + 3 ^ 40 * 2322474 * 2
def baseEnd_2322474 : Nat := 1192545469570251543494143

theorem tailTrace_2322474 : CollatzResearch.WordTrace tailWord_2322474 prefixEnd_2322474 1192545469570251543494143 := by
  unfold tailWord_2322474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21176896447020204956407619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56471723858720546550420317 21176896447020204956407619)
  ·
    refine ⟨31765344670530307434611429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21176896447020204956407619 31765344670530307434611429)
    ·
      refine ⟨5956002125724432643989643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31765344670530307434611429 5956002125724432643989643)
      ·
        refine ⟨8934003188586648965984465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5956002125724432643989643 8934003188586648965984465)
        ·
          refine ⟨6700502391439986724488349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8934003188586648965984465 6700502391439986724488349)
          ·
            refine ⟨2512688396789995021683131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6700502391439986724488349 2512688396789995021683131)
            ·
              refine ⟨3769032595184992532524697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512688396789995021683131 3769032595184992532524697)
              ·
                refine ⟨2826774446388744399393523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3769032595184992532524697 2826774446388744399393523)
                ·
                  refine ⟨4240161669583116599090285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826774446388744399393523 4240161669583116599090285)
                  ·
                    refine ⟨1590060626093668724658857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4240161669583116599090285 1590060626093668724658857)
                    ·
                      refine ⟨1192545469570251543494143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1590060626093668724658857 1192545469570251543494143)
                      ·
                        rfl

theorem cell23_2322474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_2322474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322474 prefixEnd_2322474 := by exact prefixLift 2322474
  have htrace : WordTrace (prefixWord ++ tailWord_2322474) baseStart_2322474 baseEnd_2322474 := by
    simpa [prefixWord, tailWord_2322474, baseEnd_2322474] using wordTrace_append hprefix tailTrace_2322474
  have hstable : (prefixWord ++ tailWord_2322474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322474).length < 2 ^ (prefixWord ++ tailWord_2322474).sum := by decide
  have hdescent : baseEnd_2322474 < baseStart_2322474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322503 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_2322503 : Nat := 118140960795 + 2322503 * 2 ^ 59
def prefixEnd_2322503 : Nat := 4983230072969 + 3 ^ 40 * 2322503 * 2
def baseEnd_2322503 : Nat := 1192560360509231930031509

theorem tailTrace_2322503 : CollatzResearch.WordTrace tailWord_2322503 prefixEnd_2322503 1192560360509231930031509 := by
  unfold tailWord_2322503
  simp only [CollatzResearch.WordTrace]
  refine ⟨84708643504975757778436163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56472429003317171852290775 84708643504975757778436163)
  ·
    refine ⟨127062965257463636667654245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84708643504975757778436163 127062965257463636667654245)
    ·
      refine ⟨23824305985774431875185171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127062965257463636667654245 23824305985774431875185171)
      ·
        refine ⟨35736458978661647812777757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23824305985774431875185171 35736458978661647812777757)
        ·
          refine ⟨13401172116998117929791659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35736458978661647812777757 13401172116998117929791659)
          ·
            refine ⟨20101758175497176894687489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13401172116998117929791659 20101758175497176894687489)
            ·
              refine ⟨15076318631622882671015617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20101758175497176894687489 15076318631622882671015617)
              ·
                refine ⟨11307238973717162003261713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15076318631622882671015617 11307238973717162003261713)
                ·
                  refine ⟨8480429230287871502446285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11307238973717162003261713 8480429230287871502446285)
                  ·
                    refine ⟨3180160961357951813417357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8480429230287871502446285 3180160961357951813417357)
                    ·
                      refine ⟨1192560360509231930031509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3180160961357951813417357 1192560360509231930031509)
                      ·
                        rfl

theorem cell23_2322503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_2322503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322503 prefixEnd_2322503 := by exact prefixLift 2322503
  have htrace : WordTrace (prefixWord ++ tailWord_2322503) baseStart_2322503 baseEnd_2322503 := by
    simpa [prefixWord, tailWord_2322503, baseEnd_2322503] using wordTrace_append hprefix tailTrace_2322503
  have hstable : (prefixWord ++ tailWord_2322503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322503).length < 2 ^ (prefixWord ++ tailWord_2322503).sum := by decide
  have hdescent : baseEnd_2322503 < baseStart_2322503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322506 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_2322506 : Nat := 118140960795 + 2322506 * 2 ^ 59
def prefixEnd_2322506 : Nat := 4983230072969 + 3 ^ 40 * 2322506 * 2
def baseEnd_2322506 : Nat := 397520633650398472764665

theorem tailTrace_2322506 : CollatzResearch.WordTrace tailWord_2322506 prefixEnd_2322506 397520633650398472764665 := by
  unfold tailWord_2322506
  simp only [CollatzResearch.WordTrace]
  refine ⟨21177188230991222322698843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56472501949309926193863581 21177188230991222322698843)
  ·
    refine ⟨31765782346486833484048265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21177188230991222322698843 31765782346486833484048265)
    ·
      refine ⟨23824336759865125113036199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31765782346486833484048265 23824336759865125113036199)
      ·
        refine ⟨35736505139797687669554299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23824336759865125113036199 35736505139797687669554299)
        ·
          refine ⟨53604757709696531504331449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35736505139797687669554299 53604757709696531504331449)
          ·
            refine ⟨40203568282272398628248587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53604757709696531504331449 40203568282272398628248587)
            ·
              refine ⟨60305352423408597942372881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40203568282272398628248587 60305352423408597942372881)
              ·
                refine ⟨45229014317556448456779661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60305352423408597942372881 45229014317556448456779661)
                ·
                  refine ⟨16960880369083668171292373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45229014317556448456779661 16960880369083668171292373)
                  ·
                    refine ⟨397520633650398472764665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16960880369083668171292373 397520633650398472764665)
                    ·
                      rfl

theorem cell23_2322506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_2322506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322506 prefixEnd_2322506 := by exact prefixLift 2322506
  have htrace : WordTrace (prefixWord ++ tailWord_2322506) baseStart_2322506 baseEnd_2322506 := by
    simpa [prefixWord, tailWord_2322506, baseEnd_2322506] using wordTrace_append hprefix tailTrace_2322506
  have hstable : (prefixWord ++ tailWord_2322506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322506).length < 2 ^ (prefixWord ++ tailWord_2322506).sum := by decide
  have hdescent : baseEnd_2322506 < baseStart_2322506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322510 : List Nat := [4, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_2322510 : Nat := 118140960795 + 2322510 * 2 ^ 59
def prefixEnd_2322510 : Nat := 4983230072969 + 3 ^ 40 * 2322510 * 2
def baseEnd_2322510 : Nat := 132507106097090378071553

theorem tailTrace_2322510 : CollatzResearch.WordTrace tailWord_2322510 prefixEnd_2322510 132507106097090378071553 := by
  unfold tailWord_2322510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10588612351993799746742623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56472599210633598649293989 10588612351993799746742623)
  ·
    refine ⟨15882918527990699620113935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10588612351993799746742623 15882918527990699620113935)
    ·
      refine ⟨23824377791986049430170903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15882918527990699620113935 23824377791986049430170903)
      ·
        refine ⟨35736566687979074145256355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23824377791986049430170903 35736566687979074145256355)
        ·
          refine ⟨53604850031968611217884533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35736566687979074145256355 53604850031968611217884533)
          ·
            refine ⟨5025454690497057301676675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53604850031968611217884533 5025454690497057301676675)
            ·
              refine ⟨7538182035745585952515013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025454690497057301676675 7538182035745585952515013)
              ·
                refine ⟨1413409131702297366096565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7538182035745585952515013 1413409131702297366096565)
                ·
                  refine ⟨132507106097090378071553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1413409131702297366096565 132507106097090378071553)
                  ·
                    rfl

theorem cell23_2322510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_2322510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322510 prefixEnd_2322510 := by exact prefixLift 2322510
  have htrace : WordTrace (prefixWord ++ tailWord_2322510) baseStart_2322510 baseEnd_2322510 := by
    simpa [prefixWord, tailWord_2322510, baseEnd_2322510] using wordTrace_append hprefix tailTrace_2322510
  have hstable : (prefixWord ++ tailWord_2322510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322510).length < 2 ^ (prefixWord ++ tailWord_2322510).sum := by decide
  have hdescent : baseEnd_2322510 < baseStart_2322510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322540 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_2322540 : Nat := 118140960795 + 2322540 * 2 ^ 59
def prefixEnd_2322540 : Nat := 4983230072969 + 3 ^ 40 * 2322540 * 2
def baseEnd_2322540 : Nat := 397526453097816095089613

theorem tailTrace_2322540 : CollatzResearch.WordTrace tailWord_2322540 prefixEnd_2322540 397526453097816095089613 := by
  unfold tailWord_2322540
  simp only [CollatzResearch.WordTrace]
  refine ⟨42354996502920856548766537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56473328670561142065022049 42354996502920856548766537)
  ·
    refine ⟨31766247377190642411574903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42354996502920856548766537 31766247377190642411574903)
    ·
      refine ⟨47649371065785963617362355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31766247377190642411574903 47649371065785963617362355)
      ·
        refine ⟨71474056598678945426043533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47649371065785963617362355 71474056598678945426043533)
        ·
          refine ⟨26802771224504604534766325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71474056598678945426043533 26802771224504604534766325)
          ·
            refine ⟨2512759802297306675134343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26802771224504604534766325 2512759802297306675134343)
            ·
              refine ⟨3769139703445960012701515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512759802297306675134343 3769139703445960012701515)
              ·
                refine ⟨5653709555168940019052273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3769139703445960012701515 5653709555168940019052273)
                ·
                  refine ⟨4240282166376705014289205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5653709555168940019052273 4240282166376705014289205)
                  ·
                    refine ⟨397526453097816095089613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4240282166376705014289205 397526453097816095089613)
                    ·
                      rfl

theorem cell23_2322540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_2322540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322540 prefixEnd_2322540 := by exact prefixLift 2322540
  have htrace : WordTrace (prefixWord ++ tailWord_2322540) baseStart_2322540 baseEnd_2322540 := by
    simpa [prefixWord, tailWord_2322540, baseEnd_2322540] using wordTrace_append hprefix tailTrace_2322540
  have hstable : (prefixWord ++ tailWord_2322540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322540).length < 2 ^ (prefixWord ++ tailWord_2322540).sum := by decide
  have hdescent : baseEnd_2322540 < baseStart_2322540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322543 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_2322543 : Nat := 118140960795 + 2322543 * 2 ^ 59
def prefixEnd_2322543 : Nat := 4983230072969 + 3 ^ 40 * 2322543 * 2
def baseEnd_2322543 : Nat := 1192580899735411773531325

theorem tailTrace_2322543 : CollatzResearch.WordTrace tailWord_2322543 prefixEnd_2322543 1192580899735411773531325 := by
  unfold tailWord_2322543
  simp only [CollatzResearch.WordTrace]
  refine ⟨84710102424830844609892283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56473401616553896406594855 84710102424830844609892283)
  ·
    refine ⟨127065153637246266914838425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84710102424830844609892283 127065153637246266914838425)
    ·
      refine ⟨95298865227934700186128819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127065153637246266914838425 95298865227934700186128819)
      ·
        refine ⟨142948297841902050279193229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95298865227934700186128819 142948297841902050279193229)
        ·
          refine ⟨53605611690713268854697461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142948297841902050279193229 53605611690713268854697461)
          ·
            refine ⟨5025526096004368955127887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53605611690713268854697461 5025526096004368955127887)
            ·
              refine ⟨7538289144006553432691831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025526096004368955127887 7538289144006553432691831)
              ·
                refine ⟨11307433716009830149037747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7538289144006553432691831 11307433716009830149037747)
                ·
                  refine ⟨16961150574014745223556621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11307433716009830149037747 16961150574014745223556621)
                  ·
                    refine ⟨6360431465255529458833733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16961150574014745223556621 6360431465255529458833733)
                    ·
                      refine ⟨1192580899735411773531325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6360431465255529458833733 1192580899735411773531325)
                      ·
                        rfl

theorem cell23_2322543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_2322543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322543 prefixEnd_2322543 := by exact prefixLift 2322543
  have htrace : WordTrace (prefixWord ++ tailWord_2322543) baseStart_2322543 baseEnd_2322543 := by
    simpa [prefixWord, tailWord_2322543, baseEnd_2322543] using wordTrace_append hprefix tailTrace_2322543
  have hstable : (prefixWord ++ tailWord_2322543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322543).length < 2 ^ (prefixWord ++ tailWord_2322543).sum := by decide
  have hdescent : baseEnd_2322543 < baseStart_2322543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322570 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_2322570 : Nat := 118140960795 + 2322570 * 2 ^ 59
def prefixEnd_2322570 : Nat := 4983230072969 + 3 ^ 40 * 2322570 * 2
def baseEnd_2322570 : Nat := 397531587904361055964567

theorem tailTrace_2322570 : CollatzResearch.WordTrace tailWord_2322570 prefixEnd_2322570 397531587904361055964567 := by
  unfold tailWord_2322570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21177771798933257055281291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56474058130488685480750109 21177771798933257055281291)
  ·
    refine ⟨31766657698399885582921937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21177771798933257055281291 31766657698399885582921937)
    ·
      refine ⟨23824993273799914187191453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31766657698399885582921937 23824993273799914187191453)
      ·
        refine ⟨8934372477674967820196795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23824993273799914187191453 8934372477674967820196795)
        ·
          refine ⟨13401558716512451730295193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8934372477674967820196795 13401558716512451730295193)
          ·
            refine ⟨10051169037384338797721395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13401558716512451730295193 10051169037384338797721395)
            ·
              refine ⟨15076753556076508196582093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10051169037384338797721395 15076753556076508196582093)
              ·
                refine ⟨5653782583528690573718285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15076753556076508196582093 5653782583528690573718285)
                ·
                  refine ⟨2120168468823258965144357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5653782583528690573718285 2120168468823258965144357)
                  ·
                    refine ⟨397531587904361055964567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2120168468823258965144357 397531587904361055964567)
                    ·
                      rfl

theorem cell23_2322570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_2322570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322570 prefixEnd_2322570 := by exact prefixLift 2322570
  have htrace : WordTrace (prefixWord ++ tailWord_2322570) baseStart_2322570 baseEnd_2322570 := by
    simpa [prefixWord, tailWord_2322570, baseEnd_2322570] using wordTrace_append hprefix tailTrace_2322570
  have hstable : (prefixWord ++ tailWord_2322570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322570).length < 2 ^ (prefixWord ++ tailWord_2322570).sum := by decide
  have hdescent : baseEnd_2322570 < baseStart_2322570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322650 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2]
def baseStart_2322650 : Nat := 118140960795 + 2322650 * 2 ^ 59
def prefixEnd_2322650 : Nat := 4983230072969 + 3 ^ 40 * 2322650 * 2
def baseEnd_2322650 : Nat := 1192635842165442854893333

theorem tailTrace_2322650 : CollatzResearch.WordTrace tailWord_2322650 prefixEnd_2322650 1192635842165442854893333 := by
  unfold tailWord_2322650
  simp only [CollatzResearch.WordTrace]
  refine ⟨21178501258860800471009351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56476003356962134589358269 21178501258860800471009351)
  ·
    refine ⟨31767751888291200706514027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21178501258860800471009351 31767751888291200706514027)
    ·
      refine ⟨47651627832436801059771041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31767751888291200706514027 47651627832436801059771041)
      ·
        refine ⟨35738720874327600794828281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47651627832436801059771041 35738720874327600794828281)
        ·
          refine ⟨26804040655745700596121211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35738720874327600794828281 26804040655745700596121211)
          ·
            refine ⟨40206060983618550894181817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26804040655745700596121211 40206060983618550894181817)
            ·
              refine ⟨30154545737713913170636363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40206060983618550894181817 30154545737713913170636363)
              ·
                refine ⟨45231818606570869755954545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30154545737713913170636363 45231818606570869755954545)
                ·
                  refine ⟨33923863954928152316965909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45231818606570869755954545 33923863954928152316965909)
                  ·
                    refine ⟨1590181122887257139857777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33923863954928152316965909 1590181122887257139857777)
                    ·
                      refine ⟨1192635842165442854893333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1590181122887257139857777 1192635842165442854893333)
                      ·
                        rfl

theorem cell23_2322650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_2322650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322650 prefixEnd_2322650 := by exact prefixLift 2322650
  have htrace : WordTrace (prefixWord ++ tailWord_2322650) baseStart_2322650 baseEnd_2322650 := by
    simpa [prefixWord, tailWord_2322650, baseEnd_2322650] using wordTrace_append hprefix tailTrace_2322650
  have hstable : (prefixWord ++ tailWord_2322650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322650).length < 2 ^ (prefixWord ++ tailWord_2322650).sum := by decide
  have hdescent : baseEnd_2322650 < baseStart_2322650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322667 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 1, 1, 4]
def baseStart_2322667 : Nat := 118140960795 + 2322667 * 2 ^ 59
def prefixEnd_2322667 : Nat := 4983230072969 + 3 ^ 40 * 2322667 * 2
def baseEnd_2322667 : Nat := 1192644571336569288380755

theorem tailTrace_2322667 : CollatzResearch.WordTrace tailWord_2322667 prefixEnd_2322667 1192644571336569288380755 := by
  unfold tailWord_2322667
  simp only [CollatzResearch.WordTrace]
  refine ⟨84714625076381613787406255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56476416717587742524937503 84714625076381613787406255)
  ·
    refine ⟨127071937614572420681109383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84714625076381613787406255 127071937614572420681109383)
    ·
      refine ⟨190607906421858631021664075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127071937614572420681109383 190607906421858631021664075)
      ·
        refine ⟨285911859632787946532496113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190607906421858631021664075 285911859632787946532496113)
        ·
          refine ⟨214433894724590959899372085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285911859632787946532496113 214433894724590959899372085)
          ·
            refine ⟨20103177630430402490566133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214433894724590959899372085 20103177630430402490566133)
            ·
              refine ⟨1884672902852850233490575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20103177630430402490566133 1884672902852850233490575)
              ·
                refine ⟨2827009354279275350235863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884672902852850233490575 2827009354279275350235863)
                ·
                  refine ⟨4240514031418913025353795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827009354279275350235863 4240514031418913025353795)
                  ·
                    refine ⟨6360771047128369538030693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4240514031418913025353795 6360771047128369538030693)
                    ·
                      refine ⟨1192644571336569288380755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6360771047128369538030693 1192644571336569288380755)
                      ·
                        rfl

theorem cell23_2322667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 1, 4].length) (baseStart_2322667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322667 prefixEnd_2322667 := by exact prefixLift 2322667
  have htrace : WordTrace (prefixWord ++ tailWord_2322667) baseStart_2322667 baseEnd_2322667 := by
    simpa [prefixWord, tailWord_2322667, baseEnd_2322667] using wordTrace_append hprefix tailTrace_2322667
  have hstable : (prefixWord ++ tailWord_2322667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322667).length < 2 ^ (prefixWord ++ tailWord_2322667).sum := by decide
  have hdescent : baseEnd_2322667 < baseStart_2322667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322718 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2322718 : Nat := 118140960795 + 2322718 * 2 ^ 59
def prefixEnd_2322718 : Nat := 4983230072969 + 3 ^ 40 * 2322718 * 2
def baseEnd_2322718 : Nat := 1192670758849948588843021

theorem tailTrace_2322718 : CollatzResearch.WordTrace tailWord_2322718 prefixEnd_2322718 1192670758849948588843021 := by
  unfold tailWord_2322718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10589560649899606187189101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56477656799464566331675205 10589560649899606187189101)
  ·
    refine ⟨3971085243712352320195913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10589560649899606187189101 3971085243712352320195913)
    ·
      refine ⟨2978313932784264240146935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3971085243712352320195913 2978313932784264240146935)
      ·
        refine ⟨4467470899176396360220403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2978313932784264240146935 4467470899176396360220403)
        ·
          refine ⟨6701206348764594540330605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4467470899176396360220403 6701206348764594540330605)
          ·
            refine ⟨2512952380786722952623977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6701206348764594540330605 2512952380786722952623977)
            ·
              refine ⟨1884714285590042214467983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2512952380786722952623977 1884714285590042214467983)
              ·
                refine ⟨2827071428385063321701975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884714285590042214467983 2827071428385063321701975)
                ·
                  refine ⟨4240607142577594982552963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827071428385063321701975 4240607142577594982552963)
                  ·
                    refine ⟨6360910713866392473829445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4240607142577594982552963 6360910713866392473829445)
                    ·
                      refine ⟨1192670758849948588843021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6360910713866392473829445 1192670758849948588843021)
                      ·
                        rfl

theorem cell23_2322718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2322718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322718 prefixEnd_2322718 := by exact prefixLift 2322718
  have htrace : WordTrace (prefixWord ++ tailWord_2322718) baseStart_2322718 baseEnd_2322718 := by
    simpa [prefixWord, tailWord_2322718, baseEnd_2322718] using wordTrace_append hprefix tailTrace_2322718
  have hstable : (prefixWord ++ tailWord_2322718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322718).length < 2 ^ (prefixWord ++ tailWord_2322718).sum := by decide
  have hdescent : baseEnd_2322718 < baseStart_2322718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322760 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_2322760 : Nat := 118140960795 + 2322760 * 2 ^ 59
def prefixEnd_2322760 : Nat := 4983230072969 + 3 ^ 40 * 2322760 * 2
def baseEnd_2322760 : Nat := 1192692325037437424517827

theorem tailTrace_2322760 : CollatzResearch.WordTrace tailWord_2322760 prefixEnd_2322760 1192692325037437424517827 := by
  unfold tailWord_2322760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42359008532522345335270867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56478678043363127113694489 42359008532522345335270867)
  ·
    refine ⟨63538512798783518002906301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42359008532522345335270867 63538512798783518002906301)
    ·
      refine ⟨23826942299543819251089863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63538512798783518002906301 23826942299543819251089863)
      ·
        refine ⟨35740413449315728876634795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23826942299543819251089863 35740413449315728876634795)
        ·
          refine ⟨53610620173973593314952193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35740413449315728876634795 53610620173973593314952193)
          ·
            refine ⟨40207965130480194986214145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53610620173973593314952193 40207965130480194986214145)
            ·
              refine ⟨30155973847860146239660609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40207965130480194986214145 30155973847860146239660609)
              ·
                refine ⟨22616980385895109679745457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30155973847860146239660609 22616980385895109679745457)
                ·
                  refine ⟨16962735289421332259809093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22616980385895109679745457 16962735289421332259809093)
                  ·
                    refine ⟨3180512866766499798714205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16962735289421332259809093 3180512866766499798714205)
                    ·
                      refine ⟨1192692325037437424517827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3180512866766499798714205 1192692325037437424517827)
                      ·
                        rfl

theorem cell23_2322760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_2322760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322760 prefixEnd_2322760 := by exact prefixLift 2322760
  have htrace : WordTrace (prefixWord ++ tailWord_2322760) baseStart_2322760 baseEnd_2322760 := by
    simpa [prefixWord, tailWord_2322760, baseEnd_2322760] using wordTrace_append hprefix tailTrace_2322760
  have hstable : (prefixWord ++ tailWord_2322760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322760).length < 2 ^ (prefixWord ++ tailWord_2322760).sum := by decide
  have hdescent : baseEnd_2322760 < baseStart_2322760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322763 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 9]
def baseStart_2322763 : Nat := 118140960795 + 2322763 * 2 ^ 59
def prefixEnd_2322763 : Nat := 4983230072969 + 3 ^ 40 * 2322763 * 2
def baseEnd_2322763 : Nat := 132521540608822323642257

theorem tailTrace_2322763 : CollatzResearch.WordTrace tailWord_2322763 prefixEnd_2322763 132521540608822323642257 := by
  unfold tailWord_2322763
  simp only [CollatzResearch.WordTrace]
  refine ⟨84718126484033822182900943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56478750989355881455267295 84718126484033822182900943)
  ·
    refine ⟨127077189726050733274351415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84718126484033822182900943 127077189726050733274351415)
    ·
      refine ⟨190615784589076099911527123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127077189726050733274351415 190615784589076099911527123)
      ·
        refine ⟨285923676883614149867290685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190615784589076099911527123 285923676883614149867290685)
        ·
          refine ⟨107221378831355306200234007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285923676883614149867290685 107221378831355306200234007)
          ·
            refine ⟨160832068247032959300351011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107221378831355306200234007 160832068247032959300351011)
            ·
              refine ⟨241248102370549438950526517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160832068247032959300351011 241248102370549438950526517)
              ·
                refine ⟨22617009597239009901611861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241248102370549438950526517 22617009597239009901611861)
                ·
                  refine ⟨132521540608822323642257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22617009597239009901611861 132521540608822323642257)
                  ·
                    rfl

theorem cell23_2322763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 9].length) (baseStart_2322763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322763 prefixEnd_2322763 := by exact prefixLift 2322763
  have htrace : WordTrace (prefixWord ++ tailWord_2322763) baseStart_2322763 baseEnd_2322763 := by
    simpa [prefixWord, tailWord_2322763, baseEnd_2322763] using wordTrace_append hprefix tailTrace_2322763
  have hstable : (prefixWord ++ tailWord_2322763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322763).length < 2 ^ (prefixWord ++ tailWord_2322763).sum := by decide
  have hdescent : baseEnd_2322763 < baseStart_2322763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322770 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2322770 : Nat := 118140960795 + 2322770 * 2 ^ 59
def prefixEnd_2322770 : Nat := 4983230072969 + 3 ^ 40 * 2322770 * 2
def baseEnd_2322770 : Nat := 1192697459843982385392781

theorem tailTrace_2322770 : CollatzResearch.WordTrace tailWord_2322770 prefixEnd_2322770 1192697459843982385392781 := by
  unfold tailWord_2322770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21179595448752115594601441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56478921196672308252270509 21179595448752115594601441)
  ·
    refine ⟨15884696586564086695951081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21179595448752115594601441 15884696586564086695951081)
    ·
      refine ⟨11913522439923065021963311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15884696586564086695951081 11913522439923065021963311)
      ·
        refine ⟨17870283659884597532944967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11913522439923065021963311 17870283659884597532944967)
        ·
          refine ⟨26805425489826896299417451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17870283659884597532944967 26805425489826896299417451)
          ·
            refine ⟨40208138234740344449126177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26805425489826896299417451 40208138234740344449126177)
            ·
              refine ⟨30156103676055258336844633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40208138234740344449126177 30156103676055258336844633)
              ·
                refine ⟨22617077757041443752633475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30156103676055258336844633 22617077757041443752633475)
                ·
                  refine ⟨33925616635562165628950213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22617077757041443752633475 33925616635562165628950213)
                  ·
                    refine ⟨6361053119167906055428165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33925616635562165628950213 6361053119167906055428165)
                    ·
                      refine ⟨1192697459843982385392781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6361053119167906055428165 1192697459843982385392781)
                      ·
                        rfl

theorem cell23_2322770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2322770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322770 prefixEnd_2322770 := by exact prefixLift 2322770
  have htrace : WordTrace (prefixWord ++ tailWord_2322770) baseStart_2322770 baseEnd_2322770 := by
    simpa [prefixWord, tailWord_2322770, baseEnd_2322770] using wordTrace_append hprefix tailTrace_2322770
  have hstable : (prefixWord ++ tailWord_2322770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322770).length < 2 ^ (prefixWord ++ tailWord_2322770).sum := by decide
  have hdescent : baseEnd_2322770 < baseStart_2322770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322820 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2322820 : Nat := 118140960795 + 2322820 * 2 ^ 59
def prefixEnd_2322820 : Nat := 4983230072969 + 3 ^ 40 * 2322820 * 2
def baseEnd_2322820 : Nat := 1192723133876707189767551

theorem tailTrace_2322820 : CollatzResearch.WordTrace tailWord_2322820 prefixEnd_2322820 1192723133876707189767551 := by
  unfold tailWord_2322820
  simp only [CollatzResearch.WordTrace]
  refine ⟨42360102722413660458862957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56480136963218213945150609 42360102722413660458862957)
  ·
    refine ⟨15885038520905122672073609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42360102722413660458862957 15885038520905122672073609)
    ·
      refine ⟨11913778890678842004055207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15885038520905122672073609 11913778890678842004055207)
      ·
        refine ⟨17870668336018263006082811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11913778890678842004055207 17870668336018263006082811)
        ·
          refine ⟨26806002504027394509124217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17870668336018263006082811 26806002504027394509124217)
          ·
            refine ⟨20104501878020545881843163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26806002504027394509124217 20104501878020545881843163)
            ·
              refine ⟨30156752817030818822764745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20104501878020545881843163 30156752817030818822764745)
              ·
                refine ⟨22617564612773114117073559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30156752817030818822764745 22617564612773114117073559)
                ·
                  refine ⟨33926346919159671175610339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22617564612773114117073559 33926346919159671175610339)
                  ·
                    refine ⟨50889520378739506763415509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33926346919159671175610339 50889520378739506763415509)
                    ·
                      refine ⟨1192723133876707189767551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50889520378739506763415509 1192723133876707189767551)
                      ·
                        rfl

theorem cell23_2322820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2322820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322820 prefixEnd_2322820 := by exact prefixLift 2322820
  have htrace : WordTrace (prefixWord ++ tailWord_2322820) baseStart_2322820 baseEnd_2322820 := by
    simpa [prefixWord, tailWord_2322820, baseEnd_2322820] using wordTrace_append hprefix tailTrace_2322820
  have hstable : (prefixWord ++ tailWord_2322820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322820).length < 2 ^ (prefixWord ++ tailWord_2322820).sum := by decide
  have hdescent : baseEnd_2322820 < baseStart_2322820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322827 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 2, 5]
def baseStart_2322827 : Nat := 118140960795 + 2322827 * 2 ^ 59
def prefixEnd_2322827 : Nat := 4983230072969 + 3 ^ 40 * 2322827 * 2
def baseEnd_2322827 : Nat := 397575576080429554126673

theorem tailTrace_2322827 : CollatzResearch.WordTrace tailWord_2322827 prefixEnd_2322827 397575576080429554126673 := by
  unfold tailWord_2322827
  simp only [CollatzResearch.WordTrace]
  refine ⟨84720460755801961113230735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56480307170534640742153823 84720460755801961113230735)
  ·
    refine ⟨127080691133702941669846103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84720460755801961113230735 127080691133702941669846103)
    ·
      refine ⟨190621036700554412504769155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127080691133702941669846103 190621036700554412504769155)
      ·
        refine ⟨285931555050831618757153733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190621036700554412504769155 285931555050831618757153733)
        ·
          refine ⟨53612166572030928516966325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285931555050831618757153733 53612166572030928516966325)
          ·
            refine ⟨5026140616127899548465593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53612166572030928516966325 5026140616127899548465593)
            ·
              refine ⟨3769605462095924661349195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5026140616127899548465593 3769605462095924661349195)
              ·
                refine ⟨5654408193143886992023793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3769605462095924661349195 5654408193143886992023793)
                ·
                  refine ⟨4240806144857915244017845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5654408193143886992023793 4240806144857915244017845)
                  ·
                    refine ⟨397575576080429554126673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4240806144857915244017845 397575576080429554126673)
                    ·
                      rfl

theorem cell23_2322827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 5].length) (baseStart_2322827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322827 prefixEnd_2322827 := by exact prefixLift 2322827
  have htrace : WordTrace (prefixWord ++ tailWord_2322827) baseStart_2322827 baseEnd_2322827 := by
    simpa [prefixWord, tailWord_2322827, baseEnd_2322827] using wordTrace_append hprefix tailTrace_2322827
  have hstable : (prefixWord ++ tailWord_2322827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322827).length < 2 ^ (prefixWord ++ tailWord_2322827).sum := by decide
  have hdescent : baseEnd_2322827 < baseStart_2322827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322847 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2322847 : Nat := 118140960795 + 2322847 * 2 ^ 59
def prefixEnd_2322847 : Nat := 4983230072969 + 3 ^ 40 * 2322847 * 2
def baseEnd_2322847 : Nat := 1192736997854378584129927

theorem tailTrace_2322847 : CollatzResearch.WordTrace tailWord_2322847 prefixEnd_2322847 1192736997854378584129927 := by
  unfold tailWord_2322847
  simp only [CollatzResearch.WordTrace]
  refine ⟨84721190215729504528958795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56480793477153003019305863 84721190215729504528958795)
  ·
    refine ⟨127081785323594256793438193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84721190215729504528958795 127081785323594256793438193)
    ·
      refine ⟨95311338992695692595078645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127081785323594256793438193 95311338992695692595078645)
      ·
        refine ⟨8935438030565221180788623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95311338992695692595078645 8935438030565221180788623)
        ·
          refine ⟨13403157045847831771182935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8935438030565221180788623 13403157045847831771182935)
          ·
            refine ⟨20104735568771747656774403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13403157045847831771182935 20104735568771747656774403)
            ·
              refine ⟨30157103353157621485161605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20104735568771747656774403 30157103353157621485161605)
              ·
                refine ⟨5654456878717054028467801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30157103353157621485161605 5654456878717054028467801)
                ·
                  refine ⟨4240842659037790521350851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5654456878717054028467801 4240842659037790521350851)
                  ·
                    refine ⟨6361263988556685782026277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4240842659037790521350851 6361263988556685782026277)
                    ·
                      refine ⟨1192736997854378584129927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6361263988556685782026277 1192736997854378584129927)
                      ·
                        rfl

theorem cell23_2322847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2322847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322847 prefixEnd_2322847 := by exact prefixLift 2322847
  have htrace : WordTrace (prefixWord ++ tailWord_2322847) baseStart_2322847 baseEnd_2322847 := by
    simpa [prefixWord, tailWord_2322847, baseEnd_2322847] using wordTrace_append hprefix tailTrace_2322847
  have hstable : (prefixWord ++ tailWord_2322847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322847).length < 2 ^ (prefixWord ++ tailWord_2322847).sum := by decide
  have hdescent : baseEnd_2322847 < baseStart_2322847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322858 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2322858 : Nat := 118140960795 + 2322858 * 2 ^ 59
def prefixEnd_2322858 : Nat := 4983230072969 + 3 ^ 40 * 2322858 * 2
def baseEnd_2322858 : Nat := 1192742646141578041092377

theorem tailTrace_2322858 : CollatzResearch.WordTrace tailWord_2322858 prefixEnd_2322858 1192742646141578041092377 := by
  unfold tailWord_2322858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21180397854672413351902307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56481060945793102271739485 21180397854672413351902307)
  ·
    refine ⟨31770596782008620027853461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21180397854672413351902307 31770596782008620027853461)
    ·
      refine ⟨1489246724156654063805631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31770596782008620027853461 1489246724156654063805631)
      ·
        refine ⟨2233870086234981095708447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489246724156654063805631 2233870086234981095708447)
        ·
          refine ⟨3350805129352471643562671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233870086234981095708447 3350805129352471643562671)
          ·
            refine ⟨5026207694028707465344007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350805129352471643562671 5026207694028707465344007)
            ·
              refine ⟨7539311541043061198016011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026207694028707465344007 7539311541043061198016011)
              ·
                refine ⟨11308967311564591797024017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7539311541043061198016011 11308967311564591797024017)
                ·
                  refine ⟨8481725483673443847768013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11308967311564591797024017 8481725483673443847768013)
                  ·
                    refine ⟨3180647056377541442913005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8481725483673443847768013 3180647056377541442913005)
                    ·
                      refine ⟨1192742646141578041092377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3180647056377541442913005 1192742646141578041092377)
                      ·
                        rfl

theorem cell23_2322858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2322858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322858 prefixEnd_2322858 := by exact prefixLift 2322858
  have htrace : WordTrace (prefixWord ++ tailWord_2322858) baseStart_2322858 baseEnd_2322858 := by
    simpa [prefixWord, tailWord_2322858, baseEnd_2322858] using wordTrace_append hprefix tailTrace_2322858
  have hstable : (prefixWord ++ tailWord_2322858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322858).length < 2 ^ (prefixWord ++ tailWord_2322858).sum := by decide
  have hdescent : baseEnd_2322858 < baseStart_2322858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322860 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_2322860 : Nat := 118140960795 + 2322860 * 2 ^ 59
def prefixEnd_2322860 : Nat := 4983230072969 + 3 ^ 40 * 2322860 * 2
def baseEnd_2322860 : Nat := 1192743673102887033267367

theorem tailTrace_2322860 : CollatzResearch.WordTrace tailWord_2322860 prefixEnd_2322860 1192743673102887033267367 := by
  unfold tailWord_2322860
  simp only [CollatzResearch.WordTrace]
  refine ⟨42360832182341203874591017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56481109576454938499454689 42360832182341203874591017)
  ·
    refine ⟨31770624136755902905943263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42360832182341203874591017 31770624136755902905943263)
    ·
      refine ⟨47655936205133854358914895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31770624136755902905943263 47655936205133854358914895)
      ·
        refine ⟨71483904307700781538372343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47655936205133854358914895 71483904307700781538372343)
        ·
          refine ⟨107225856461551172307558515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71483904307700781538372343 107225856461551172307558515)
          ·
            refine ⟨160838784692326758461337773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107225856461551172307558515 160838784692326758461337773)
            ·
              refine ⟨60314544259622534423001665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160838784692326758461337773 60314544259622534423001665)
              ·
                refine ⟨45235908194716900817251249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60314544259622534423001665 45235908194716900817251249)
                ·
                  refine ⟨33926931146037675612938437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45235908194716900817251249 33926931146037675612938437)
                  ·
                    refine ⟨6361299589882064177425957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33926931146037675612938437 6361299589882064177425957)
                    ·
                      refine ⟨1192743673102887033267367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6361299589882064177425957 1192743673102887033267367)
                      ·
                        rfl

theorem cell23_2322860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_2322860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322860 prefixEnd_2322860 := by exact prefixLift 2322860
  have htrace : WordTrace (prefixWord ++ tailWord_2322860) baseStart_2322860 baseEnd_2322860 := by
    simpa [prefixWord, tailWord_2322860, baseEnd_2322860] using wordTrace_append hprefix tailTrace_2322860
  have hstable : (prefixWord ++ tailWord_2322860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322860).length < 2 ^ (prefixWord ++ tailWord_2322860).sum := by decide
  have hdescent : baseEnd_2322860 < baseStart_2322860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322937 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_2322937 : Nat := 118140960795 + 2322937 * 2 ^ 59
def prefixEnd_2322937 : Nat := 4983230072969 + 3 ^ 40 * 2322937 * 2
def baseEnd_2322937 : Nat := 1192783211113283232004513

theorem tailTrace_2322937 : CollatzResearch.WordTrace tailWord_2322937 prefixEnd_2322937 1192783211113283232004513 := by
  unfold tailWord_2322937
  simp only [CollatzResearch.WordTrace]
  refine ⟨84724472785403449899735065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56482981856935633266490043 84724472785403449899735065)
  ·
    refine ⟨63543354589052587424801299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84724472785403449899735065 63543354589052587424801299)
    ·
      refine ⟨95315031883578881137201949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63543354589052587424801299 95315031883578881137201949)
      ·
        refine ⟨35743136956342080426450731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95315031883578881137201949 35743136956342080426450731)
        ·
          refine ⟨53614705434513120639676097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35743136956342080426450731 53614705434513120639676097)
          ·
            refine ⟨40211029075884840479757073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53614705434513120639676097 40211029075884840479757073)
            ·
              refine ⟨30158271806913630359817805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40211029075884840479757073 30158271806913630359817805)
              ·
                refine ⟨11309351927592611384931677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30158271806913630359817805 11309351927592611384931677)
                ·
                  refine ⟨4241006972847229269349379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11309351927592611384931677 4241006972847229269349379)
                  ·
                    refine ⟨6361510459270843904024069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4241006972847229269349379 6361510459270843904024069)
                    ·
                      refine ⟨1192783211113283232004513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6361510459270843904024069 1192783211113283232004513)
                      ·
                        rfl

theorem cell23_2322937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_2322937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322937 prefixEnd_2322937 := by exact prefixLift 2322937
  have htrace : WordTrace (prefixWord ++ tailWord_2322937) baseStart_2322937 baseEnd_2322937 := by
    simpa [prefixWord, tailWord_2322937, baseEnd_2322937] using wordTrace_append hprefix tailTrace_2322937
  have hstable : (prefixWord ++ tailWord_2322937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322937).length < 2 ^ (prefixWord ++ tailWord_2322937).sum := by decide
  have hdescent : baseEnd_2322937 < baseStart_2322937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322947 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 6, 4]
def baseStart_2322947 : Nat := 118140960795 + 2322947 * 2 ^ 59
def prefixEnd_2322947 : Nat := 4983230072969 + 3 ^ 40 * 2322947 * 2
def baseEnd_2322947 : Nat := 397596115306609397626489

theorem tailTrace_2322947 : CollatzResearch.WordTrace tailWord_2322947 prefixEnd_2322947 397596115306609397626489 := by
  unfold tailWord_2322947
  simp only [CollatzResearch.WordTrace]
  refine ⟨84724837515367221607599095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56483225010244814405066063 84724837515367221607599095)
  ·
    refine ⟨127087256273050832411398643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84724837515367221607599095 127087256273050832411398643)
    ·
      refine ⟨190630884409576248617097965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127087256273050832411398643 190630884409576248617097965)
      ·
        refine ⟨71486581653591093231411737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190630884409576248617097965 71486581653591093231411737)
        ·
          refine ⟨53614936240193319923558803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71486581653591093231411737 53614936240193319923558803)
          ·
            refine ⟨80422404360289979885338205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53614936240193319923558803 80422404360289979885338205)
            ·
              refine ⟨30158401635108742457001827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80422404360289979885338205 30158401635108742457001827)
              ·
                refine ⟨45237602452663113685502741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30158401635108742457001827 45237602452663113685502741)
                ·
                  refine ⟨2120512614968583454007941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45237602452663113685502741 2120512614968583454007941)
                  ·
                    refine ⟨397596115306609397626489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2120512614968583454007941 397596115306609397626489)
                    ·
                      rfl

theorem cell23_2322947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 4].length) (baseStart_2322947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322947 prefixEnd_2322947 := by exact prefixLift 2322947
  have htrace : WordTrace (prefixWord ++ tailWord_2322947) baseStart_2322947 baseEnd_2322947 := by
    simpa [prefixWord, tailWord_2322947, baseEnd_2322947] using wordTrace_append hprefix tailTrace_2322947
  have hstable : (prefixWord ++ tailWord_2322947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322947).length < 2 ^ (prefixWord ++ tailWord_2322947).sum := by decide
  have hdescent : baseEnd_2322947 < baseStart_2322947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322954 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_2322954 : Nat := 118140960795 + 2322954 * 2 ^ 59
def prefixEnd_2322954 : Nat := 4983230072969 + 3 ^ 40 * 2322954 * 2
def baseEnd_2322954 : Nat := 1192791940284409665491935

theorem tailTrace_2322954 : CollatzResearch.WordTrace tailWord_2322954 prefixEnd_2322954 1192791940284409665491935 := by
  unfold tailWord_2322954
  simp only [CollatzResearch.WordTrace]
  refine ⟨21181273206585465450775979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56483395217561241202069277 21181273206585465450775979)
  ·
    refine ⟨31771909809878198176163969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21181273206585465450775979 31771909809878198176163969)
    ·
      refine ⟨23828932357408648632122977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31771909809878198176163969 23828932357408648632122977)
      ·
        refine ⟨17871699268056486474092233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23828932357408648632122977 17871699268056486474092233)
        ·
          refine ⟨13403774451042364855569175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17871699268056486474092233 13403774451042364855569175)
          ·
            refine ⟨20105661676563547283353763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13403774451042364855569175 20105661676563547283353763)
            ·
              refine ⟨30158492514845320925030645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20105661676563547283353763 30158492514845320925030645)
              ·
                refine ⟨2827358673266748836721623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30158492514845320925030645 2827358673266748836721623)
                ·
                  refine ⟨4241038009900123255082435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827358673266748836721623 4241038009900123255082435)
                  ·
                    refine ⟨6361557014850184882623653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4241038009900123255082435 6361557014850184882623653)
                    ·
                      refine ⟨1192791940284409665491935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6361557014850184882623653 1192791940284409665491935)
                      ·
                        rfl

theorem cell23_2322954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_2322954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322954 prefixEnd_2322954 := by exact prefixLift 2322954
  have htrace : WordTrace (prefixWord ++ tailWord_2322954) baseStart_2322954 baseEnd_2322954 := by
    simpa [prefixWord, tailWord_2322954, baseEnd_2322954] using wordTrace_append hprefix tailTrace_2322954
  have hstable : (prefixWord ++ tailWord_2322954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322954).length < 2 ^ (prefixWord ++ tailWord_2322954).sum := by decide
  have hdescent : baseEnd_2322954 < baseStart_2322954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322977 : List Nat := [1, 2, 3, 2, 2, 1, 4, 8]
def baseStart_2322977 : Nat := 118140960795 + 2322977 * 2 ^ 59
def prefixEnd_2322977 : Nat := 4983230072969 + 3 ^ 40 * 2322977 * 2
def baseEnd_2322977 : Nat := 44177916679239373166827

theorem tailTrace_2322977 : CollatzResearch.WordTrace tailWord_2322977 prefixEnd_2322977 44177916679239373166827 := by
  unfold tailWord_2322977
  simp only [CollatzResearch.WordTrace]
  refine ⟨84725931705258536731191185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56483954470172357820794123 84725931705258536731191185)
  ·
    refine ⟨63544448778943902548393389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84725931705258536731191185 63544448778943902548393389)
    ·
      refine ⟨23829168292103963455647521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63544448778943902548393389 23829168292103963455647521)
      ·
        refine ⟨17871876219077972591735641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23829168292103963455647521 17871876219077972591735641)
        ·
          refine ⟨13403907164308479443801731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17871876219077972591735641 13403907164308479443801731)
          ·
            refine ⟨20105860746462719165702597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13403907164308479443801731 20105860746462719165702597)
            ·
              refine ⟨3769848889961759843569237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20105860746462719165702597 3769848889961759843569237)
              ·
                refine ⟨44177916679239373166827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3769848889961759843569237 44177916679239373166827)
                ·
                  rfl

theorem cell23_2322977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 8].length) (baseStart_2322977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322977 prefixEnd_2322977 := by exact prefixLift 2322977
  have htrace : WordTrace (prefixWord ++ tailWord_2322977) baseStart_2322977 baseEnd_2322977 := by
    simpa [prefixWord, tailWord_2322977, baseEnd_2322977] using wordTrace_append hprefix tailTrace_2322977
  have hstable : (prefixWord ++ tailWord_2322977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322977).length < 2 ^ (prefixWord ++ tailWord_2322977).sum := by decide
  have hdescent : baseEnd_2322977 < baseStart_2322977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322981 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_2322981 : Nat := 118140960795 + 2322981 * 2 ^ 59
def prefixEnd_2322981 : Nat := 4983230072969 + 3 ^ 40 * 2322981 * 2
def baseEnd_2322981 : Nat := 397601934754027019951437

theorem tailTrace_2322981 : CollatzResearch.WordTrace tailWord_2322981 prefixEnd_2322981 397601934754027019951437 := by
  unfold tailWord_2322981
  simp only [CollatzResearch.WordTrace]
  refine ⟨84726077597244045414336797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56484051731496030276224531 84726077597244045414336797)
  ·
    refine ⟨31772279098966517030376299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84726077597244045414336797 31772279098966517030376299)
    ·
      refine ⟨47658418648449775545564449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31772279098966517030376299 47658418648449775545564449)
      ·
        refine ⟨35743813986337331659173337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47658418648449775545564449 35743813986337331659173337)
        ·
          refine ⟨26807860489752998744380003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35743813986337331659173337 26807860489752998744380003)
          ·
            refine ⟨40211790734629498116570005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26807860489752998744380003 40211790734629498116570005)
            ·
              refine ⟨1884927690685757724214219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40211790734629498116570005 1884927690685757724214219)
              ·
                refine ⟨2827391536028636586321329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884927690685757724214219 2827391536028636586321329)
                ·
                  refine ⟨2120543652021477439740997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827391536028636586321329 2120543652021477439740997)
                  ·
                    refine ⟨397601934754027019951437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2120543652021477439740997 397601934754027019951437)
                    ·
                      rfl

theorem cell23_2322981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_2322981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322981 prefixEnd_2322981 := by exact prefixLift 2322981
  have htrace : WordTrace (prefixWord ++ tailWord_2322981) baseStart_2322981 baseEnd_2322981 := by
    simpa [prefixWord, tailWord_2322981, baseEnd_2322981] using wordTrace_append hprefix tailTrace_2322981
  have hstable : (prefixWord ++ tailWord_2322981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322981).length < 2 ^ (prefixWord ++ tailWord_2322981).sum := by decide
  have hdescent : baseEnd_2322981 < baseStart_2322981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322984 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2322984 : Nat := 118140960795 + 2322984 * 2 ^ 59
def prefixEnd_2322984 : Nat := 4983230072969 + 3 ^ 40 * 2322984 * 2
def baseEnd_2322984 : Nat := 1192807344704044548116797

theorem tailTrace_2322984 : CollatzResearch.WordTrace tailWord_2322984 prefixEnd_2322984 1192807344704044548116797 := by
  unfold tailWord_2322984
  simp only [CollatzResearch.WordTrace]
  refine ⟨42363093508116588463348003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56484124677488784617797337 42363093508116588463348003)
  ·
    refine ⟨63544640262174882695022005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42363093508116588463348003 63544640262174882695022005)
    ·
      refine ⟨5957310024578895252658313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63544640262174882695022005 5957310024578895252658313)
      ·
        refine ⟨4467982518434171439493735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5957310024578895252658313 4467982518434171439493735)
        ·
          refine ⟨6701973777651257159240603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4467982518434171439493735 6701973777651257159240603)
          ·
            refine ⟨10052960666476885738860905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6701973777651257159240603 10052960666476885738860905)
            ·
              refine ⟨7539720499857664304145679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10052960666476885738860905 7539720499857664304145679)
              ·
                refine ⟨11309580749786496456218519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7539720499857664304145679 11309580749786496456218519)
                ·
                  refine ⟨16964371124679744684327779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11309580749786496456218519 16964371124679744684327779)
                  ·
                    refine ⟨25446556687019617026491669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16964371124679744684327779 25446556687019617026491669)
                    ·
                      refine ⟨1192807344704044548116797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25446556687019617026491669 1192807344704044548116797)
                      ·
                        rfl

theorem cell23_2322984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2322984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322984 prefixEnd_2322984 := by exact prefixLift 2322984
  have htrace : WordTrace (prefixWord ++ tailWord_2322984) baseStart_2322984 baseEnd_2322984 := by
    simpa [prefixWord, tailWord_2322984, baseEnd_2322984] using wordTrace_append hprefix tailTrace_2322984
  have hstable : (prefixWord ++ tailWord_2322984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322984).length < 2 ^ (prefixWord ++ tailWord_2322984).sum := by decide
  have hdescent : baseEnd_2322984 < baseStart_2322984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2322987 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 3]
def baseStart_2322987 : Nat := 118140960795 + 2322987 * 2 ^ 59
def prefixEnd_2322987 : Nat := 4983230072969 + 3 ^ 40 * 2322987 * 2
def baseEnd_2322987 : Nat := 1192808885146008036379283

theorem tailTrace_2322987 : CollatzResearch.WordTrace tailWord_2322987 prefixEnd_2322987 1192808885146008036379283 := by
  unfold tailWord_2322987
  simp only [CollatzResearch.WordTrace]
  refine ⟨84726296435222308439055215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56484197623481538959370143 84726296435222308439055215)
  ·
    refine ⟨127089444652833462658582823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84726296435222308439055215 127089444652833462658582823)
    ·
      refine ⟨190634166979250193987874235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127089444652833462658582823 190634166979250193987874235)
      ·
        refine ⟨285951250468875290981811353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190634166979250193987874235 285951250468875290981811353)
        ·
          refine ⟨214463437851656468236358515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285951250468875290981811353 214463437851656468236358515)
          ·
            refine ⟨321695156777484702354537773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214463437851656468236358515 321695156777484702354537773)
            ·
              refine ⟨120635683791556763382951665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321695156777484702354537773 120635683791556763382951665)
              ·
                refine ⟨90476762843667572537213749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120635683791556763382951665 90476762843667572537213749)
                ·
                  refine ⟨8482196516593834925363789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90476762843667572537213749 8482196516593834925363789)
                  ·
                    refine ⟨3180823693722688097011421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8482196516593834925363789 3180823693722688097011421)
                    ·
                      refine ⟨1192808885146008036379283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3180823693722688097011421 1192808885146008036379283)
                      ·
                        rfl

theorem cell23_2322987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 3].length) (baseStart_2322987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2322987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2322987 prefixEnd_2322987 := by exact prefixLift 2322987
  have htrace : WordTrace (prefixWord ++ tailWord_2322987) baseStart_2322987 baseEnd_2322987 := by
    simpa [prefixWord, tailWord_2322987, baseEnd_2322987] using wordTrace_append hprefix tailTrace_2322987
  have hstable : (prefixWord ++ tailWord_2322987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2322987).length < 2 ^ (prefixWord ++ tailWord_2322987).sum := by decide
  have hdescent : baseEnd_2322987 < baseStart_2322987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2322987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323004 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_2323004 : Nat := 118140960795 + 2323004 * 2 ^ 59
def prefixEnd_2323004 : Nat := 4983230072969 + 3 ^ 40 * 2323004 * 2
def baseEnd_2323004 : Nat := 1192817614317134469866705

theorem tailTrace_2323004 : CollatzResearch.WordTrace tailWord_2323004 prefixEnd_2323004 1192817614317134469866705 := by
  unfold tailWord_2323004
  simp only [CollatzResearch.WordTrace]
  refine ⟨42363458238080360171212033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56484610984107146894949377 42363458238080360171212033)
  ·
    refine ⟨31772593678560270128409025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42363458238080360171212033 31772593678560270128409025)
    ·
      refine ⟨23829445258920202596306769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31772593678560270128409025 23829445258920202596306769)
      ·
        refine ⟨17872083944190151947230077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23829445258920202596306769 17872083944190151947230077)
        ·
          refine ⟨6702031479071306980211279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17872083944190151947230077 6702031479071306980211279)
          ·
            refine ⟨10053047218606960470316919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702031479071306980211279 10053047218606960470316919)
            ·
              refine ⟨15079570827910440705475379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10053047218606960470316919 15079570827910440705475379)
              ·
                refine ⟨22619356241865661058213069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15079570827910440705475379 22619356241865661058213069)
                ·
                  refine ⟨8482258590699622896829901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22619356241865661058213069 8482258590699622896829901)
                  ·
                    refine ⟨3180846971512358586311213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8482258590699622896829901 3180846971512358586311213)
                    ·
                      refine ⟨1192817614317134469866705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3180846971512358586311213 1192817614317134469866705)
                      ·
                        rfl

theorem cell23_2323004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_2323004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323004 prefixEnd_2323004 := by exact prefixLift 2323004
  have htrace : WordTrace (prefixWord ++ tailWord_2323004) baseStart_2323004 baseEnd_2323004 := by
    simpa [prefixWord, tailWord_2323004, baseEnd_2323004] using wordTrace_append hprefix tailTrace_2323004
  have hstable : (prefixWord ++ tailWord_2323004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323004).length < 2 ^ (prefixWord ++ tailWord_2323004).sum := by decide
  have hdescent : baseEnd_2323004 < baseStart_2323004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323065 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 1, 3, 2]
def baseStart_2323065 : Nat := 118140960795 + 2323065 * 2 ^ 59
def prefixEnd_2323065 : Nat := 4983230072969 + 3 ^ 40 * 2323065 * 2
def baseEnd_2323065 : Nat := 1192848936637058731203925

theorem tailTrace_2323065 : CollatzResearch.WordTrace tailWord_2323065 prefixEnd_2323065 1192848936637058731203925 := by
  unfold tailWord_2323065
  simp only [CollatzResearch.WordTrace]
  refine ⟨84729141328939727760394649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56486094219293151840263099 84729141328939727760394649)
  ·
    refine ⟨63546855996704795820295987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84729141328939727760394649 63546855996704795820295987)
    ·
      refine ⟨95320283995057193730443981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63546855996704795820295987 95320283995057193730443981)
      ·
        refine ⟨35745106498146447648916493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95320283995057193730443981 35745106498146447648916493)
        ·
          refine ⟨13404414936804917868343685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35745106498146447648916493 13404414936804917868343685)
          ·
            refine ⟨2513327800650922100314441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13404414936804917868343685 2513327800650922100314441)
            ·
              refine ⟨1884995850488191575235831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2513327800650922100314441 1884995850488191575235831)
              ·
                refine ⟨2827493775732287362853747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884995850488191575235831 2827493775732287362853747)
                ·
                  refine ⟨4241240663598431044280621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827493775732287362853747 4241240663598431044280621)
                  ·
                    refine ⟨1590465248849411641605233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4241240663598431044280621 1590465248849411641605233)
                    ·
                      refine ⟨1192848936637058731203925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1590465248849411641605233 1192848936637058731203925)
                      ·
                        rfl

theorem cell23_2323065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_2323065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323065 prefixEnd_2323065 := by exact prefixLift 2323065
  have htrace : WordTrace (prefixWord ++ tailWord_2323065) baseStart_2323065 baseEnd_2323065 := by
    simpa [prefixWord, tailWord_2323065, baseEnd_2323065] using wordTrace_append hprefix tailTrace_2323065
  have hstable : (prefixWord ++ tailWord_2323065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323065).length < 2 ^ (prefixWord ++ tailWord_2323065).sum := by decide
  have hdescent : baseEnd_2323065 < baseStart_2323065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323095 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 2, 2, 2]
def baseStart_2323095 : Nat := 118140960795 + 2323095 * 2 ^ 59
def prefixEnd_2323095 : Nat := 4983230072969 + 3 ^ 40 * 2323095 * 2
def baseEnd_2323095 : Nat := 1192864341056693613828787

theorem tailTrace_2323095 : CollatzResearch.WordTrace tailWord_2323095 prefixEnd_2323095 1192864341056693613828787 := by
  unfold tailWord_2323095
  simp only [CollatzResearch.WordTrace]
  refine ⟨84730235518831042883986739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56486823679220695255991159 84730235518831042883986739)
  ·
    refine ⟨127095353278246564325980109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84730235518831042883986739 127095353278246564325980109)
    ·
      refine ⟨47660757479342461622242541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127095353278246564325980109 47660757479342461622242541)
      ·
        refine ⟨17872784054753423108340953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47660757479342461622242541 17872784054753423108340953)
        ·
          refine ⟨13404588041065067331255715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17872784054753423108340953 13404588041065067331255715)
          ·
            refine ⟨20106882061597600996883573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13404588041065067331255715 20106882061597600996883573)
            ·
              refine ⟨1885020193274775093457835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20106882061597600996883573 1885020193274775093457835)
              ·
                refine ⟨2827530289912162640186753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1885020193274775093457835 2827530289912162640186753)
                ·
                  refine ⟨2120647717434121980140065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827530289912162640186753 2120647717434121980140065)
                  ·
                    refine ⟨1590485788075591485105049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2120647717434121980140065 1590485788075591485105049)
                    ·
                      refine ⟨1192864341056693613828787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1590485788075591485105049 1192864341056693613828787)
                      ·
                        rfl

theorem cell23_2323095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_2323095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323095 prefixEnd_2323095 := by exact prefixLift 2323095
  have htrace : WordTrace (prefixWord ++ tailWord_2323095) baseStart_2323095 baseEnd_2323095 := by
    simpa [prefixWord, tailWord_2323095, baseEnd_2323095] using wordTrace_append hprefix tailTrace_2323095
  have hstable : (prefixWord ++ tailWord_2323095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323095).length < 2 ^ (prefixWord ++ tailWord_2323095).sum := by decide
  have hdescent : baseEnd_2323095 < baseStart_2323095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
