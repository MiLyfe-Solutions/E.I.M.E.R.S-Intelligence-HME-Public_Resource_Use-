import V185TrunkScan22Chunk245

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2195399 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2195399 : Nat := 118140960795 + 2195399 * 2 ^ 59
def prefixEnd_2195399 : Nat := 4983230072969 + 3 ^ 40 * 2195399 * 2
def baseEnd_2195399 : Nat := 751529943600107483344033

theorem tailTrace_2195399 : CollatzResearch.WordTrace tailWord_2195399 prefixEnd_2195399 751529943600107483344033 := by
  unfold tailWord_2195399
  simp only [CollatzResearch.WordTrace]
  refine ⟨80072779773451842143469251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53381853182301228095646167 80072779773451842143469251)
  ·
    refine ⟨120109169660177763215203877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80072779773451842143469251 120109169660177763215203877)
    ·
      refine ⟨22520469311283330602850727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120109169660177763215203877 22520469311283330602850727)
      ·
        refine ⟨33780703966924995904276091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22520469311283330602850727 33780703966924995904276091)
        ·
          refine ⟨50671055950387493856414137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33780703966924995904276091 50671055950387493856414137)
          ·
            refine ⟨38003291962790620392310603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50671055950387493856414137 38003291962790620392310603)
            ·
              refine ⟨57004937944185930588465905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38003291962790620392310603 57004937944185930588465905)
              ·
                refine ⟨42753703458139447941349429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57004937944185930588465905 42753703458139447941349429)
                ·
                  refine ⟨4008159699200573244501509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42753703458139447941349429 4008159699200573244501509)
                  ·
                    refine ⟨751529943600107483344033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4008159699200573244501509 751529943600107483344033)
                    ·
                      rfl

theorem cell22_2195399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2195399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195399 prefixEnd_2195399 := by exact prefixLift 2195399
  have htrace : WordTrace (prefixWord ++ tailWord_2195399) baseStart_2195399 baseEnd_2195399 := by
    simpa [prefixWord, tailWord_2195399, baseEnd_2195399] using wordTrace_append hprefix tailTrace_2195399
  have hstable : (prefixWord ++ tailWord_2195399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195399).length < 2 ^ (prefixWord ++ tailWord_2195399).sum := by decide
  have hdescent : baseEnd_2195399 < baseStart_2195399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195461 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_2195461 : Nat := 118140960795 + 2195461 * 2 ^ 59
def prefixEnd_2195461 : Nat := 4983230072969 + 3 ^ 40 * 2195461 * 2
def baseEnd_2195461 : Nat := 751551167467159988293843

theorem tailTrace_2195461 : CollatzResearch.WordTrace tailWord_2195461 prefixEnd_2195461 751551167467159988293843 := by
  unfold tailWord_2195461
  simp only [CollatzResearch.WordTrace]
  refine ⟨80075041099227226732226237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53383360732818151154817491 80075041099227226732226237)
  ·
    refine ⟨30028140412210210024584839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80075041099227226732226237 30028140412210210024584839)
    ·
      refine ⟨45042210618315315036877259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30028140412210210024584839 45042210618315315036877259)
      ·
        refine ⟨67563315927472972555315889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45042210618315315036877259 67563315927472972555315889)
        ·
          refine ⟨50672486945604729416486917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67563315927472972555315889 50672486945604729416486917)
          ·
            refine ⟨9501091302300886765591297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50672486945604729416486917 9501091302300886765591297)
            ·
              refine ⟨7125818476725665074193473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9501091302300886765591297 7125818476725665074193473)
              ·
                refine ⟨5344363857544248805645105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7125818476725665074193473 5344363857544248805645105)
                ·
                  refine ⟨4008272893158186604233829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5344363857544248805645105 4008272893158186604233829)
                  ·
                    refine ⟨751551167467159988293843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4008272893158186604233829 751551167467159988293843)
                    ·
                      rfl

theorem cell22_2195461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_2195461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195461 prefixEnd_2195461 := by exact prefixLift 2195461
  have htrace : WordTrace (prefixWord ++ tailWord_2195461) baseStart_2195461 baseEnd_2195461 := by
    simpa [prefixWord, tailWord_2195461, baseEnd_2195461] using wordTrace_append hprefix tailTrace_2195461
  have hstable : (prefixWord ++ tailWord_2195461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195461).length < 2 ^ (prefixWord ++ tailWord_2195461).sum := by decide
  have hdescent : baseEnd_2195461 < baseStart_2195461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195463 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 2, 3]
def baseStart_2195463 : Nat := 118140960795 + 2195463 * 2 ^ 59
def prefixEnd_2195463 : Nat := 4983230072969 + 3 ^ 40 * 2195463 * 2
def baseEnd_2195463 : Nat := 751551852108032649743837

theorem tailTrace_2195463 : CollatzResearch.WordTrace tailWord_2195463 prefixEnd_2195463 751551852108032649743837 := by
  unfold tailWord_2195463
  simp only [CollatzResearch.WordTrace]
  refine ⟨80075114045219981073799043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53383409363479987382532695 80075114045219981073799043)
  ·
    refine ⟨120112671067829971610698565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80075114045219981073799043 120112671067829971610698565)
    ·
      refine ⟨22521125825218119677005981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120112671067829971610698565 22521125825218119677005981)
      ·
        refine ⟨8445422184456794878877243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22521125825218119677005981 8445422184456794878877243)
        ·
          refine ⟨12668133276685192318315865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8445422184456794878877243 12668133276685192318315865)
          ·
            refine ⟨9501099957513894238736899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12668133276685192318315865 9501099957513894238736899)
            ·
              refine ⟨14251649936270841358105349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9501099957513894238736899 14251649936270841358105349)
              ·
                refine ⟨2672184363050782754644753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14251649936270841358105349 2672184363050782754644753)
                ·
                  refine ⟨2004138272288087065983565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2672184363050782754644753 2004138272288087065983565)
                  ·
                    refine ⟨751551852108032649743837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004138272288087065983565 751551852108032649743837)
                    ·
                      rfl

theorem cell22_2195463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_2195463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195463 prefixEnd_2195463 := by exact prefixLift 2195463
  have htrace : WordTrace (prefixWord ++ tailWord_2195463) baseStart_2195463 baseEnd_2195463 := by
    simpa [prefixWord, tailWord_2195463, baseEnd_2195463] using wordTrace_append hprefix tailTrace_2195463
  have hstable : (prefixWord ++ tailWord_2195463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195463).length < 2 ^ (prefixWord ++ tailWord_2195463).sum := by decide
  have hdescent : baseEnd_2195463 < baseStart_2195463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195542 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2195542 : Nat := 118140960795 + 2195542 * 2 ^ 59
def prefixEnd_2195542 : Nat := 4983230072969 + 3 ^ 40 * 2195542 * 2
def baseEnd_2195542 : Nat := 751578895422502777018595

theorem tailTrace_2195542 : CollatzResearch.WordTrace tailWord_2195542 prefixEnd_2195542 751578895422502777018595 := by
  unfold tailWord_2195542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004874713245861097870305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53385330274622518377283253 5004874713245861097870305)
  ·
    refine ⟨3753656034934395823402729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5004874713245861097870305 3753656034934395823402729)
    ·
      refine ⟨2815242026200796867552047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3753656034934395823402729 2815242026200796867552047)
      ·
        refine ⟨4222863039301195301328071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2815242026200796867552047 4222863039301195301328071)
        ·
          refine ⟨6334294558951792951992107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4222863039301195301328071 6334294558951792951992107)
          ·
            refine ⟨9501441838427689427988161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334294558951792951992107 9501441838427689427988161)
            ·
              refine ⟨7126081378820767070991121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9501441838427689427988161 7126081378820767070991121)
              ·
                refine ⟨5344561034115575303243341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7126081378820767070991121 5344561034115575303243341)
                ·
                  refine ⟨2004210387793340738716253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5344561034115575303243341 2004210387793340738716253)
                  ·
                    refine ⟨751578895422502777018595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004210387793340738716253 751578895422502777018595)
                    ·
                      rfl

theorem cell22_2195542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2195542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195542 prefixEnd_2195542 := by exact prefixLift 2195542
  have htrace : WordTrace (prefixWord ++ tailWord_2195542) baseStart_2195542 baseEnd_2195542 := by
    simpa [prefixWord, tailWord_2195542, baseEnd_2195542] using wordTrace_append hprefix tailTrace_2195542
  have hstable : (prefixWord ++ tailWord_2195542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195542).length < 2 ^ (prefixWord ++ tailWord_2195542).sum := by decide
  have hdescent : baseEnd_2195542 < baseStart_2195542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195568 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_2195568 : Nat := 118140960795 + 2195568 * 2 ^ 59
def prefixEnd_2195568 : Nat := 4983230072969 + 3 ^ 40 * 2195568 * 2
def baseEnd_2195568 : Nat := 751587795753847375868515

theorem tailTrace_2195568 : CollatzResearch.WordTrace tailWord_2195568 prefixEnd_2195568 751587795753847375868515 := by
  unfold tailWord_2195568
  simp only [CollatzResearch.WordTrace]
  refine ⟨40039471854919792003185679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53385962473226389337580905 40039471854919792003185679)
  ·
    refine ⟨60059207782379688004778519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40039471854919792003185679 60059207782379688004778519)
    ·
      refine ⟨90088811673569532007167779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60059207782379688004778519 90088811673569532007167779)
      ·
        refine ⟨135133217510354298010751669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90088811673569532007167779 135133217510354298010751669)
        ·
          refine ⟨12668739141595715438507969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135133217510354298010751669 12668739141595715438507969)
          ·
            refine ⟨9501554356196786578880977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12668739141595715438507969 9501554356196786578880977)
            ·
              refine ⟨7126165767147589934160733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9501554356196786578880977 7126165767147589934160733)
              ·
                refine ⟨2672312162680346225310275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7126165767147589934160733 2672312162680346225310275)
                ·
                  refine ⟨4008468244020519337965413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672312162680346225310275 4008468244020519337965413)
                  ·
                    refine ⟨751587795753847375868515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4008468244020519337965413 751587795753847375868515)
                    ·
                      rfl

theorem cell22_2195568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_2195568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195568 prefixEnd_2195568 := by exact prefixLift 2195568
  have htrace : WordTrace (prefixWord ++ tailWord_2195568) baseStart_2195568 baseEnd_2195568 := by
    simpa [prefixWord, tailWord_2195568, baseEnd_2195568] using wordTrace_append hprefix tailTrace_2195568
  have hstable : (prefixWord ++ tailWord_2195568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195568).length < 2 ^ (prefixWord ++ tailWord_2195568).sum := by decide
  have hdescent : baseEnd_2195568 < baseStart_2195568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195613 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2195613 : Nat := 118140960795 + 2195613 * 2 ^ 59
def prefixEnd_2195613 : Nat := 4983230072969 + 3 ^ 40 * 2195613 * 2
def baseEnd_2195613 : Nat := 751603200173482258493377

theorem tailTrace_2195613 : CollatzResearch.WordTrace tailWord_2195613 prefixEnd_2195613 751603200173482258493377 := by
  unfold tailWord_2195613
  simp only [CollatzResearch.WordTrace]
  refine ⟨80080584994676556691759493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53387056663117704461172995 80080584994676556691759493)
  ·
    refine ⟨15015109686501854379704905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80080584994676556691759493 15015109686501854379704905)
    ·
      refine ⟨11261332264876390784778679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15015109686501854379704905 11261332264876390784778679)
      ·
        refine ⟨16891998397314586177168019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11261332264876390784778679 16891998397314586177168019)
        ·
          refine ⟨25337997595971879265752029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16891998397314586177168019 25337997595971879265752029)
          ·
            refine ⟨9501749098489454724657011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25337997595971879265752029 9501749098489454724657011)
            ·
              refine ⟨14252623647734182086985517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9501749098489454724657011 14252623647734182086985517)
              ·
                refine ⟨5344733867900318282619569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14252623647734182086985517 5344733867900318282619569)
                ·
                  refine ⟨4008550400925238711964677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5344733867900318282619569 4008550400925238711964677)
                  ·
                    refine ⟨751603200173482258493377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4008550400925238711964677 751603200173482258493377)
                    ·
                      rfl

theorem cell22_2195613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2195613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195613 prefixEnd_2195613 := by exact prefixLift 2195613
  have htrace : WordTrace (prefixWord ++ tailWord_2195613) baseStart_2195613 baseEnd_2195613 := by
    simpa [prefixWord, tailWord_2195613, baseEnd_2195613] using wordTrace_append hprefix tailTrace_2195613
  have hstable : (prefixWord ++ tailWord_2195613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195613).length < 2 ^ (prefixWord ++ tailWord_2195613).sum := by decide
  have hdescent : baseEnd_2195613 < baseStart_2195613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195641 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_2195641 : Nat := 118140960795 + 2195641 * 2 ^ 59
def prefixEnd_2195641 : Nat := 4983230072969 + 3 ^ 40 * 2195641 * 2
def baseEnd_2195641 : Nat := 751612785145699518793291

theorem tailTrace_2195641 : CollatzResearch.WordTrace tailWord_2195641 prefixEnd_2195641 751612785145699518793291 := by
  unfold tailWord_2195641
  simp only [CollatzResearch.WordTrace]
  refine ⟨80081606238575117473778777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53387737492383411649185851 80081606238575117473778777)
  ·
    refine ⟨60061204678931338105334083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80081606238575117473778777 60061204678931338105334083)
    ·
      refine ⟨90091807018397007158001125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60061204678931338105334083 90091807018397007158001125)
      ·
        refine ⟨16892213815949438842125211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90091807018397007158001125 16892213815949438842125211)
        ·
          refine ⟨25338320723924158263187817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16892213815949438842125211 25338320723924158263187817)
          ·
            refine ⟨19003740542943118697390863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25338320723924158263187817 19003740542943118697390863)
            ·
              refine ⟨28505610814414678046086295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19003740542943118697390863 28505610814414678046086295)
              ·
                refine ⟨42758416221622017069129443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28505610814414678046086295 42758416221622017069129443)
                ·
                  refine ⟨64137624332433025603694165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42758416221622017069129443 64137624332433025603694165)
                  ·
                    refine ⟨751612785145699518793291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64137624332433025603694165 751612785145699518793291)
                    ·
                      rfl

theorem cell22_2195641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_2195641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195641 prefixEnd_2195641 := by exact prefixLift 2195641
  have htrace : WordTrace (prefixWord ++ tailWord_2195641) baseStart_2195641 baseEnd_2195641 := by
    simpa [prefixWord, tailWord_2195641, baseEnd_2195641] using wordTrace_append hprefix tailTrace_2195641
  have hstable : (prefixWord ++ tailWord_2195641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195641).length < 2 ^ (prefixWord ++ tailWord_2195641).sum := by decide
  have hdescent : baseEnd_2195641 < baseStart_2195641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195643 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 3, 3]
def baseStart_2195643 : Nat := 118140960795 + 2195643 * 2 ^ 59
def prefixEnd_2195643 : Nat := 4983230072969 + 3 ^ 40 * 2195643 * 2
def baseEnd_2195643 : Nat := 751613469786572180243285

theorem tailTrace_2195643 : CollatzResearch.WordTrace tailWord_2195643 prefixEnd_2195643 751613469786572180243285 := by
  unfold tailWord_2195643
  simp only [CollatzResearch.WordTrace]
  refine ⟨80081679184567871815351583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53387786123045247876901055 80081679184567871815351583)
  ·
    refine ⟨120122518776851807723027375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80081679184567871815351583 120122518776851807723027375)
    ·
      refine ⟨180183778165277711584541063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120122518776851807723027375 180183778165277711584541063)
      ·
        refine ⟨270275667247916567376811595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180183778165277711584541063 270275667247916567376811595)
        ·
          refine ⟨405413500871874851065217393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270275667247916567376811595 405413500871874851065217393)
          ·
            refine ⟨304060125653906138298913045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405413500871874851065217393 304060125653906138298913045)
            ·
              refine ⟨14252818390026850232761549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 304060125653906138298913045 14252818390026850232761549)
              ·
                refine ⟨5344806896260068837285581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14252818390026850232761549 5344806896260068837285581)
                ·
                  refine ⟨2004302586097525813982093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5344806896260068837285581 2004302586097525813982093)
                  ·
                    refine ⟨751613469786572180243285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004302586097525813982093 751613469786572180243285)
                    ·
                      rfl

theorem cell22_2195643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 3].length) (baseStart_2195643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195643 prefixEnd_2195643 := by exact prefixLift 2195643
  have htrace : WordTrace (prefixWord ++ tailWord_2195643) baseStart_2195643 baseEnd_2195643 := by
    simpa [prefixWord, tailWord_2195643, baseEnd_2195643] using wordTrace_append hprefix tailTrace_2195643
  have hstable : (prefixWord ++ tailWord_2195643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195643).length < 2 ^ (prefixWord ++ tailWord_2195643).sum := by decide
  have hdescent : baseEnd_2195643 < baseStart_2195643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195656 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 9]
def baseStart_2195656 : Nat := 118140960795 + 2195656 * 2 ^ 59
def prefixEnd_2195656 : Nat := 4983230072969 + 3 ^ 40 * 2195656 * 2
def baseEnd_2195656 : Nat := 250539306650748159889415

theorem tailTrace_2195656 : CollatzResearch.WordTrace tailWord_2195656 prefixEnd_2195656 250539306650748159889415 := by
  unfold tailWord_2195656
  simp only [CollatzResearch.WordTrace]
  refine ⟨40041076666760387517787411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53388102222347183357049881 40041076666760387517787411)
  ·
    refine ⟨60061615000140581276681117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40041076666760387517787411 60061615000140581276681117)
    ·
      refine ⟨22523105625052717978755419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60061615000140581276681117 22523105625052717978755419)
      ·
        refine ⟨33784658437579076968133129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22523105625052717978755419 33784658437579076968133129)
        ·
          refine ⟨25338493828184307726099847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33784658437579076968133129 25338493828184307726099847)
          ·
            refine ⟨38007740742276461589149771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25338493828184307726099847 38007740742276461589149771)
            ·
              refine ⟨57011611113414692383724657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38007740742276461589149771 57011611113414692383724657)
              ·
                refine ⟨42758708335061019287793493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57011611113414692383724657 42758708335061019287793493)
                ·
                  refine ⟨250539306650748159889415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42758708335061019287793493 250539306650748159889415)
                  ·
                    rfl

theorem cell22_2195656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_2195656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195656 prefixEnd_2195656 := by exact prefixLift 2195656
  have htrace : WordTrace (prefixWord ++ tailWord_2195656) baseStart_2195656 baseEnd_2195656 := by
    simpa [prefixWord, tailWord_2195656, baseEnd_2195656] using wordTrace_append hprefix tailTrace_2195656
  have hstable : (prefixWord ++ tailWord_2195656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195656).length < 2 ^ (prefixWord ++ tailWord_2195656).sum := by decide
  have hdescent : baseEnd_2195656 < baseStart_2195656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195671 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 3, 7]
def baseStart_2195671 : Nat := 118140960795 + 2195671 * 2 ^ 59
def prefixEnd_2195671 : Nat := 4983230072969 + 3 ^ 40 * 2195671 * 2
def baseEnd_2195671 : Nat := 751623054758789440543199

theorem tailTrace_2195671 : CollatzResearch.WordTrace tailWord_2195671 prefixEnd_2195671 751623054758789440543199 := by
  unfold tailWord_2195671
  simp only [CollatzResearch.WordTrace]
  refine ⟨80082700428466432597370867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53388466952310955064913911 80082700428466432597370867)
  ·
    refine ⟨120124050642699648896056301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80082700428466432597370867 120124050642699648896056301)
    ·
      refine ⟨45046518991012368336021113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120124050642699648896056301 45046518991012368336021113)
      ·
        refine ⟨33784889243259276252015835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45046518991012368336021113 33784889243259276252015835)
        ·
          refine ⟨50677333864888914378023753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33784889243259276252015835 50677333864888914378023753)
          ·
            refine ⟨38008000398666685783517815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50677333864888914378023753 38008000398666685783517815)
            ·
              refine ⟨57012000598000028675276723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38008000398666685783517815 57012000598000028675276723)
              ·
                refine ⟨85518000897000043012915085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57012000598000028675276723 85518000897000043012915085)
                ·
                  refine ⟨32069250336375016129843157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85518000897000043012915085 32069250336375016129843157)
                  ·
                    refine ⟨751623054758789440543199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32069250336375016129843157 751623054758789440543199)
                    ·
                      rfl

theorem cell22_2195671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_2195671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195671 prefixEnd_2195671 := by exact prefixLift 2195671
  have htrace : WordTrace (prefixWord ++ tailWord_2195671) baseStart_2195671 baseEnd_2195671 := by
    simpa [prefixWord, tailWord_2195671, baseEnd_2195671] using wordTrace_append hprefix tailTrace_2195671
  have hstable : (prefixWord ++ tailWord_2195671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195671).length < 2 ^ (prefixWord ++ tailWord_2195671).sum := by decide
  have hdescent : baseEnd_2195671 < baseStart_2195671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195688 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2195688 : Nat := 118140960795 + 2195688 * 2 ^ 59
def prefixEnd_2195688 : Nat := 4983230072969 + 3 ^ 40 * 2195688 * 2
def baseEnd_2195688 : Nat := 751628874206207062868147

theorem tailTrace_2195688 : CollatzResearch.WordTrace tailWord_2195688 prefixEnd_2195688 751628874206207062868147 := by
  unfold tailWord_2195688
  simp only [CollatzResearch.WordTrace]
  refine ⟨40041660234702422250369859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53388880312936563000493145 40041660234702422250369859)
  ·
    refine ⟨60062490352053633375554789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40041660234702422250369859 60062490352053633375554789)
    ·
      refine ⟨11261716941010056257916523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60062490352053633375554789 11261716941010056257916523)
      ·
        refine ⟨16892575411515084386874785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11261716941010056257916523 16892575411515084386874785)
        ·
          refine ⟨12669431558636313290156089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16892575411515084386874785 12669431558636313290156089)
          ·
            refine ⟨9502073668977234967617067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12669431558636313290156089 9502073668977234967617067)
            ·
              refine ⟨14253110503465852451425601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9502073668977234967617067 14253110503465852451425601)
              ·
                refine ⟨10689832877599389338569201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14253110503465852451425601 10689832877599389338569201)
                ·
                  refine ⟨8017374658199542003926901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10689832877599389338569201 8017374658199542003926901)
                  ·
                    refine ⟨751628874206207062868147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8017374658199542003926901 751628874206207062868147)
                    ·
                      rfl

theorem cell22_2195688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2195688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195688 prefixEnd_2195688 := by exact prefixLift 2195688
  have htrace : WordTrace (prefixWord ++ tailWord_2195688) baseStart_2195688 baseEnd_2195688 := by
    simpa [prefixWord, tailWord_2195688, baseEnd_2195688] using wordTrace_append hprefix tailTrace_2195688
  have hstable : (prefixWord ++ tailWord_2195688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195688).length < 2 ^ (prefixWord ++ tailWord_2195688).sum := by decide
  have hdescent : baseEnd_2195688 < baseStart_2195688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195720 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_2195720 : Nat := 118140960795 + 2195720 * 2 ^ 59
def prefixEnd_2195720 : Nat := 4983230072969 + 3 ^ 40 * 2195720 * 2
def baseEnd_2195720 : Nat := 751639828460169646068049

theorem tailTrace_2195720 : CollatzResearch.WordTrace tailWord_2195720 prefixEnd_2195720 751639828460169646068049 := by
  unfold tailWord_2195720
  simp only [CollatzResearch.WordTrace]
  refine ⟨40042243802644456982952307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53389658403525942643936409 40042243802644456982952307)
  ·
    refine ⟨60063365703966685474428461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40042243802644456982952307 60063365703966685474428461)
    ·
      refine ⟨22523762138987507052910673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60063365703966685474428461 22523762138987507052910673)
      ·
        refine ⟨16892821604240630289683005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22523762138987507052910673 16892821604240630289683005)
        ·
          refine ⟨6334808101590236358631127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16892821604240630289683005 6334808101590236358631127)
          ·
            refine ⟨9502212152385354537946691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334808101590236358631127 9502212152385354537946691)
            ·
              refine ⟨14253318228578031806920037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9502212152385354537946691 14253318228578031806920037)
              ·
                refine ⟨2672497167858380963797507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14253318228578031806920037 2672497167858380963797507)
                ·
                  refine ⟨4008745751787571445696261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672497167858380963797507 4008745751787571445696261)
                  ·
                    refine ⟨751639828460169646068049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4008745751787571445696261 751639828460169646068049)
                    ·
                      rfl

theorem cell22_2195720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_2195720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195720 prefixEnd_2195720 := by exact prefixLift 2195720
  have htrace : WordTrace (prefixWord ++ tailWord_2195720) baseStart_2195720 baseEnd_2195720 := by
    simpa [prefixWord, tailWord_2195720, baseEnd_2195720] using wordTrace_append hprefix tailTrace_2195720
  have hstable : (prefixWord ++ tailWord_2195720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195720).length < 2 ^ (prefixWord ++ tailWord_2195720).sum := by decide
  have hdescent : baseEnd_2195720 < baseStart_2195720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195733 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_2195733 : Nat := 118140960795 + 2195733 * 2 ^ 59
def prefixEnd_2195733 : Nat := 4983230072969 + 3 ^ 40 * 2195733 * 2
def baseEnd_2195733 : Nat := 751644278625841945493009

theorem tailTrace_2195733 : CollatzResearch.WordTrace tailWord_2195733 prefixEnd_2195733 751644278625841945493009 := by
  unfold tailWord_2195733
  simp only [CollatzResearch.WordTrace]
  refine ⟨80084961754241817186127853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53389974502827878124085235 80084961754241817186127853)
  ·
    refine ⟨30031860657840681444797945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80084961754241817186127853 30031860657840681444797945)
    ·
      refine ⟨22523895493380511083598459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30031860657840681444797945 22523895493380511083598459)
      ·
        refine ⟨33785843240070766625397689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22523895493380511083598459 33785843240070766625397689)
        ·
          refine ⟨25339382430053074969048267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33785843240070766625397689 25339382430053074969048267)
          ·
            refine ⟨38009073645079612453572401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25339382430053074969048267 38009073645079612453572401)
            ·
              refine ⟨28506805233809709340179301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38009073645079612453572401 28506805233809709340179301)
              ·
                refine ⟨5345025981339320501283619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28506805233809709340179301 5345025981339320501283619)
                ·
                  refine ⟨8017538972008980751925429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5345025981339320501283619 8017538972008980751925429)
                  ·
                    refine ⟨751644278625841945493009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8017538972008980751925429 751644278625841945493009)
                    ·
                      rfl

theorem cell22_2195733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_2195733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195733 prefixEnd_2195733 := by exact prefixLift 2195733
  have htrace : WordTrace (prefixWord ++ tailWord_2195733) baseStart_2195733 baseEnd_2195733 := by
    simpa [prefixWord, tailWord_2195733, baseEnd_2195733] using wordTrace_append hprefix tailTrace_2195733
  have hstable : (prefixWord ++ tailWord_2195733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195733).length < 2 ^ (prefixWord ++ tailWord_2195733).sum := by decide
  have hdescent : baseEnd_2195733 < baseStart_2195733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195752 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 6]
def baseStart_2195752 : Nat := 118140960795 + 2195752 * 2 ^ 59
def prefixEnd_2195752 : Nat := 4983230072969 + 3 ^ 40 * 2195752 * 2
def baseEnd_2195752 : Nat := 250550260904710743089317

theorem tailTrace_2195752 : CollatzResearch.WordTrace tailWord_2195752 prefixEnd_2195752 250550260904710743089317 := by
  unfold tailWord_2195752
  simp only [CollatzResearch.WordTrace]
  refine ⟨40042827370586491715534755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53390436494115322287379673 40042827370586491715534755)
  ·
    refine ⟨60064241055879737573302133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40042827370586491715534755 60064241055879737573302133)
    ·
      refine ⟨5631022598988725397497075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60064241055879737573302133 5631022598988725397497075)
      ·
        refine ⟨8446533898483088096245613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5631022598988725397497075 8446533898483088096245613)
        ·
          refine ⟨3167450211931158036092105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8446533898483088096245613 3167450211931158036092105)
          ·
            refine ⟨2375587658948368527069079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3167450211931158036092105 2375587658948368527069079)
            ·
              refine ⟨3563381488422552790603619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2375587658948368527069079 3563381488422552790603619)
              ·
                refine ⟨5345072232633829185905429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563381488422552790603619 5345072232633829185905429)
                ·
                  refine ⟨250550260904710743089317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5345072232633829185905429 250550260904710743089317)
                  ·
                    rfl

theorem cell22_2195752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_2195752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195752 prefixEnd_2195752 := by exact prefixLift 2195752
  have htrace : WordTrace (prefixWord ++ tailWord_2195752) baseStart_2195752 baseEnd_2195752 := by
    simpa [prefixWord, tailWord_2195752, baseEnd_2195752] using wordTrace_append hprefix tailTrace_2195752
  have hstable : (prefixWord ++ tailWord_2195752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195752).length < 2 ^ (prefixWord ++ tailWord_2195752).sum := by decide
  have hdescent : baseEnd_2195752 < baseStart_2195752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195763 : List Nat := [1, 1, 1, 2, 5, 1, 4, 7]
def baseStart_2195763 : Nat := 118140960795 + 2195763 * 2 ^ 59
def prefixEnd_2195763 : Nat := 4983230072969 + 3 ^ 40 * 2195763 * 2
def baseEnd_2195763 : Nat := 83517172026547985249213

theorem tailTrace_2195763 : CollatzResearch.WordTrace tailWord_2195763 prefixEnd_2195763 83517172026547985249213 := by
  unfold tailWord_2195763
  simp only [CollatzResearch.WordTrace]
  refine ⟨80086055944133132309719943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53390703962755421539813295 80086055944133132309719943)
  ·
    refine ⟨120129083916199698464579915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80086055944133132309719943 120129083916199698464579915)
    ·
      refine ⟨180193625874299547696869873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120129083916199698464579915 180193625874299547696869873)
      ·
        refine ⟨135145219405724660772652405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180193625874299547696869873 135145219405724660772652405)
        ·
          refine ⟨12669864319286686947436163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135145219405724660772652405 12669864319286686947436163)
          ·
            refine ⟨19004796478930030421154245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12669864319286686947436163 19004796478930030421154245)
            ·
              refine ⟨3563399339799380703966421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19004796478930030421154245 3563399339799380703966421)
              ·
                refine ⟨83517172026547985249213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3563399339799380703966421 83517172026547985249213)
                ·
                  rfl

theorem cell22_2195763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 7].length) (baseStart_2195763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195763 prefixEnd_2195763 := by exact prefixLift 2195763
  have htrace : WordTrace (prefixWord ++ tailWord_2195763) baseStart_2195763 baseEnd_2195763 := by
    simpa [prefixWord, tailWord_2195763, baseEnd_2195763] using wordTrace_append hprefix tailTrace_2195763
  have hstable : (prefixWord ++ tailWord_2195763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195763).length < 2 ^ (prefixWord ++ tailWord_2195763).sum := by decide
  have hdescent : baseEnd_2195763 < baseStart_2195763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195810 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2195810 : Nat := 118140960795 + 2195810 * 2 ^ 59
def prefixEnd_2195810 : Nat := 4983230072969 + 3 ^ 40 * 2195810 * 2
def baseEnd_2195810 : Nat := 751670637299439411317773

theorem tailTrace_2195810 : CollatzResearch.WordTrace tailWord_2195810 prefixEnd_2195810 751670637299439411317773 := by
  unfold tailWord_2195810
  simp only [CollatzResearch.WordTrace]
  refine ⟨20021942543740714834170221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53391846783308572891120589 20021942543740714834170221)
  ·
    refine ⟨7508228453902768062813833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20021942543740714834170221 7508228453902768062813833)
    ·
      refine ⟨5631171340427076047110375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7508228453902768062813833 5631171340427076047110375)
      ·
        refine ⟨8446757010640614070665563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5631171340427076047110375 8446757010640614070665563)
        ·
          refine ⟨12670135515960921105998345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8446757010640614070665563 12670135515960921105998345)
          ·
            refine ⟨9502601636970690829498759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12670135515960921105998345 9502601636970690829498759)
            ·
              refine ⟨14253902455456036244248139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9502601636970690829498759 14253902455456036244248139)
              ·
                refine ⟨21380853683184054366372209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14253902455456036244248139 21380853683184054366372209)
                ·
                  refine ⟨16035640262388040774779157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21380853683184054366372209 16035640262388040774779157)
                  ·
                    refine ⟨751670637299439411317773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16035640262388040774779157 751670637299439411317773)
                    ·
                      rfl

theorem cell22_2195810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2195810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195810 prefixEnd_2195810 := by exact prefixLift 2195810
  have htrace : WordTrace (prefixWord ++ tailWord_2195810) baseStart_2195810 baseEnd_2195810 := by
    simpa [prefixWord, tailWord_2195810, baseEnd_2195810] using wordTrace_append hprefix tailTrace_2195810
  have hstable : (prefixWord ++ tailWord_2195810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195810).length < 2 ^ (prefixWord ++ tailWord_2195810).sum := by decide
  have hdescent : baseEnd_2195810 < baseStart_2195810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195902 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_2195902 : Nat := 118140960795 + 2195902 * 2 ^ 59
def prefixEnd_2195902 : Nat := 4983230072969 + 3 ^ 40 * 2195902 * 2
def baseEnd_2195902 : Nat := 751702130779581838017491

theorem tailTrace_2195902 : CollatzResearch.WordTrace tailWord_2195902 prefixEnd_2195902 751702130779581838017491 := by
  unfold tailWord_2195902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10011390711328694881128745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53394083793753039366019973 10011390711328694881128745)
  ·
    refine ⟨7508543033496521160846559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10011390711328694881128745 7508543033496521160846559)
    ·
      refine ⟨11262814550244781741269839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7508543033496521160846559 11262814550244781741269839)
      ·
        refine ⟨16894221825367172611904759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11262814550244781741269839 16894221825367172611904759)
        ·
          refine ⟨25341332738050758917857139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16894221825367172611904759 25341332738050758917857139)
          ·
            refine ⟨38011999107076138376785709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25341332738050758917857139 38011999107076138376785709)
            ·
              refine ⟨14254499665153551891294641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38011999107076138376785709 14254499665153551891294641)
              ·
                refine ⟨10690874748865163918470981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14254499665153551891294641 10690874748865163918470981)
                ·
                  refine ⟨2004539015412218234713309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10690874748865163918470981 2004539015412218234713309)
                  ·
                    refine ⟨751702130779581838017491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004539015412218234713309 751702130779581838017491)
                    ·
                      rfl

theorem cell22_2195902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_2195902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195902 prefixEnd_2195902 := by exact prefixLift 2195902
  have htrace : WordTrace (prefixWord ++ tailWord_2195902) baseStart_2195902 baseEnd_2195902 := by
    simpa [prefixWord, tailWord_2195902, baseEnd_2195902] using wordTrace_append hprefix tailTrace_2195902
  have hstable : (prefixWord ++ tailWord_2195902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195902).length < 2 ^ (prefixWord ++ tailWord_2195902).sum := by decide
  have hdescent : baseEnd_2195902 < baseStart_2195902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195964 : List Nat := [2, 2, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_2195964 : Nat := 118140960795 + 2195964 * 2 ^ 59
def prefixEnd_2195964 : Nat := 4983230072969 + 3 ^ 40 * 2195964 * 2
def baseEnd_2195964 : Nat := 751723354646634342967301

theorem tailTrace_2195964 : CollatzResearch.WordTrace tailWord_2195964 prefixEnd_2195964 751723354646634342967301 := by
  unfold tailWord_2195964
  simp only [CollatzResearch.WordTrace]
  refine ⟨40046693508202471818893473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53395591344269962425191297 40046693508202471818893473)
  ·
    refine ⟨30035020131151853864170105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40046693508202471818893473 30035020131151853864170105)
    ·
      refine ⟨22526265098363890398127579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30035020131151853864170105 22526265098363890398127579)
      ·
        refine ⟨33789397647545835597191369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22526265098363890398127579 33789397647545835597191369)
        ·
          refine ⟨25342048235659376697893527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33789397647545835597191369 25342048235659376697893527)
          ·
            refine ⟨38013072353489065046840291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25342048235659376697893527 38013072353489065046840291)
            ·
              refine ⟨57019608530233597570260437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38013072353489065046840291 57019608530233597570260437)
              ·
                refine ⟨1336397074927349943052979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57019608530233597570260437 1336397074927349943052979)
                ·
                  refine ⟨2004595612391024914579469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336397074927349943052979 2004595612391024914579469)
                  ·
                    refine ⟨751723354646634342967301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004595612391024914579469 751723354646634342967301)
                    ·
                      rfl

theorem cell22_2195964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_2195964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195964 prefixEnd_2195964 := by exact prefixLift 2195964
  have htrace : WordTrace (prefixWord ++ tailWord_2195964) baseStart_2195964 baseEnd_2195964 := by
    simpa [prefixWord, tailWord_2195964, baseEnd_2195964] using wordTrace_append hprefix tailTrace_2195964
  have hstable : (prefixWord ++ tailWord_2195964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195964).length < 2 ^ (prefixWord ++ tailWord_2195964).sum := by decide
  have hdescent : baseEnd_2195964 < baseStart_2195964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195992 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_2195992 : Nat := 118140960795 + 2195992 * 2 ^ 59
def prefixEnd_2195992 : Nat := 4983230072969 + 3 ^ 40 * 2195992 * 2
def baseEnd_2195992 : Nat := 751732939618851603267215

theorem tailTrace_2195992 : CollatzResearch.WordTrace tailWord_2195992 prefixEnd_2195992 751732939618851603267215 := by
  unfold tailWord_2195992
  simp only [CollatzResearch.WordTrace]
  refine ⟨40047204130151752209903115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53396272173535669613204153 40047204130151752209903115)
  ·
    refine ⟨60070806195227628314854673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40047204130151752209903115 60070806195227628314854673)
    ·
      refine ⟨45053104646420721236141005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60070806195227628314854673 45053104646420721236141005)
      ·
        refine ⟨16894914242407770463552877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45053104646420721236141005 16894914242407770463552877)
        ·
          refine ⟨6335592840902913923832329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16894914242407770463552877 6335592840902913923832329)
          ·
            refine ⟨4751694630677185442874247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6335592840902913923832329 4751694630677185442874247)
            ·
              refine ⟨7127541946015778164311371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4751694630677185442874247 7127541946015778164311371)
              ·
                refine ⟨10691312919023667246467057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7127541946015778164311371 10691312919023667246467057)
                ·
                  refine ⟨8018484689267750434850293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10691312919023667246467057 8018484689267750434850293)
                  ·
                    refine ⟨751732939618851603267215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8018484689267750434850293 751732939618851603267215)
                    ·
                      rfl

theorem cell22_2195992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_2195992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195992 prefixEnd_2195992 := by exact prefixLift 2195992
  have htrace : WordTrace (prefixWord ++ tailWord_2195992) baseStart_2195992 baseEnd_2195992 := by
    simpa [prefixWord, tailWord_2195992, baseEnd_2195992] using wordTrace_append hprefix tailTrace_2195992
  have hstable : (prefixWord ++ tailWord_2195992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195992).length < 2 ^ (prefixWord ++ tailWord_2195992).sum := by decide
  have hdescent : baseEnd_2195992 < baseStart_2195992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196005 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 8]
def baseStart_2196005 : Nat := 118140960795 + 2196005 * 2 ^ 59
def prefixEnd_2196005 : Nat := 4983230072969 + 3 ^ 40 * 2196005 * 2
def baseEnd_2196005 : Nat := 250579129928174634230725

theorem tailTrace_2196005 : CollatzResearch.WordTrace tailWord_2196005 prefixEnd_2196005 250579129928174634230725 := by
  unfold tailWord_2196005
  simp only [CollatzResearch.WordTrace]
  refine ⟨80094882409256407640029469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53396588272837605093352979 80094882409256407640029469)
  ·
    refine ⟨30035580903471152865011051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80094882409256407640029469 30035580903471152865011051)
    ·
      refine ⟨45053371355206729297516577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30035580903471152865011051 45053371355206729297516577)
      ·
        refine ⟨33790028516405046973137433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45053371355206729297516577 33790028516405046973137433)
        ·
          refine ⟨25342521387303785229853075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33790028516405046973137433 25342521387303785229853075)
          ·
            refine ⟨38013782080955677844779613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25342521387303785229853075 38013782080955677844779613)
            ·
              refine ⟨14255168280358379191792355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38013782080955677844779613 14255168280358379191792355)
              ·
                refine ⟨21382752420537568787688533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14255168280358379191792355 21382752420537568787688533)
                ·
                  refine ⟨250579129928174634230725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21382752420537568787688533 250579129928174634230725)
                  ·
                    rfl

theorem cell22_2196005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_2196005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196005 prefixEnd_2196005 := by exact prefixLift 2196005
  have htrace : WordTrace (prefixWord ++ tailWord_2196005) baseStart_2196005 baseEnd_2196005 := by
    simpa [prefixWord, tailWord_2196005, baseEnd_2196005] using wordTrace_append hprefix tailTrace_2196005
  have hstable : (prefixWord ++ tailWord_2196005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196005).length < 2 ^ (prefixWord ++ tailWord_2196005).sum := by decide
  have hdescent : baseEnd_2196005 < baseStart_2196005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196039 : List Nat := [1, 1, 4, 1, 4, 1, 2, 4, 4]
def baseStart_2196039 : Nat := 118140960795 + 2196039 * 2 ^ 59
def prefixEnd_2196039 : Nat := 4983230072969 + 3 ^ 40 * 2196039 * 2
def baseEnd_2196039 : Nat := 250583009559786382447357

theorem tailTrace_2196039 : CollatzResearch.WordTrace tailWord_2196039 prefixEnd_2196039 250583009559786382447357 := by
  unfold tailWord_2196039
  simp only [CollatzResearch.WordTrace]
  refine ⟨80096122491133231446767171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53397414994088820964511447 80096122491133231446767171)
  ·
    refine ⟨120144183736699847170150757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80096122491133231446767171 120144183736699847170150757)
    ·
      refine ⟨22527034450631221344403267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120144183736699847170150757 22527034450631221344403267)
      ·
        refine ⟨33790551675946832016604901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22527034450631221344403267 33790551675946832016604901)
        ·
          refine ⟨6335728439240031003113419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33790551675946832016604901 6335728439240031003113419)
          ·
            refine ⟨9503592658860046504670129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6335728439240031003113419 9503592658860046504670129)
            ·
              refine ⟨7127694494145034878502597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9503592658860046504670129 7127694494145034878502597)
              ·
                refine ⟨1336442717652194039719237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7127694494145034878502597 1336442717652194039719237)
                ·
                  refine ⟨250583009559786382447357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336442717652194039719237 250583009559786382447357)
                  ·
                    rfl

theorem cell22_2196039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 4].length) (baseStart_2196039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196039 prefixEnd_2196039 := by exact prefixLift 2196039
  have htrace : WordTrace (prefixWord ++ tailWord_2196039) baseStart_2196039 baseEnd_2196039 := by
    simpa [prefixWord, tailWord_2196039, baseEnd_2196039] using wordTrace_append hprefix tailTrace_2196039
  have hstable : (prefixWord ++ tailWord_2196039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196039).length < 2 ^ (prefixWord ++ tailWord_2196039).sum := by decide
  have hdescent : baseEnd_2196039 < baseStart_2196039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196052 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2196052 : Nat := 118140960795 + 2196052 * 2 ^ 59
def prefixEnd_2196052 : Nat := 4983230072969 + 3 ^ 40 * 2196052 * 2
def baseEnd_2196052 : Nat := 751753478845031446767031

theorem tailTrace_2196052 : CollatzResearch.WordTrace tailWord_2196052 prefixEnd_2196052 751753478845031446767031 := by
  unfold tailWord_2196052
  simp only [CollatzResearch.WordTrace]
  refine ⟨40048298320043067333495205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53397731093390756444660273 40048298320043067333495205)
  ·
    refine ⟨7509055935008075125030351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40048298320043067333495205 7509055935008075125030351)
    ·
      refine ⟨11263583902512112687545527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509055935008075125030351 11263583902512112687545527)
      ·
        refine ⟨16895375853768169031318291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11263583902512112687545527 16895375853768169031318291)
        ·
          refine ⟨25343063780652253546977437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16895375853768169031318291 25343063780652253546977437)
          ·
            refine ⟨9503648917744595080116539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25343063780652253546977437 9503648917744595080116539)
            ·
              refine ⟨14255473376616892620174809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9503648917744595080116539 14255473376616892620174809)
              ·
                refine ⟨10691605032462669465131107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14255473376616892620174809 10691605032462669465131107)
                ·
                  refine ⟨16037407548694004197696661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10691605032462669465131107 16037407548694004197696661)
                  ·
                    refine ⟨751753478845031446767031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16037407548694004197696661 751753478845031446767031)
                    ·
                      rfl

theorem cell22_2196052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2196052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196052 prefixEnd_2196052 := by exact prefixLift 2196052
  have htrace : WordTrace (prefixWord ++ tailWord_2196052) baseStart_2196052 baseEnd_2196052 := by
    simpa [prefixWord, tailWord_2196052, baseEnd_2196052] using wordTrace_append hprefix tailTrace_2196052
  have hstable : (prefixWord ++ tailWord_2196052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196052).length < 2 ^ (prefixWord ++ tailWord_2196052).sum := by decide
  have hdescent : baseEnd_2196052 < baseStart_2196052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196086 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_2196086 : Nat := 118140960795 + 2196086 * 2 ^ 59
def prefixEnd_2196086 : Nat := 4983230072969 + 3 ^ 40 * 2196086 * 2
def baseEnd_2196086 : Nat := 751765117739866691416927

theorem tailTrace_2196086 : CollatzResearch.WordTrace tailWord_2196086 prefixEnd_2196086 751765117739866691416927 := by
  unfold tailWord_2196086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006114795122684904608007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53398557814641972315818741 5006114795122684904608007)
  ·
    refine ⟨7509172192684027356912011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5006114795122684904608007 7509172192684027356912011)
    ·
      refine ⟨11263758289026041035368017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509172192684027356912011 11263758289026041035368017)
      ·
        refine ⟨8447818716769530776526013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11263758289026041035368017 8447818716769530776526013)
        ·
          refine ⟨3167932018788574041197255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8447818716769530776526013 3167932018788574041197255)
          ·
            refine ⟨4751898028182861061795883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167932018788574041197255 4751898028182861061795883)
            ·
              refine ⟨7127847042274291592693825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4751898028182861061795883 7127847042274291592693825)
              ·
                refine ⟨5345885281705718694520369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7127847042274291592693825 5345885281705718694520369)
                ·
                  refine ⟨4009413961279289020890277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5345885281705718694520369 4009413961279289020890277)
                  ·
                    refine ⟨751765117739866691416927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4009413961279289020890277 751765117739866691416927)
                    ·
                      rfl

theorem cell22_2196086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_2196086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196086 prefixEnd_2196086 := by exact prefixLift 2196086
  have htrace : WordTrace (prefixWord ++ tailWord_2196086) baseStart_2196086 baseEnd_2196086 := by
    simpa [prefixWord, tailWord_2196086, baseEnd_2196086] using wordTrace_append hprefix tailTrace_2196086
  have hstable : (prefixWord ++ tailWord_2196086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196086).length < 2 ^ (prefixWord ++ tailWord_2196086).sum := by decide
  have hdescent : baseEnd_2196086 < baseStart_2196086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196097 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2196097 : Nat := 118140960795 + 2196097 * 2 ^ 59
def prefixEnd_2196097 : Nat := 4983230072969 + 3 ^ 40 * 2196097 * 2
def baseEnd_2196097 : Nat := 751768883264666329391893

theorem tailTrace_2196097 : CollatzResearch.WordTrace tailWord_2196097 prefixEnd_2196097 751768883264666329391893 := by
  unfold tailWord_2196097
  simp only [CollatzResearch.WordTrace]
  refine ⟨80098237924923107352378545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53398825283282071568252363 80098237924923107352378545)
  ·
    refine ⟨60073678443692330514283909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80098237924923107352378545 60073678443692330514283909)
    ·
      refine ⟨11263814708192311971428233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60073678443692330514283909 11263814708192311971428233)
      ·
        refine ⟨8447861031144233978571175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11263814708192311971428233 8447861031144233978571175)
        ·
          refine ⟨12671791546716350967856763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8447861031144233978571175 12671791546716350967856763)
          ·
            refine ⟨19007687320074526451785145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12671791546716350967856763 19007687320074526451785145)
            ·
              refine ⟨14255765490055894838838859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19007687320074526451785145 14255765490055894838838859)
              ·
                refine ⟨21383648235083842258258289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14255765490055894838838859 21383648235083842258258289)
                ·
                  refine ⟨16037736176312881693693717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21383648235083842258258289 16037736176312881693693717)
                  ·
                    refine ⟨751768883264666329391893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16037736176312881693693717 751768883264666329391893)
                    ·
                      rfl

theorem cell22_2196097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2196097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196097 prefixEnd_2196097 := by exact prefixLift 2196097
  have htrace : WordTrace (prefixWord ++ tailWord_2196097) baseStart_2196097 baseEnd_2196097 := by
    simpa [prefixWord, tailWord_2196097, baseEnd_2196097] using wordTrace_append hprefix tailTrace_2196097
  have hstable : (prefixWord ++ tailWord_2196097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196097).length < 2 ^ (prefixWord ++ tailWord_2196097).sum := by decide
  have hdescent : baseEnd_2196097 < baseStart_2196097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196099 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 3, 3]
def baseStart_2196099 : Nat := 118140960795 + 2196099 * 2 ^ 59
def prefixEnd_2196099 : Nat := 4983230072969 + 3 ^ 40 * 2196099 * 2
def baseEnd_2196099 : Nat := 751769567905538990841887

theorem tailTrace_2196099 : CollatzResearch.WordTrace tailWord_2196099 prefixEnd_2196099 751769567905538990841887 := by
  unfold tailWord_2196099
  simp only [CollatzResearch.WordTrace]
  refine ⟨80098310870915861693951351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53398873913943907795967567 80098310870915861693951351)
  ·
    refine ⟨120147466306373792540927027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80098310870915861693951351 120147466306373792540927027)
    ·
      refine ⟨180221199459560688811390541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120147466306373792540927027 180221199459560688811390541)
      ·
        refine ⟨67582949797335258304271453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180221199459560688811390541 67582949797335258304271453)
        ·
          refine ⟨25343606174000721864101795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67582949797335258304271453 25343606174000721864101795)
          ·
            refine ⟨38015409261001082796152693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25343606174000721864101795 38015409261001082796152693)
            ·
              refine ⟨3563944618218851512139315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38015409261001082796152693 3563944618218851512139315)
              ·
                refine ⟨5345916927328277268208973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563944618218851512139315 5345916927328277268208973)
                ·
                  refine ⟨2004718847748103975578365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5345916927328277268208973 2004718847748103975578365)
                  ·
                    refine ⟨751769567905538990841887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004718847748103975578365 751769567905538990841887)
                    ·
                      rfl

theorem cell22_2196099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 3].length) (baseStart_2196099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196099 prefixEnd_2196099 := by exact prefixLift 2196099
  have htrace : WordTrace (prefixWord ++ tailWord_2196099) baseStart_2196099 baseEnd_2196099 := by
    simpa [prefixWord, tailWord_2196099, baseEnd_2196099] using wordTrace_append hprefix tailTrace_2196099
  have hstable : (prefixWord ++ tailWord_2196099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196099).length < 2 ^ (prefixWord ++ tailWord_2196099).sum := by decide
  have hdescent : baseEnd_2196099 < baseStart_2196099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196174 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_2196174 : Nat := 118140960795 + 2196174 * 2 ^ 59
def prefixEnd_2196174 : Nat := 4983230072969 + 3 ^ 40 * 2196174 * 2
def baseEnd_2196174 : Nat := 250598413979421265072219

theorem tailTrace_2196174 : CollatzResearch.WordTrace tailWord_2196174 prefixEnd_2196174 250598413979421265072219 := by
  unfold tailWord_2196174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012630793205518687866447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53400697563762766335287717 10012630793205518687866447)
  ·
    refine ⟨15018946189808278031799671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10012630793205518687866447 15018946189808278031799671)
    ·
      refine ⟨22528419284712417047699507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15018946189808278031799671 22528419284712417047699507)
      ·
        refine ⟨33792628927068625571549261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22528419284712417047699507 33792628927068625571549261)
        ·
          refine ⟨12672235847650734589330973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33792628927068625571549261 12672235847650734589330973)
          ·
            refine ⟨4752088442869025470999115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12672235847650734589330973 4752088442869025470999115)
            ·
              refine ⟨7128132664303538206498673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752088442869025470999115 7128132664303538206498673)
              ·
                refine ⟨5346099498227653654874005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7128132664303538206498673 5346099498227653654874005)
                ·
                  refine ⟨250598413979421265072219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5346099498227653654874005 250598413979421265072219)
                  ·
                    rfl

theorem cell22_2196174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_2196174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196174 prefixEnd_2196174 := by exact prefixLift 2196174
  have htrace : WordTrace (prefixWord ++ tailWord_2196174) baseStart_2196174 baseEnd_2196174 := by
    simpa [prefixWord, tailWord_2196174, baseEnd_2196174] using wordTrace_append hprefix tailTrace_2196174
  have hstable : (prefixWord ++ tailWord_2196174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196174).length < 2 ^ (prefixWord ++ tailWord_2196174).sum := by decide
  have hdescent : baseEnd_2196174 < baseStart_2196174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196187 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 8, 4]
def baseStart_2196187 : Nat := 118140960795 + 2196187 * 2 ^ 59
def prefixEnd_2196187 : Nat := 4983230072969 + 3 ^ 40 * 2196187 * 2
def baseEnd_2196187 : Nat := 751799692103936094641617

theorem tailTrace_2196187 : CollatzResearch.WordTrace tailWord_2196187 prefixEnd_2196187 751799692103936094641617 := by
  unfold tailWord_2196187
  simp only [CollatzResearch.WordTrace]
  refine ⟨80101520494597052723154815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53401013663064701815436543 80101520494597052723154815)
  ·
    refine ⟨120152280741895579084732223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80101520494597052723154815 120152280741895579084732223)
    ·
      refine ⟨180228421112843368627098335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120152280741895579084732223 180228421112843368627098335)
      ·
        refine ⟨270342631669265052940647503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180228421112843368627098335 270342631669265052940647503)
        ·
          refine ⟨405513947503897579410971255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270342631669265052940647503 405513947503897579410971255)
          ·
            refine ⟨608270921255846369116456883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405513947503897579410971255 608270921255846369116456883)
            ·
              refine ⟨912406381883769553674685325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608270921255846369116456883 912406381883769553674685325)
              ·
                refine ⟨342152393206413582628006997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 912406381883769553674685325 342152393206413582628006997)
                ·
                  refine ⟨4009598357887659171421957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 342152393206413582628006997 4009598357887659171421957)
                  ·
                    refine ⟨751799692103936094641617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4009598357887659171421957 751799692103936094641617)
                    ·
                      rfl

theorem cell22_2196187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 4].length) (baseStart_2196187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196187 prefixEnd_2196187 := by exact prefixLift 2196187
  have htrace : WordTrace (prefixWord ++ tailWord_2196187) baseStart_2196187 baseEnd_2196187 := by
    simpa [prefixWord, tailWord_2196187, baseEnd_2196187] using wordTrace_append hprefix tailTrace_2196187
  have hstable : (prefixWord ++ tailWord_2196187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196187).length < 2 ^ (prefixWord ++ tailWord_2196187).sum := by decide
  have hdescent : baseEnd_2196187 < baseStart_2196187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196191 : List Nat := [1, 1, 2, 3, 2, 4, 2, 3, 4]
def baseStart_2196191 : Nat := 118140960795 + 2196191 * 2 ^ 59
def prefixEnd_2196191 : Nat := 4983230072969 + 3 ^ 40 * 2196191 * 2
def baseEnd_2196191 : Nat := 250600353795227139180535

theorem tailTrace_2196191 : CollatzResearch.WordTrace tailWord_2196191 prefixEnd_2196191 250600353795227139180535 := by
  unfold tailWord_2196191
  simp only [CollatzResearch.WordTrace]
  refine ⟨80101666386582561406300427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53401110924388374270866951 80101666386582561406300427)
  ·
    refine ⟨120152499579873842109450641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80101666386582561406300427 120152499579873842109450641)
    ·
      refine ⟨90114374684905381582087981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120152499579873842109450641 90114374684905381582087981)
      ·
        refine ⟨33792890506839518093282993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90114374684905381582087981 33792890506839518093282993)
        ·
          refine ⟨25344667880129638569962245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33792890506839518093282993 25344667880129638569962245)
          ·
            refine ⟨4752125227524307231867921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25344667880129638569962245 4752125227524307231867921)
            ·
              refine ⟨3564093920643230423900941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4752125227524307231867921 3564093920643230423900941)
              ·
                refine ⟨1336535220241211408962853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3564093920643230423900941 1336535220241211408962853)
                ·
                  refine ⟨250600353795227139180535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336535220241211408962853 250600353795227139180535)
                  ·
                    rfl

theorem cell22_2196191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 4].length) (baseStart_2196191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196191 prefixEnd_2196191 := by exact prefixLift 2196191
  have htrace : WordTrace (prefixWord ++ tailWord_2196191) baseStart_2196191 baseEnd_2196191 := by
    simpa [prefixWord, tailWord_2196191, baseEnd_2196191] using wordTrace_append hprefix tailTrace_2196191
  have hstable : (prefixWord ++ tailWord_2196191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196191).length < 2 ^ (prefixWord ++ tailWord_2196191).sum := by decide
  have hdescent : baseEnd_2196191 < baseStart_2196191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196193 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 1, 4]
def baseStart_2196193 : Nat := 118140960795 + 2196193 * 2 ^ 59
def prefixEnd_2196193 : Nat := 4983230072969 + 3 ^ 40 * 2196193 * 2
def baseEnd_2196193 : Nat := 751801746026554078991599

theorem tailTrace_2196193 : CollatzResearch.WordTrace tailWord_2196193 prefixEnd_2196193 751801746026554078991599 := by
  unfold tailWord_2196193
  simp only [CollatzResearch.WordTrace]
  refine ⟨80101739332575315747873233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53401159555050210498582155 80101739332575315747873233)
  ·
    refine ⟨60076304499431486810904925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80101739332575315747873233 60076304499431486810904925)
    ·
      refine ⟨22528614187286807554089347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60076304499431486810904925 22528614187286807554089347)
      ·
        refine ⟨33792921280930211331134021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22528614187286807554089347 33792921280930211331134021)
        ·
          refine ⟨6336172740174414624587629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33792921280930211331134021 6336172740174414624587629)
          ·
            refine ⟨2376064777565405484220361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6336172740174414624587629 2376064777565405484220361)
            ·
              refine ⟨1782048583174054113165271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2376064777565405484220361 1782048583174054113165271)
              ·
                refine ⟨2673072874761081169747907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782048583174054113165271 2673072874761081169747907)
                ·
                  refine ⟨4009609312141621754621861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673072874761081169747907 4009609312141621754621861)
                  ·
                    refine ⟨751801746026554078991599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4009609312141621754621861 751801746026554078991599)
                    ·
                      rfl

theorem cell22_2196193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_2196193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196193 prefixEnd_2196193 := by exact prefixLift 2196193
  have htrace : WordTrace (prefixWord ++ tailWord_2196193) baseStart_2196193 baseEnd_2196193 := by
    simpa [prefixWord, tailWord_2196193, baseEnd_2196193] using wordTrace_append hprefix tailTrace_2196193
  have hstable : (prefixWord ++ tailWord_2196193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196193).length < 2 ^ (prefixWord ++ tailWord_2196193).sum := by decide
  have hdescent : baseEnd_2196193 < baseStart_2196193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196206 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2196206 : Nat := 118140960795 + 2196206 * 2 ^ 59
def prefixEnd_2196206 : Nat := 4983230072969 + 3 ^ 40 * 2196206 * 2
def baseEnd_2196206 : Nat := 751806196192226378416559

theorem tailTrace_2196206 : CollatzResearch.WordTrace tailWord_2196206 prefixEnd_2196206 751806196192226378416559 := by
  unfold tailWord_2196206
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012776685191027371012059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53401475654352145978730981 10012776685191027371012059)
  ·
    refine ⟨15019165027786541056518089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10012776685191027371012059 15019165027786541056518089)
    ·
      refine ⟨11264373770839905792388567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15019165027786541056518089 11264373770839905792388567)
      ·
        refine ⟨16896560656259858688582851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11264373770839905792388567 16896560656259858688582851)
        ·
          refine ⟨25344840984389788032874277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16896560656259858688582851 25344840984389788032874277)
          ·
            refine ⟨4752157684573085256163927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25344840984389788032874277 4752157684573085256163927)
            ·
              refine ⟨7128236526859627884245891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752157684573085256163927 7128236526859627884245891)
              ·
                refine ⟨10692354790289441826368837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7128236526859627884245891 10692354790289441826368837)
                ·
                  refine ⟨2004816523179270342444157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10692354790289441826368837 2004816523179270342444157)
                  ·
                    refine ⟨751806196192226378416559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004816523179270342444157 751806196192226378416559)
                    ·
                      rfl

theorem cell22_2196206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2196206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196206 prefixEnd_2196206 := by exact prefixLift 2196206
  have htrace : WordTrace (prefixWord ++ tailWord_2196206) baseStart_2196206 baseEnd_2196206 := by
    simpa [prefixWord, tailWord_2196206, baseEnd_2196206] using wordTrace_append hprefix tailTrace_2196206
  have hstable : (prefixWord ++ tailWord_2196206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196206).length < 2 ^ (prefixWord ++ tailWord_2196206).sum := by decide
  have hdescent : baseEnd_2196206 < baseStart_2196206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196242 : List Nat := [3, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_2196242 : Nat := 118140960795 + 2196242 * 2 ^ 59
def prefixEnd_2196242 : Nat := 4983230072969 + 3 ^ 40 * 2196242 * 2
def baseEnd_2196242 : Nat := 250606173242644761505483

theorem tailTrace_2196242 : CollatzResearch.WordTrace tailWord_2196242 prefixEnd_2196242 250606173242644761505483 := by
  unfold tailWord_2196242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20025881627349449279101745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53402351006265198077604653 20025881627349449279101745)
  ·
    refine ⟨15019411220512086959326309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20025881627349449279101745 15019411220512086959326309)
    ·
      refine ⟨2816139603846016304873683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15019411220512086959326309 2816139603846016304873683)
      ·
        refine ⟨4224209405769024457310525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2816139603846016304873683 4224209405769024457310525)
        ·
          refine ⟨1584078527163384171491447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4224209405769024457310525 1584078527163384171491447)
          ·
            refine ⟨2376117790745076257237171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584078527163384171491447 2376117790745076257237171)
            ·
              refine ⟨3564176686117614385855757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376117790745076257237171 3564176686117614385855757)
              ·
                refine ⟨1336566257294105394695909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3564176686117614385855757 1336566257294105394695909)
                ·
                  refine ⟨250606173242644761505483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336566257294105394695909 250606173242644761505483)
                  ·
                    rfl

theorem cell22_2196242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_2196242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196242 prefixEnd_2196242 := by exact prefixLift 2196242
  have htrace : WordTrace (prefixWord ++ tailWord_2196242) baseStart_2196242 baseEnd_2196242 := by
    simpa [prefixWord, tailWord_2196242, baseEnd_2196242] using wordTrace_append hprefix tailTrace_2196242
  have hstable : (prefixWord ++ tailWord_2196242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196242).length < 2 ^ (prefixWord ++ tailWord_2196242).sum := by decide
  have hdescent : baseEnd_2196242 < baseStart_2196242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196253 : List Nat := [1, 4, 2, 4, 2, 1, 8]
def baseStart_2196253 : Nat := 118140960795 + 2196253 * 2 ^ 59
def prefixEnd_2196253 : Nat := 4983230072969 + 3 ^ 40 * 2196253 * 2
def baseEnd_2196253 : Nat := 27845269824175330462645

theorem tailTrace_2196253 : CollatzResearch.WordTrace tailWord_2196253 prefixEnd_2196253 27845269824175330462645 := by
  unfold tailWord_2196253
  simp only [CollatzResearch.WordTrace]
  refine ⟨80103927712357945995057413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53402618474905297330038275 80103927712357945995057413)
  ·
    refine ⟨15019486446067114874073265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80103927712357945995057413 15019486446067114874073265)
    ·
      refine ⟨11264614834550336155554949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15019486446067114874073265 11264614834550336155554949)
      ·
        refine ⟨2112115281478188029166553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11264614834550336155554949 2112115281478188029166553)
        ·
          refine ⟨1584086461108641021874915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2112115281478188029166553 1584086461108641021874915)
          ·
            refine ⟨2376129691662961532812373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584086461108641021874915 2376129691662961532812373)
            ·
              refine ⟨27845269824175330462645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2376129691662961532812373 27845269824175330462645)
              ·
                rfl

theorem cell22_2196253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 8].length) (baseStart_2196253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196253 prefixEnd_2196253 := by exact prefixLift 2196253
  have htrace : WordTrace (prefixWord ++ tailWord_2196253) baseStart_2196253 baseEnd_2196253 := by
    simpa [prefixWord, tailWord_2196253, baseEnd_2196253] using wordTrace_append hprefix tailTrace_2196253
  have hstable : (prefixWord ++ tailWord_2196253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196253).length < 2 ^ (prefixWord ++ tailWord_2196253).sum := by decide
  have hdescent : baseEnd_2196253 < baseStart_2196253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196264 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 7]
def baseStart_2196264 : Nat := 118140960795 + 2196264 * 2 ^ 59
def prefixEnd_2196264 : Nat := 4983230072969 + 3 ^ 40 * 2196264 * 2
def baseEnd_2196264 : Nat := 250608683592511186822127

theorem tailTrace_2196264 : CollatzResearch.WordTrace tailWord_2196264 prefixEnd_2196264 250608683592511186822127 := by
  unfold tailWord_2196264
  simp only [CollatzResearch.WordTrace]
  refine ⟨40052164457659047436853923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53402885943545396582471897 40052164457659047436853923)
  ·
    refine ⟨60078246686488571155280885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40052164457659047436853923 60078246686488571155280885)
    ·
      refine ⟨5632335626858303545807583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60078246686488571155280885 5632335626858303545807583)
      ·
        refine ⟨8448503440287455318711375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5632335626858303545807583 8448503440287455318711375)
        ·
          refine ⟨12672755160431182978067063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8448503440287455318711375 12672755160431182978067063)
          ·
            refine ⟨19009132740646774467100595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12672755160431182978067063 19009132740646774467100595)
            ·
              refine ⟨28513699110970161700650893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19009132740646774467100595 28513699110970161700650893)
              ·
                refine ⟨10692637166613810637744085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28513699110970161700650893 10692637166613810637744085)
                ·
                  refine ⟨250608683592511186822127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10692637166613810637744085 250608683592511186822127)
                  ·
                    rfl

theorem cell22_2196264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_2196264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196264 prefixEnd_2196264 := by exact prefixLift 2196264
  have htrace : WordTrace (prefixWord ++ tailWord_2196264) baseStart_2196264 baseEnd_2196264 := by
    simpa [prefixWord, tailWord_2196264, baseEnd_2196264] using wordTrace_append hprefix tailTrace_2196264
  have hstable : (prefixWord ++ tailWord_2196264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196264).length < 2 ^ (prefixWord ++ tailWord_2196264).sum := by decide
  have hdescent : baseEnd_2196264 < baseStart_2196264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196339 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 4, 4]
def baseStart_2196339 : Nat := 118140960795 + 2196339 * 2 ^ 59
def prefixEnd_2196339 : Nat := 4983230072969 + 3 ^ 40 * 2196339 * 2
def baseEnd_2196339 : Nat := 751851724810258364841151

theorem tailTrace_2196339 : CollatzResearch.WordTrace tailWord_2196339 prefixEnd_2196339 751851724810258364841151 := by
  unfold tailWord_2196339
  simp only [CollatzResearch.WordTrace]
  refine ⟨80107064390046382682688071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53404709593364255121792047 80107064390046382682688071)
  ·
    refine ⟨120160596585069574024032107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80107064390046382682688071 120160596585069574024032107)
    ·
      refine ⟨180240894877604361036048161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120160596585069574024032107 180240894877604361036048161)
      ·
        refine ⟨135180671158203270777036121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180240894877604361036048161 135180671158203270777036121)
        ·
          refine ⟨101385503368652453082777091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135180671158203270777036121 101385503368652453082777091)
          ·
            refine ⟨152078255052978679624165637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101385503368652453082777091 152078255052978679624165637)
            ·
              refine ⟨28514672822433502429531057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152078255052978679624165637 28514672822433502429531057)
              ·
                refine ⟨21386004616825126822148293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28514672822433502429531057 21386004616825126822148293)
                ·
                  refine ⟨4009875865654711279152805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21386004616825126822148293 4009875865654711279152805)
                  ·
                    refine ⟨751851724810258364841151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4009875865654711279152805 751851724810258364841151)
                    ·
                      rfl

theorem cell22_2196339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 4].length) (baseStart_2196339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196339 prefixEnd_2196339 := by exact prefixLift 2196339
  have htrace : WordTrace (prefixWord ++ tailWord_2196339) baseStart_2196339 baseEnd_2196339 := by
    simpa [prefixWord, tailWord_2196339, baseEnd_2196339] using wordTrace_append hprefix tailTrace_2196339
  have hstable : (prefixWord ++ tailWord_2196339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196339).length < 2 ^ (prefixWord ++ tailWord_2196339).sum := by decide
  have hdescent : baseEnd_2196339 < baseStart_2196339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196341 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2196341 : Nat := 118140960795 + 2196341 * 2 ^ 59
def prefixEnd_2196341 : Nat := 4983230072969 + 3 ^ 40 * 2196341 * 2
def baseEnd_2196341 : Nat := 751852409451131026291145

theorem tailTrace_2196341 : CollatzResearch.WordTrace tailWord_2196341 prefixEnd_2196341 751852409451131026291145 := by
  unfold tailWord_2196341
  simp only [CollatzResearch.WordTrace]
  refine ⟨80107137336039137024260877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53404758224026091349507251 80107137336039137024260877)
  ·
    refine ⟨30040176501014676384097829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80107137336039137024260877 30040176501014676384097829)
    ·
      refine ⟨5632533093940251822018343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30040176501014676384097829 5632533093940251822018343)
      ·
        refine ⟨8448799640910377733027515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5632533093940251822018343 8448799640910377733027515)
        ·
          refine ⟨12673199461365566599541273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8448799640910377733027515 12673199461365566599541273)
          ·
            refine ⟨9504899596024174949655955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12673199461365566599541273 9504899596024174949655955)
            ·
              refine ⟨14257349394036262424483933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9504899596024174949655955 14257349394036262424483933)
              ·
                refine ⟨5346506022763598409181475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14257349394036262424483933 5346506022763598409181475)
                ·
                  refine ⟨8019759034145397613772213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5346506022763598409181475 8019759034145397613772213)
                  ·
                    refine ⟨751852409451131026291145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8019759034145397613772213 751852409451131026291145)
                    ·
                      rfl

theorem cell22_2196341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2196341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196341 prefixEnd_2196341 := by exact prefixLift 2196341
  have htrace : WordTrace (prefixWord ++ tailWord_2196341) baseStart_2196341 baseEnd_2196341 := by
    simpa [prefixWord, tailWord_2196341, baseEnd_2196341] using wordTrace_append hprefix tailTrace_2196341
  have hstable : (prefixWord ++ tailWord_2196341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196341).length < 2 ^ (prefixWord ++ tailWord_2196341).sum := by decide
  have hdescent : baseEnd_2196341 < baseStart_2196341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196384 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_2196384 : Nat := 118140960795 + 2196384 * 2 ^ 59
def prefixEnd_2196384 : Nat := 4983230072969 + 3 ^ 40 * 2196384 * 2
def baseEnd_2196384 : Nat := 751867129229893247466013

theorem tailTrace_2196384 : CollatzResearch.WordTrace tailWord_2196384 prefixEnd_2196384 751867129229893247466013 := by
  unfold tailWord_2196384
  simp only [CollatzResearch.WordTrace]
  refine ⟨40054352837441677684038103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53405803783255570245384137 40054352837441677684038103)
  ·
    refine ⟨60081529256162516526057155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40054352837441677684038103 60081529256162516526057155)
    ·
      refine ⟨90122293884243774789085733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60081529256162516526057155 90122293884243774789085733)
      ·
        refine ⟨16897930103295707772953575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90122293884243774789085733 16897930103295707772953575)
        ·
          refine ⟨25346895154943561659430363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16897930103295707772953575 25346895154943561659430363)
          ·
            refine ⟨38020342732415342489145545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25346895154943561659430363 38020342732415342489145545)
            ·
              refine ⟨28515257049311506866859159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38020342732415342489145545 28515257049311506866859159)
              ·
                refine ⟨42772885573967260300288739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28515257049311506866859159 42772885573967260300288739)
                ·
                  refine ⟨64159328360950890450433109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42772885573967260300288739 64159328360950890450433109)
                  ·
                    refine ⟨751867129229893247466013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64159328360950890450433109 751867129229893247466013)
                    ·
                      rfl

theorem cell22_2196384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_2196384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196384 prefixEnd_2196384 := by exact prefixLift 2196384
  have htrace : WordTrace (prefixWord ++ tailWord_2196384) baseStart_2196384 baseEnd_2196384 := by
    simpa [prefixWord, tailWord_2196384, baseEnd_2196384] using wordTrace_append hprefix tailTrace_2196384
  have hstable : (prefixWord ++ tailWord_2196384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196384).length < 2 ^ (prefixWord ++ tailWord_2196384).sum := by decide
  have hdescent : baseEnd_2196384 < baseStart_2196384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196437 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_2196437 : Nat := 118140960795 + 2196437 * 2 ^ 59
def prefixEnd_2196437 : Nat := 4983230072969 + 3 ^ 40 * 2196437 * 2
def baseEnd_2196437 : Nat := 751885272213018775890851

theorem tailTrace_2196437 : CollatzResearch.WordTrace tailWord_2196437 prefixEnd_2196437 751885272213018775890851 := by
  unfold tailWord_2196437
  simp only [CollatzResearch.WordTrace]
  refine ⟨80110638743691345419755565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53407092495794230279837043 80110638743691345419755565)
  ·
    refine ⟨30041489528884254532408337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80110638743691345419755565 30041489528884254532408337)
    ·
      refine ⟨22531117146663190899306253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30041489528884254532408337 22531117146663190899306253)
      ·
        refine ⟨8449168929998696587239845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22531117146663190899306253 8449168929998696587239845)
        ·
          refine ⟨1584219174374755610107471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8449168929998696587239845 1584219174374755610107471)
          ·
            refine ⟨2376328761562133415161207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584219174374755610107471 2376328761562133415161207)
            ·
              refine ⟨3564493142343200122741811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376328761562133415161207 3564493142343200122741811)
              ·
                refine ⟨5346739713514800184112717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3564493142343200122741811 5346739713514800184112717)
                ·
                  refine ⟨2005027392568050069042269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5346739713514800184112717 2005027392568050069042269)
                  ·
                    refine ⟨751885272213018775890851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005027392568050069042269 751885272213018775890851)
                    ·
                      rfl

theorem cell22_2196437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_2196437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196437 prefixEnd_2196437 := by exact prefixLift 2196437
  have htrace : WordTrace (prefixWord ++ tailWord_2196437) baseStart_2196437 baseEnd_2196437 := by
    simpa [prefixWord, tailWord_2196437, baseEnd_2196437] using wordTrace_append hprefix tailTrace_2196437
  have hstable : (prefixWord ++ tailWord_2196437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196437).length < 2 ^ (prefixWord ++ tailWord_2196437).sum := by decide
  have hdescent : baseEnd_2196437 < baseStart_2196437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196450 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_2196450 : Nat := 118140960795 + 2196450 * 2 ^ 59
def prefixEnd_2196450 : Nat := 4983230072969 + 3 ^ 40 * 2196450 * 2
def baseEnd_2196450 : Nat := 250629907459563691771937

theorem tailTrace_2196450 : CollatzResearch.WordTrace tailWord_2196450 prefixEnd_2196450 250629907459563691771937 := by
  unfold tailWord_2196450
  simp only [CollatzResearch.WordTrace]
  refine ⟨20027778223161062159994701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53407408595096165759985869 20027778223161062159994701)
  ·
    refine ⟨7510416833685398309998013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20027778223161062159994701 7510416833685398309998013)
    ·
      refine ⟨2816406312632024366249255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7510416833685398309998013 2816406312632024366249255)
      ·
        refine ⟨4224609468948036549373883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2816406312632024366249255 4224609468948036549373883)
        ·
          refine ⟨6336914203422054824060825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224609468948036549373883 6336914203422054824060825)
          ·
            refine ⟨4752685652566541118045619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6336914203422054824060825 4752685652566541118045619)
            ·
              refine ⟨7129028478849811677068429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752685652566541118045619 7129028478849811677068429)
              ·
                refine ⟨2673385679568679378900661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7129028478849811677068429 2673385679568679378900661)
                ·
                  refine ⟨250629907459563691771937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2673385679568679378900661 250629907459563691771937)
                  ·
                    rfl

theorem cell22_2196450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_2196450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196450 prefixEnd_2196450 := by exact prefixLift 2196450
  have htrace : WordTrace (prefixWord ++ tailWord_2196450) baseStart_2196450 baseEnd_2196450 := by
    simpa [prefixWord, tailWord_2196450, baseEnd_2196450] using wordTrace_append hprefix tailTrace_2196450
  have hstable : (prefixWord ++ tailWord_2196450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196450).length < 2 ^ (prefixWord ++ tailWord_2196450).sum := by decide
  have hdescent : baseEnd_2196450 < baseStart_2196450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196463 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 1, 4]
def baseStart_2196463 : Nat := 118140960795 + 2196463 * 2 ^ 59
def prefixEnd_2196463 : Nat := 4983230072969 + 3 ^ 40 * 2196463 * 2
def baseEnd_2196463 : Nat := 751894172544363374740771

theorem tailTrace_2196463 : CollatzResearch.WordTrace tailWord_2196463 prefixEnd_2196463 751894172544363374740771 := by
  unfold tailWord_2196463
  simp only [CollatzResearch.WordTrace]
  refine ⟨80111587041597151860202043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53407724694398101240134695 80111587041597151860202043)
  ·
    refine ⟨120167380562395727790303065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80111587041597151860202043 120167380562395727790303065)
    ·
      refine ⟨90125535421796795842727299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120167380562395727790303065 90125535421796795842727299)
      ·
        refine ⟨135188303132695193764090949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90125535421796795842727299 135188303132695193764090949)
        ·
          refine ⟨25347806837380348830767053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135188303132695193764090949 25347806837380348830767053)
          ·
            refine ⟨9505427564017630811537645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25347806837380348830767053 9505427564017630811537645)
            ·
              refine ⟨3564535336506611554326617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9505427564017630811537645 3564535336506611554326617)
              ·
                refine ⟨2673401502379958665744963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564535336506611554326617 2673401502379958665744963)
                ·
                  refine ⟨4010102253569937998617445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673401502379958665744963 4010102253569937998617445)
                  ·
                    refine ⟨751894172544363374740771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4010102253569937998617445 751894172544363374740771)
                    ·
                      rfl

theorem cell22_2196463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_2196463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196463 prefixEnd_2196463 := by exact prefixLift 2196463
  have htrace : WordTrace (prefixWord ++ tailWord_2196463) baseStart_2196463 baseEnd_2196463 := by
    simpa [prefixWord, tailWord_2196463, baseEnd_2196463] using wordTrace_append hprefix tailTrace_2196463
  have hstable : (prefixWord ++ tailWord_2196463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196463).length < 2 ^ (prefixWord ++ tailWord_2196463).sum := by decide
  have hdescent : baseEnd_2196463 < baseStart_2196463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196476 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_2196476 : Nat := 118140960795 + 2196476 * 2 ^ 59
def prefixEnd_2196476 : Nat := 4983230072969 + 3 ^ 40 * 2196476 * 2
def baseEnd_2196476 : Nat := 751898622710035674165731

theorem tailTrace_2196476 : CollatzResearch.WordTrace tailWord_2196476 prefixEnd_2196476 751898622710035674165731 := by
  unfold tailWord_2196476
  simp only [CollatzResearch.WordTrace]
  refine ⟨40056030595275027540212641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53408040793700036720283521 40056030595275027540212641)
  ·
    refine ⟨30042022946456270655159481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40056030595275027540212641 30042022946456270655159481)
    ·
      refine ⟨22531517209842202991369611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30042022946456270655159481 22531517209842202991369611)
      ·
        refine ⟨33797275814763304487054417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22531517209842202991369611 33797275814763304487054417)
        ·
          refine ⟨25347956861072478365290813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33797275814763304487054417 25347956861072478365290813)
          ·
            refine ⟨9505483822902179386984055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25347956861072478365290813 9505483822902179386984055)
            ·
              refine ⟨14258225734353269080476083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9505483822902179386984055 14258225734353269080476083)
              ·
                refine ⟨21387338601529903620714125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14258225734353269080476083 21387338601529903620714125)
                ·
                  refine ⟨8020251975573713857767797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21387338601529903620714125 8020251975573713857767797)
                  ·
                    refine ⟨751898622710035674165731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8020251975573713857767797 751898622710035674165731)
                    ·
                      rfl

theorem cell22_2196476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_2196476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196476 prefixEnd_2196476 := by exact prefixLift 2196476
  have htrace : WordTrace (prefixWord ++ tailWord_2196476) baseStart_2196476 baseEnd_2196476 := by
    simpa [prefixWord, tailWord_2196476, baseEnd_2196476] using wordTrace_append hprefix tailTrace_2196476
  have hstable : (prefixWord ++ tailWord_2196476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196476).length < 2 ^ (prefixWord ++ tailWord_2196476).sum := by decide
  have hdescent : baseEnd_2196476 < baseStart_2196476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196574 : List Nat := [4, 4, 1, 1, 1, 3, 2, 6]
def baseStart_2196574 : Nat := 118140960795 + 2196574 * 2 ^ 59
def prefixEnd_2196574 : Nat := 4983230072969 + 3 ^ 40 * 2196574 * 2
def baseEnd_2196574 : Nat := 83548018901421787246159

theorem tailTrace_2196574 : CollatzResearch.WordTrace tailWord_2196574 prefixEnd_2196574 83548018901421787246159 := by
  unfold tailWord_2196574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10014454443024377227186597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53410423696130011878328517 10014454443024377227186597)
  ·
    refine ⟨1877710208067070730097487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10014454443024377227186597 1877710208067070730097487)
    ·
      refine ⟨2816565312100606095146231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1877710208067070730097487 2816565312100606095146231)
      ·
        refine ⟨4224847968150909142719347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2816565312100606095146231 4224847968150909142719347)
        ·
          refine ⟨6337271952226363714079021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224847968150909142719347 6337271952226363714079021)
          ·
            refine ⟨2376476982084886392779633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6337271952226363714079021 2376476982084886392779633)
            ·
              refine ⟨1782357736563664794584725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2376476982084886392779633 1782357736563664794584725)
              ·
                refine ⟨83548018901421787246159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1782357736563664794584725 83548018901421787246159)
                ·
                  rfl

theorem cell22_2196574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_2196574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196574 prefixEnd_2196574 := by exact prefixLift 2196574
  have htrace : WordTrace (prefixWord ++ tailWord_2196574) baseStart_2196574 baseEnd_2196574 := by
    simpa [prefixWord, tailWord_2196574, baseEnd_2196574] using wordTrace_append hprefix tailTrace_2196574
  have hstable : (prefixWord ++ tailWord_2196574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196574).length < 2 ^ (prefixWord ++ tailWord_2196574).sum := by decide
  have hdescent : baseEnd_2196574 < baseStart_2196574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196589 : List Nat := [1, 5, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2196589 : Nat := 118140960795 + 2196589 * 2 ^ 59
def prefixEnd_2196589 : Nat := 4983230072969 + 3 ^ 40 * 2196589 * 2
def baseEnd_2196589 : Nat := 751937304919341046090385

theorem tailTrace_2196589 : CollatzResearch.WordTrace tailWord_2196589 prefixEnd_2196589 751937304919341046090385 := by
  unfold tailWord_2196589
  simp only [CollatzResearch.WordTrace]
  refine ⟨80116182639140675379288821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53410788426093783586192547 80116182639140675379288821)
  ·
    refine ⟨7510892122419438316808327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80116182639140675379288821 7510892122419438316808327)
    ·
      refine ⟨11266338183629157475212491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7510892122419438316808327 11266338183629157475212491)
      ·
        refine ⟨16899507275443736212818737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11266338183629157475212491 16899507275443736212818737)
        ·
          refine ⟨12674630456582802159614053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16899507275443736212818737 12674630456582802159614053)
          ·
            refine ⟨2376493210609275404927635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12674630456582802159614053 2376493210609275404927635)
            ·
              refine ⟨3564739815913913107391453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376493210609275404927635 3564739815913913107391453)
              ·
                refine ⟨1336777430967717415271795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3564739815913913107391453 1336777430967717415271795)
                ·
                  refine ⟨2005166146451576122907693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336777430967717415271795 2005166146451576122907693)
                  ·
                    refine ⟨751937304919341046090385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005166146451576122907693 751937304919341046090385)
                    ·
                      rfl

theorem cell22_2196589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2196589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196589 prefixEnd_2196589 := by exact prefixLift 2196589
  have htrace : WordTrace (prefixWord ++ tailWord_2196589) baseStart_2196589 baseEnd_2196589 := by
    simpa [prefixWord, tailWord_2196589, baseEnd_2196589] using wordTrace_append hprefix tailTrace_2196589
  have hstable : (prefixWord ++ tailWord_2196589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196589).length < 2 ^ (prefixWord ++ tailWord_2196589).sum := by decide
  have hdescent : baseEnd_2196589 < baseStart_2196589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196632 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 1, 4]
def baseStart_2196632 : Nat := 118140960795 + 2196632 * 2 ^ 59
def prefixEnd_2196632 : Nat := 4983230072969 + 3 ^ 40 * 2196632 * 2
def baseEnd_2196632 : Nat := 751952024698103267265253

theorem tailTrace_2196632 : CollatzResearch.WordTrace tailWord_2196632 prefixEnd_2196632 751952024698103267265253 := by
  unfold tailWord_2196632
  simp only [CollatzResearch.WordTrace]
  refine ⟨40058875488992446861552075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53411833985323262482069433 40058875488992446861552075)
  ·
    refine ⟨60088313233488670292328113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40058875488992446861552075 60088313233488670292328113)
    ·
      refine ⟨45066234925116502719246085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60088313233488670292328113 45066234925116502719246085)
      ·
        refine ⟨8449919048459344259858641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45066234925116502719246085 8449919048459344259858641)
        ·
          refine ⟨6337439286344508194893981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8449919048459344259858641 6337439286344508194893981)
          ·
            refine ⟨2376539732379190573085243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6337439286344508194893981 2376539732379190573085243)
            ·
              refine ⟨3564809598568785859627865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376539732379190573085243 3564809598568785859627865)
              ·
                refine ⟨2673607198926589394720899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564809598568785859627865 2673607198926589394720899)
                ·
                  refine ⟨4010410798389884092081349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673607198926589394720899 4010410798389884092081349)
                  ·
                    refine ⟨751952024698103267265253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4010410798389884092081349 751952024698103267265253)
                    ·
                      rfl

theorem cell22_2196632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_2196632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196632 prefixEnd_2196632 := by exact prefixLift 2196632
  have htrace : WordTrace (prefixWord ++ tailWord_2196632) baseStart_2196632 baseEnd_2196632 := by
    simpa [prefixWord, tailWord_2196632, baseEnd_2196632] using wordTrace_append hprefix tailTrace_2196632
  have hstable : (prefixWord ++ tailWord_2196632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196632).length < 2 ^ (prefixWord ++ tailWord_2196632).sum := by decide
  have hdescent : baseEnd_2196632 < baseStart_2196632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196737 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 5]
def baseStart_2196737 : Nat := 118140960795 + 2196737 * 2 ^ 59
def prefixEnd_2196737 : Nat := 4983230072969 + 3 ^ 40 * 2196737 * 2
def baseEnd_2196737 : Nat := 250662656114639331129977

theorem tailTrace_2196737 : CollatzResearch.WordTrace tailWord_2196737 prefixEnd_2196737 250662656114639331129977 := by
  unfold tailWord_2196737
  simp only [CollatzResearch.WordTrace]
  refine ⟨80121580642604496655676465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53414387095069664437117643 80121580642604496655676465)
  ·
    refine ⟨60091185481953372491757349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80121580642604496655676465 60091185481953372491757349)
    ·
      refine ⟨11267097277866257342204503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60091185481953372491757349 11267097277866257342204503)
      ·
        refine ⟨16900645916799386013306755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11267097277866257342204503 16900645916799386013306755)
        ·
          refine ⟨25350968875199079019960133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16900645916799386013306755 25350968875199079019960133)
          ·
            refine ⟨4753306664099827316242525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25350968875199079019960133 4753306664099827316242525)
            ·
              refine ⟨1782489999037435243590947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4753306664099827316242525 1782489999037435243590947)
              ·
                refine ⟨2673734998556152865386421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782489999037435243590947 2673734998556152865386421)
                ·
                  refine ⟨250662656114639331129977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2673734998556152865386421 250662656114639331129977)
                  ·
                    rfl

theorem cell22_2196737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_2196737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196737 prefixEnd_2196737 := by exact prefixLift 2196737
  have htrace : WordTrace (prefixWord ++ tailWord_2196737) baseStart_2196737 baseEnd_2196737 := by
    simpa [prefixWord, tailWord_2196737, baseEnd_2196737] using wordTrace_append hprefix tailTrace_2196737
  have hstable : (prefixWord ++ tailWord_2196737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196737).length < 2 ^ (prefixWord ++ tailWord_2196737).sum := by decide
  have hdescent : baseEnd_2196737 < baseStart_2196737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196763 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 3, 5]
def baseStart_2196763 : Nat := 118140960795 + 2196763 * 2 ^ 59
def prefixEnd_2196763 : Nat := 4983230072969 + 3 ^ 40 * 2196763 * 2
def baseEnd_2196763 : Nat := 751996868675262592239851

theorem tailTrace_2196763 : CollatzResearch.WordTrace tailWord_2196763 prefixEnd_2196763 751996868675262592239851 := by
  unfold tailWord_2196763
  simp only [CollatzResearch.WordTrace]
  refine ⟨80122528940510303096122943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53415019293673535397415295 80122528940510303096122943)
  ·
    refine ⟨120183793410765454644184415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80122528940510303096122943 120183793410765454644184415)
    ·
      refine ⟨180275690116148181966276623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120183793410765454644184415 180275690116148181966276623)
      ·
        refine ⟨270413535174222272949414935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180275690116148181966276623 270413535174222272949414935)
        ·
          refine ⟨405620302761333409424122403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270413535174222272949414935 405620302761333409424122403)
          ·
            refine ⟨608430454142000114136183605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405620302761333409424122403 608430454142000114136183605)
            ·
              refine ⟨57040355075812510700267213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 608430454142000114136183605 57040355075812510700267213)
              ·
                refine ⟨21390133153429691512600205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57040355075812510700267213 21390133153429691512600205)
                ·
                  refine ⟨8021299932536134317225077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21390133153429691512600205 8021299932536134317225077)
                  ·
                    refine ⟨751996868675262592239851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8021299932536134317225077 751996868675262592239851)
                    ·
                      rfl

theorem cell22_2196763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_2196763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196763 prefixEnd_2196763 := by exact prefixLift 2196763
  have htrace : WordTrace (prefixWord ++ tailWord_2196763) baseStart_2196763 baseEnd_2196763 := by
    simpa [prefixWord, tailWord_2196763, baseEnd_2196763] using wordTrace_append hprefix tailTrace_2196763
  have hstable : (prefixWord ++ tailWord_2196763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196763).length < 2 ^ (prefixWord ++ tailWord_2196763).sum := by decide
  have hdescent : baseEnd_2196763 < baseStart_2196763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196812 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_2196812 : Nat := 118140960795 + 2196812 * 2 ^ 59
def prefixEnd_2196812 : Nat := 4983230072969 + 3 ^ 40 * 2196812 * 2
def baseEnd_2196812 : Nat := 752013642376642797764701

theorem tailTrace_2196812 : CollatzResearch.WordTrace tailWord_2196812 prefixEnd_2196812 752013642376642797764701 := by
  unfold tailWord_2196812
  simp only [CollatzResearch.WordTrace]
  refine ⟨40062158058666392232328345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53416210744888522976437793 40062158058666392232328345)
  ·
    refine ⟨30046618543999794174246259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40062158058666392232328345 30046618543999794174246259)
    ·
      refine ⟨45069927815999691261369389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30046618543999794174246259 45069927815999691261369389)
      ·
        refine ⟨16901222930999884223013521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45069927815999691261369389 16901222930999884223013521)
        ·
          refine ⟨12675917198249913167260141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16901222930999884223013521 12675917198249913167260141)
          ·
            refine ⟨4753468949343717437722553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12675917198249913167260141 4753468949343717437722553)
            ·
              refine ⟨3565101712007788078291915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4753468949343717437722553 3565101712007788078291915)
              ·
                refine ⟨5347652568011682117437873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565101712007788078291915 5347652568011682117437873)
                ·
                  refine ⟨4010739426008761588078405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5347652568011682117437873 4010739426008761588078405)
                  ·
                    refine ⟨752013642376642797764701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4010739426008761588078405 752013642376642797764701)
                    ·
                      rfl

theorem cell22_2196812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_2196812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196812 prefixEnd_2196812 := by exact prefixLift 2196812
  have htrace : WordTrace (prefixWord ++ tailWord_2196812) baseStart_2196812 baseEnd_2196812 := by
    simpa [prefixWord, tailWord_2196812, baseEnd_2196812] using wordTrace_append hprefix tailTrace_2196812
  have hstable : (prefixWord ++ tailWord_2196812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196812).length < 2 ^ (prefixWord ++ tailWord_2196812).sum := by decide
  have hdescent : baseEnd_2196812 < baseStart_2196812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196855 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 5]
def baseStart_2196855 : Nat := 118140960795 + 2196855 * 2 ^ 59
def prefixEnd_2196855 : Nat := 4983230072969 + 3 ^ 40 * 2196855 * 2
def baseEnd_2196855 : Nat := 250676120718468339646523

theorem tailTrace_2196855 : CollatzResearch.WordTrace tailWord_2196855 prefixEnd_2196855 250676120718468339646523 := by
  unfold tailWord_2196855
  simp only [CollatzResearch.WordTrace]
  refine ⟨80125884456177002808472019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53417256304118001872314679 80125884456177002808472019)
  ·
    refine ⟨120188826684265504212708029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80125884456177002808472019 120188826684265504212708029)
    ·
      refine ⟨45070810006599564079765511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120188826684265504212708029 45070810006599564079765511)
      ·
        refine ⟨67606215009899346119648267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45070810006599564079765511 67606215009899346119648267)
        ·
          refine ⟨101409322514849019179472401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67606215009899346119648267 101409322514849019179472401)
          ·
            refine ⟨76056991886136764384604301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101409322514849019179472401 76056991886136764384604301)
            ·
              refine ⟨28521371957301286644226613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76056991886136764384604301 28521371957301286644226613)
              ·
                refine ⟨2673878620996995622896245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28521371957301286644226613 2673878620996995622896245)
                ·
                  refine ⟨250676120718468339646523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2673878620996995622896245 250676120718468339646523)
                  ·
                    rfl

theorem cell22_2196855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 5].length) (baseStart_2196855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196855 prefixEnd_2196855 := by exact prefixLift 2196855
  have htrace : WordTrace (prefixWord ++ tailWord_2196855) baseStart_2196855 baseEnd_2196855 := by
    simpa [prefixWord, tailWord_2196855, baseEnd_2196855] using wordTrace_append hprefix tailTrace_2196855
  have hstable : (prefixWord ++ tailWord_2196855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196855).length < 2 ^ (prefixWord ++ tailWord_2196855).sum := by decide
  have hdescent : baseEnd_2196855 < baseStart_2196855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196917 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 6]
def baseStart_2196917 : Nat := 118140960795 + 2196917 * 2 ^ 59
def prefixEnd_2196917 : Nat := 4983230072969 + 3 ^ 40 * 2196917 * 2
def baseEnd_2196917 : Nat := 250683195340819174629793

theorem tailTrace_2196917 : CollatzResearch.WordTrace tailWord_2196917 prefixEnd_2196917 250683195340819174629793 := by
  unfold tailWord_2196917
  simp only [CollatzResearch.WordTrace]
  refine ⟨80128145781952387397229005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53418763854634924931486003 80128145781952387397229005)
  ·
    refine ⟨30048054668232145273960877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80128145781952387397229005 30048054668232145273960877)
    ·
      refine ⟨11268020500587054477735329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30048054668232145273960877 11268020500587054477735329)
      ·
        refine ⟨8451015375440290858301497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11268020500587054477735329 8451015375440290858301497)
        ·
          refine ⟨6338261531580218143726123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8451015375440290858301497 6338261531580218143726123)
          ·
            refine ⟨9507392297370327215589185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6338261531580218143726123 9507392297370327215589185)
            ·
              refine ⟨7130544223027745411691889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9507392297370327215589185 7130544223027745411691889)
              ·
                refine ⟨5347908167270809058768917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7130544223027745411691889 5347908167270809058768917)
                ·
                  refine ⟨250683195340819174629793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5347908167270809058768917 250683195340819174629793)
                  ·
                    rfl

theorem cell22_2196917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_2196917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196917 prefixEnd_2196917 := by exact prefixLift 2196917
  have htrace : WordTrace (prefixWord ++ tailWord_2196917) baseStart_2196917 baseEnd_2196917 := by
    simpa [prefixWord, tailWord_2196917, baseEnd_2196917] using wordTrace_append hprefix tailTrace_2196917
  have hstable : (prefixWord ++ tailWord_2196917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196917).length < 2 ^ (prefixWord ++ tailWord_2196917).sum := by decide
  have hdescent : baseEnd_2196917 < baseStart_2196917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196949 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_2196949 : Nat := 118140960795 + 2196949 * 2 ^ 59
def prefixEnd_2196949 : Nat := 4983230072969 + 3 ^ 40 * 2196949 * 2
def baseEnd_2196949 : Nat := 752060540276420107089281

theorem tailTrace_2196949 : CollatzResearch.WordTrace tailWord_2196949 prefixEnd_2196949 752060540276420107089281 := by
  unfold tailWord_2196949
  simp only [CollatzResearch.WordTrace]
  refine ⟨80129312917836456862393901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53419541945224304574929267 80129312917836456862393901)
  ·
    refine ⟨30048492344188671323397713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80129312917836456862393901 30048492344188671323397713)
    ·
      refine ⟨22536369258141503492548285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30048492344188671323397713 22536369258141503492548285)
      ·
        refine ⟨8451138471803063809705607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22536369258141503492548285 8451138471803063809705607)
        ·
          refine ⟨12676707707704595714558411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8451138471803063809705607 12676707707704595714558411)
          ·
            refine ⟨19015061561556893571837617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12676707707704595714558411 19015061561556893571837617)
            ·
              refine ⟨14261296171167670178878213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19015061561556893571837617 14261296171167670178878213)
              ·
                refine ⟨2673993032093938158539665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14261296171167670178878213 2673993032093938158539665)
                ·
                  refine ⟨2005494774070453618904749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2673993032093938158539665 2005494774070453618904749)
                  ·
                    refine ⟨752060540276420107089281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005494774070453618904749 752060540276420107089281)
                    ·
                      rfl

theorem cell22_2196949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_2196949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196949 prefixEnd_2196949 := by exact prefixLift 2196949
  have htrace : WordTrace (prefixWord ++ tailWord_2196949) baseStart_2196949 baseEnd_2196949 := by
    simpa [prefixWord, tailWord_2196949, baseEnd_2196949] using wordTrace_append hprefix tailTrace_2196949
  have hstable : (prefixWord ++ tailWord_2196949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196949).length < 2 ^ (prefixWord ++ tailWord_2196949).sum := by decide
  have hdescent : baseEnd_2196949 < baseStart_2196949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196960 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_2196960 : Nat := 118140960795 + 2196960 * 2 ^ 59
def prefixEnd_2196960 : Nat := 4983230072969 + 3 ^ 40 * 2196960 * 2
def baseEnd_2196960 : Nat := 752064305801219745064247

theorem tailTrace_2196960 : CollatzResearch.WordTrace tailWord_2196960 prefixEnd_2196960 752064305801219745064247 := by
  unfold tailWord_2196960
  simp only [CollatzResearch.WordTrace]
  refine ⟨40064857060398302870522167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53419809413864403827362889 40064857060398302870522167)
  ·
    refine ⟨60097285590597454305783251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40064857060398302870522167 60097285590597454305783251)
    ·
      refine ⟨90145928385896181458674877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60097285590597454305783251 90145928385896181458674877)
      ·
        refine ⟨33804723144711068047003079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90145928385896181458674877 33804723144711068047003079)
        ·
          refine ⟨50707084717066602070504619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33804723144711068047003079 50707084717066602070504619)
          ·
            refine ⟨76060627075599903105756929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50707084717066602070504619 76060627075599903105756929)
            ·
              refine ⟨57045470306699927329317697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76060627075599903105756929 57045470306699927329317697)
              ·
                refine ⟨42784102730024945496988273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57045470306699927329317697 42784102730024945496988273)
                ·
                  refine ⟨32088077047518709122741205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42784102730024945496988273 32088077047518709122741205)
                  ·
                    refine ⟨752064305801219745064247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32088077047518709122741205 752064305801219745064247)
                    ·
                      rfl

theorem cell22_2196960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_2196960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196960 prefixEnd_2196960 := by exact prefixLift 2196960
  have htrace : WordTrace (prefixWord ++ tailWord_2196960) baseStart_2196960 baseEnd_2196960 := by
    simpa [prefixWord, tailWord_2196960, baseEnd_2196960] using wordTrace_append hprefix tailTrace_2196960
  have hstable : (prefixWord ++ tailWord_2196960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196960).length < 2 ^ (prefixWord ++ tailWord_2196960).sum := by decide
  have hdescent : baseEnd_2196960 < baseStart_2196960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196981 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2196981 : Nat := 118140960795 + 2196981 * 2 ^ 59
def prefixEnd_2196981 : Nat := 4983230072969 + 3 ^ 40 * 2196981 * 2
def baseEnd_2196981 : Nat := 752071494530382690289183

theorem tailTrace_2196981 : CollatzResearch.WordTrace tailWord_2196981 prefixEnd_2196981 752071494530382690289183 := by
  unfold tailWord_2196981
  simp only [CollatzResearch.WordTrace]
  refine ⟨80130480053720526327558797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53420320035813684218372531 80130480053720526327558797)
  ·
    refine ⟨30048930020145197372834549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80130480053720526327558797 30048930020145197372834549)
    ·
      refine ⟨2817087189388612253703239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30048930020145197372834549 2817087189388612253703239)
      ·
        refine ⟨4225630784082918380554859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2817087189388612253703239 4225630784082918380554859)
        ·
          refine ⟨6338446176124377570832289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4225630784082918380554859 6338446176124377570832289)
          ·
            refine ⟨4753834632093283178124217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6338446176124377570832289 4753834632093283178124217)
            ·
              refine ⟨3565375974069962383593163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4753834632093283178124217 3565375974069962383593163)
              ·
                refine ⟨5348063961104943575389745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565375974069962383593163 5348063961104943575389745)
                ·
                  refine ⟨4011047970828707681542309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5348063961104943575389745 4011047970828707681542309)
                  ·
                    refine ⟨752071494530382690289183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4011047970828707681542309 752071494530382690289183)
                    ·
                      rfl

theorem cell22_2196981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2196981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2196981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2196981 prefixEnd_2196981 := by exact prefixLift 2196981
  have htrace : WordTrace (prefixWord ++ tailWord_2196981) baseStart_2196981 baseEnd_2196981 := by
    simpa [prefixWord, tailWord_2196981, baseEnd_2196981] using wordTrace_append hprefix tailTrace_2196981
  have hstable : (prefixWord ++ tailWord_2196981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196981).length < 2 ^ (prefixWord ++ tailWord_2196981).sum := by decide
  have hdescent : baseEnd_2196981 < baseStart_2196981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197011 : List Nat := [1, 1, 1, 2, 1, 7, 1, 4, 1, 3]
def baseStart_2197011 : Nat := 118140960795 + 2197011 * 2 ^ 59
def prefixEnd_2197011 : Nat := 4983230072969 + 3 ^ 40 * 2197011 * 2
def baseEnd_2197011 : Nat := 752081764143472612039091

theorem tailTrace_2197011 : CollatzResearch.WordTrace tailWord_2197011 prefixEnd_2197011 752081764143472612039091 := by
  unfold tailWord_2197011
  simp only [CollatzResearch.WordTrace]
  refine ⟨80131574243611841451150887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53421049495741227634100591 80131574243611841451150887)
  ·
    refine ⟨120197361365417762176726331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80131574243611841451150887 120197361365417762176726331)
    ·
      refine ⟨180296042048126643265089497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120197361365417762176726331 180296042048126643265089497)
      ·
        refine ⟨135222031536094982448817123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180296042048126643265089497 135222031536094982448817123)
        ·
          refine ⟨202833047304142473673225685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135222031536094982448817123 202833047304142473673225685)
          ·
            refine ⟨4753899546190839226716227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 202833047304142473673225685 4753899546190839226716227)
            ·
              refine ⟨7130849319286258840074341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753899546190839226716227 7130849319286258840074341)
              ·
                refine ⟨1337034247366173532513939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7130849319286258840074341 1337034247366173532513939)
                ·
                  refine ⟨2005551371049260298770909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337034247366173532513939 2005551371049260298770909)
                  ·
                    refine ⟨752081764143472612039091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005551371049260298770909 752081764143472612039091)
                    ·
                      rfl

theorem cell22_2197011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 3].length) (baseStart_2197011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197011 prefixEnd_2197011 := by exact prefixLift 2197011
  have htrace : WordTrace (prefixWord ++ tailWord_2197011) baseStart_2197011 baseEnd_2197011 := by
    simpa [prefixWord, tailWord_2197011, baseEnd_2197011] using wordTrace_append hprefix tailTrace_2197011
  have hstable : (prefixWord ++ tailWord_2197011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197011).length < 2 ^ (prefixWord ++ tailWord_2197011).sum := by decide
  have hdescent : baseEnd_2197011 < baseStart_2197011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197024 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 5]
def baseStart_2197024 : Nat := 118140960795 + 2197024 * 2 ^ 59
def prefixEnd_2197024 : Nat := 4983230072969 + 3 ^ 40 * 2197024 * 2
def baseEnd_2197024 : Nat := 250695404769714970488017

theorem tailTrace_2197024 : CollatzResearch.WordTrace tailWord_2197024 prefixEnd_2197024 250695404769714970488017 := by
  unfold tailWord_2197024
  simp only [CollatzResearch.WordTrace]
  refine ⟨40066024196282372335687063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53421365595043163114249417 40066024196282372335687063)
  ·
    refine ⟨60099036294423558503530595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40066024196282372335687063 60099036294423558503530595)
    ·
      refine ⟨90148554441635337755295893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60099036294423558503530595 90148554441635337755295893)
      ·
        refine ⟨4225713489451656457279495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90148554441635337755295893 4225713489451656457279495)
        ·
          refine ⟨6338570234177484685919243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4225713489451656457279495 6338570234177484685919243)
          ·
            refine ⟨9507855351266227028878865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6338570234177484685919243 9507855351266227028878865)
            ·
              refine ⟨7130891513449670271659149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9507855351266227028878865 7130891513449670271659149)
              ·
                refine ⟨2674084317543626351872181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7130891513449670271659149 2674084317543626351872181)
                ·
                  refine ⟨250695404769714970488017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2674084317543626351872181 250695404769714970488017)
                  ·
                    rfl

theorem cell22_2197024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_2197024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197024 prefixEnd_2197024 := by exact prefixLift 2197024
  have htrace : WordTrace (prefixWord ++ tailWord_2197024) baseStart_2197024 baseEnd_2197024 := by
    simpa [prefixWord, tailWord_2197024, baseEnd_2197024] using wordTrace_append hprefix tailTrace_2197024
  have hstable : (prefixWord ++ tailWord_2197024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197024).length < 2 ^ (prefixWord ++ tailWord_2197024).sum := by decide
  have hdescent : baseEnd_2197024 < baseStart_2197024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197180 : List Nat := [2, 2, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_2197180 : Nat := 118140960795 + 2197180 * 2 ^ 59
def prefixEnd_2197180 : Nat := 4983230072969 + 3 ^ 40 * 2197180 * 2
def baseEnd_2197180 : Nat := 752139616297212504563573

theorem tailTrace_2197180 : CollatzResearch.WordTrace tailWord_2197180 prefixEnd_2197180 752139616297212504563573 := by
  unfold tailWord_2197180
  simp only [CollatzResearch.WordTrace]
  refine ⟨40068869089999791657026497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53425158786666388876035329 40068869089999791657026497)
  ·
    refine ⟨30051651817499843742769873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40068869089999791657026497 30051651817499843742769873)
    ·
      refine ⟨22538738863124882807077405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30051651817499843742769873 22538738863124882807077405)
      ·
        refine ⟨8452027073671831052654027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22538738863124882807077405 8452027073671831052654027)
        ·
          refine ⟨12678040610507746578981041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8452027073671831052654027 12678040610507746578981041)
          ·
            refine ⟨9508530457880809934235781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12678040610507746578981041 9508530457880809934235781)
            ·
              refine ⟨1782849460852651862669209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9508530457880809934235781 1782849460852651862669209)
              ·
                refine ⟨1337137095639488897001907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782849460852651862669209 1337137095639488897001907)
                ·
                  refine ⟨2005705643459233345502861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337137095639488897001907 2005705643459233345502861)
                  ·
                    refine ⟨752139616297212504563573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005705643459233345502861 752139616297212504563573)
                    ·
                      rfl

theorem cell22_2197180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_2197180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197180 prefixEnd_2197180 := by exact prefixLift 2197180
  have htrace : WordTrace (prefixWord ++ tailWord_2197180) baseStart_2197180 baseEnd_2197180 := by
    simpa [prefixWord, tailWord_2197180, baseEnd_2197180] using wordTrace_append hprefix tailTrace_2197180
  have hstable : (prefixWord ++ tailWord_2197180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197180).length < 2 ^ (prefixWord ++ tailWord_2197180).sum := by decide
  have hdescent : baseEnd_2197180 < baseStart_2197180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197187 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 12]
def baseStart_2197187 : Nat := 118140960795 + 2197187 * 2 ^ 59
def prefixEnd_2197187 : Nat := 4983230072969 + 3 ^ 40 * 2197187 * 2
def baseEnd_2197187 : Nat := 250714004180088939879517

theorem tailTrace_2197187 : CollatzResearch.WordTrace tailWord_2197187 prefixEnd_2197187 250714004180088939879517 := by
  unfold tailWord_2197187
  simp only [CollatzResearch.WordTrace]
  refine ⟨80137993490974223509557815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53425328993982815673038543 80137993490974223509557815)
  ·
    refine ⟨120206990236461335264336723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80137993490974223509557815 120206990236461335264336723)
    ·
      refine ⟨180310485354692002896505085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120206990236461335264336723 180310485354692002896505085)
      ·
        refine ⟨67616432008009501086189407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180310485354692002896505085 67616432008009501086189407)
        ·
          refine ⟨101424648012014251629284111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67616432008009501086189407 101424648012014251629284111)
          ·
            refine ⟨152136972018021377443926167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101424648012014251629284111 152136972018021377443926167)
            ·
              refine ⟨228205458027032066165889251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152136972018021377443926167 228205458027032066165889251)
              ·
                refine ⟨342308187040548099248833877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228205458027032066165889251 342308187040548099248833877)
                ·
                  refine ⟨250714004180088939879517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 342308187040548099248833877 250714004180088939879517)
                  ·
                    rfl

theorem cell22_2197187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 12].length) (baseStart_2197187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197187 prefixEnd_2197187 := by exact prefixLift 2197187
  have htrace : WordTrace (prefixWord ++ tailWord_2197187) baseStart_2197187 baseEnd_2197187 := by
    simpa [prefixWord, tailWord_2197187, baseEnd_2197187] using wordTrace_append hprefix tailTrace_2197187
  have hstable : (prefixWord ++ tailWord_2197187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197187).length < 2 ^ (prefixWord ++ tailWord_2197187).sum := by decide
  have hdescent : baseEnd_2197187 < baseStart_2197187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197238 : List Nat := [5, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_2197238 : Nat := 118140960795 + 2197238 * 2 ^ 59
def prefixEnd_2197238 : Nat := 4983230072969 + 3 ^ 40 * 2197238 * 2
def baseEnd_2197238 : Nat := 250719823627506562204465

theorem tailTrace_2197238 : CollatzResearch.WordTrace tailWord_2197238 prefixEnd_2197238 250719823627506562204465 := by
  unfold tailWord_2197238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008740850861841201229023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53426569075859639479776245 5008740850861841201229023)
  ·
    refine ⟨7513111276292761801843535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5008740850861841201229023 7513111276292761801843535)
    ·
      refine ⟨11269666914439142702765303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7513111276292761801843535 11269666914439142702765303)
      ·
        refine ⟨16904500371658714054147955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11269666914439142702765303 16904500371658714054147955)
        ·
          refine ⟨25356750557488071081221933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16904500371658714054147955 25356750557488071081221933)
          ·
            refine ⟨9508781459058026655458225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25356750557488071081221933 9508781459058026655458225)
            ·
              refine ⟨7131586094293519991593669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9508781459058026655458225 7131586094293519991593669)
              ·
                refine ⟨1337172392680034998423813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7131586094293519991593669 1337172392680034998423813)
                ·
                  refine ⟨250719823627506562204465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1337172392680034998423813 250719823627506562204465)
                  ·
                    rfl

theorem cell22_2197238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_2197238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197238 prefixEnd_2197238 := by exact prefixLift 2197238
  have htrace : WordTrace (prefixWord ++ tailWord_2197238) baseStart_2197238 baseEnd_2197238 := by
    simpa [prefixWord, tailWord_2197238, baseEnd_2197238] using wordTrace_append hprefix tailTrace_2197238
  have hstable : (prefixWord ++ tailWord_2197238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197238).length < 2 ^ (prefixWord ++ tailWord_2197238).sum := by decide
  have hdescent : baseEnd_2197238 < baseStart_2197238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197298 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_2197298 : Nat := 118140960795 + 2197298 * 2 ^ 59
def prefixEnd_2197298 : Nat := 4983230072969 + 3 ^ 40 * 2197298 * 2
def baseEnd_2197298 : Nat := 752180010108699530113211

theorem tailTrace_2197298 : CollatzResearch.WordTrace tailWord_2197298 prefixEnd_2197298 752180010108699530113211 := by
  unfold tailWord_2197298
  simp only [CollatzResearch.WordTrace]
  refine ⟨20035510498393022366712137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53428027995714726311232365 20035510498393022366712137)
  ·
    refine ⟨15026632873794766775034103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20035510498393022366712137 15026632873794766775034103)
    ·
      refine ⟨22539949310692150162551155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15026632873794766775034103 22539949310692150162551155)
      ·
        refine ⟨33809923966038225243826733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22539949310692150162551155 33809923966038225243826733)
        ·
          refine ⟨12678721487264334466435025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33809923966038225243826733 12678721487264334466435025)
          ·
            refine ⟨9509041115448250849826269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12678721487264334466435025 9509041115448250849826269)
            ·
              refine ⟨3565890418293094068684851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9509041115448250849826269 3565890418293094068684851)
              ·
                refine ⟨5348835627439641103027277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565890418293094068684851 5348835627439641103027277)
                ·
                  refine ⟨2005813360289865413635229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5348835627439641103027277 2005813360289865413635229)
                  ·
                    refine ⟨752180010108699530113211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005813360289865413635229 752180010108699530113211)
                    ·
                      rfl

theorem cell22_2197298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_2197298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197298 prefixEnd_2197298 := by exact prefixLift 2197298
  have htrace : WordTrace (prefixWord ++ tailWord_2197298) baseStart_2197298 baseEnd_2197298 := by
    simpa [prefixWord, tailWord_2197298, baseEnd_2197298] using wordTrace_append hprefix tailTrace_2197298
  have hstable : (prefixWord ++ tailWord_2197298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197298).length < 2 ^ (prefixWord ++ tailWord_2197298).sum := by decide
  have hdescent : baseEnd_2197298 < baseStart_2197298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197358 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2197358 : Nat := 118140960795 + 2197358 * 2 ^ 59
def prefixEnd_2197358 : Nat := 4983230072969 + 3 ^ 40 * 2197358 * 2
def baseEnd_2197358 : Nat := 752200549334879373613027

theorem tailTrace_2197358 : CollatzResearch.WordTrace tailWord_2197358 prefixEnd_2197358 752200549334879373613027 := by
  unfold tailWord_2197358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10018028796669339964254091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53429486915569813142688485 10018028796669339964254091)
  ·
    refine ⟨15027043195004009946381137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10018028796669339964254091 15027043195004009946381137)
    ·
      refine ⟨11270282396253007459785853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15027043195004009946381137 11270282396253007459785853)
      ·
        refine ⟨4226355898594877797419695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11270282396253007459785853 4226355898594877797419695)
        ·
          refine ⟨6339533847892316696129543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4226355898594877797419695 6339533847892316696129543)
          ·
            refine ⟨9509300771838475044194315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6339533847892316696129543 9509300771838475044194315)
            ·
              refine ⟨14263951157757712566291473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9509300771838475044194315 14263951157757712566291473)
              ·
                refine ⟨10697963368318284424718605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14263951157757712566291473 10697963368318284424718605)
                ·
                  refine ⟨4011736263119356659269477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10697963368318284424718605 4011736263119356659269477)
                  ·
                    refine ⟨752200549334879373613027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4011736263119356659269477 752200549334879373613027)
                    ·
                      rfl

theorem cell22_2197358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2197358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197358 prefixEnd_2197358 := by exact prefixLift 2197358
  have htrace : WordTrace (prefixWord ++ tailWord_2197358) baseStart_2197358 baseEnd_2197358 := by
    simpa [prefixWord, tailWord_2197358, baseEnd_2197358] using wordTrace_append hprefix tailTrace_2197358
  have hstable : (prefixWord ++ tailWord_2197358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197358).length < 2 ^ (prefixWord ++ tailWord_2197358).sum := by decide
  have hdescent : baseEnd_2197358 < baseStart_2197358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197371 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 6, 3]
def baseStart_2197371 : Nat := 118140960795 + 2197371 * 2 ^ 59
def prefixEnd_2197371 : Nat := 4983230072969 + 3 ^ 40 * 2197371 * 2
def baseEnd_2197371 : Nat := 752204999500551673037987

theorem tailTrace_2197371 : CollatzResearch.WordTrace tailWord_2197371 prefixEnd_2197371 752204999500551673037987 := by
  unfold tailWord_2197371
  simp only [CollatzResearch.WordTrace]
  refine ⟨80144704522307622934255967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53429803014871748622837311 80144704522307622934255967)
  ·
    refine ⟨120217056783461434401383951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80144704522307622934255967 120217056783461434401383951)
    ·
      refine ⟨180325585175192151602075927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120217056783461434401383951 180325585175192151602075927)
      ·
        refine ⟨270488377762788227403113891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180325585175192151602075927 270488377762788227403113891)
        ·
          refine ⟨405732566644182341104670837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270488377762788227403113891 405732566644182341104670837)
          ·
            refine ⟨38037428122892094478562891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 405732566644182341104670837 38037428122892094478562891)
            ·
              refine ⟨57056142184338141717844337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38037428122892094478562891 57056142184338141717844337)
              ·
                refine ⟨42792106638253606288383253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57056142184338141717844337 42792106638253606288383253)
                ·
                  refine ⟨2005879998668137794767965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42792106638253606288383253 2005879998668137794767965)
                  ·
                    refine ⟨752204999500551673037987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005879998668137794767965 752204999500551673037987)
                    ·
                      rfl

theorem cell22_2197371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 3].length) (baseStart_2197371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197371 prefixEnd_2197371 := by exact prefixLift 2197371
  have htrace : WordTrace (prefixWord ++ tailWord_2197371) baseStart_2197371 baseEnd_2197371 := by
    simpa [prefixWord, tailWord_2197371, baseEnd_2197371] using wordTrace_append hprefix tailTrace_2197371
  have hstable : (prefixWord ++ tailWord_2197371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197371).length < 2 ^ (prefixWord ++ tailWord_2197371).sum := by decide
  have hdescent : baseEnd_2197371 < baseStart_2197371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197405 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_2197405 : Nat := 118140960795 + 2197405 * 2 ^ 59
def prefixEnd_2197405 : Nat := 4983230072969 + 3 ^ 40 * 2197405 * 2
def baseEnd_2197405 : Nat := 752216638395386917687883

theorem tailTrace_2197405 : CollatzResearch.WordTrace tailWord_2197405 prefixEnd_2197405 752216638395386917687883 := by
  unfold tailWord_2197405
  simp only [CollatzResearch.WordTrace]
  refine ⟨80145944604184446740993669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53430629736122964493995779 80145944604184446740993669)
  ·
    refine ⟨15027364613284583763936313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80145944604184446740993669 15027364613284583763936313)
    ·
      refine ⟨11270523459963437822952235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15027364613284583763936313 11270523459963437822952235)
      ·
        refine ⟨16905785189945156734428353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11270523459963437822952235 16905785189945156734428353)
        ·
          refine ⟨12679338892458867550821265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16905785189945156734428353 12679338892458867550821265)
          ·
            refine ⟨9509504169344150663115949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12679338892458867550821265 9509504169344150663115949)
            ·
              refine ⟨3566064063504056498668481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9509504169344150663115949 3566064063504056498668481)
              ·
                refine ⟨2674548047628042374001361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566064063504056498668481 2674548047628042374001361)
                ·
                  refine ⟨2005911035721031780501021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2674548047628042374001361 2005911035721031780501021)
                  ·
                    refine ⟨752216638395386917687883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005911035721031780501021 752216638395386917687883)
                    ·
                      rfl

theorem cell22_2197405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_2197405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197405 prefixEnd_2197405 := by exact prefixLift 2197405
  have htrace : WordTrace (prefixWord ++ tailWord_2197405) baseStart_2197405 baseEnd_2197405 := by
    simpa [prefixWord, tailWord_2197405, baseEnd_2197405] using wordTrace_append hprefix tailTrace_2197405
  have hstable : (prefixWord ++ tailWord_2197405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197405).length < 2 ^ (prefixWord ++ tailWord_2197405).sum := by decide
  have hdescent : baseEnd_2197405 < baseStart_2197405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197433 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 3, 3]
def baseStart_2197433 : Nat := 118140960795 + 2197433 * 2 ^ 59
def prefixEnd_2197433 : Nat := 4983230072969 + 3 ^ 40 * 2197433 * 2
def baseEnd_2197433 : Nat := 752226223367604177987797

theorem tailTrace_2197433 : CollatzResearch.WordTrace tailWord_2197433 prefixEnd_2197433 752226223367604177987797 := by
  unfold tailWord_2197433
  simp only [CollatzResearch.WordTrace]
  refine ⟨80146965848083007523012953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53431310565388671682008635 80146965848083007523012953)
  ·
    refine ⟨60110224386062255642259715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80146965848083007523012953 60110224386062255642259715)
    ·
      refine ⟨90165336579093383463389573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60110224386062255642259715 90165336579093383463389573)
      ·
        refine ⟨16906000608580009399385545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90165336579093383463389573 16906000608580009399385545)
        ·
          refine ⟨12679500456435007049539159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16906000608580009399385545 12679500456435007049539159)
          ·
            refine ⟨19019250684652510574308739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12679500456435007049539159 19019250684652510574308739)
            ·
              refine ⟨28528876026978765861463109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19019250684652510574308739 28528876026978765861463109)
              ·
                refine ⟨5349164255058518599024333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28528876026978765861463109 5349164255058518599024333)
                ·
                  refine ⟨2005936595646944474634125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5349164255058518599024333 2005936595646944474634125)
                  ·
                    refine ⟨752226223367604177987797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005936595646944474634125 752226223367604177987797)
                    ·
                      rfl

theorem cell22_2197433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_2197433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197433 prefixEnd_2197433 := by exact prefixLift 2197433
  have htrace : WordTrace (prefixWord ++ tailWord_2197433) baseStart_2197433 baseEnd_2197433 := by
    simpa [prefixWord, tailWord_2197433, baseEnd_2197433] using wordTrace_append hprefix tailTrace_2197433
  have hstable : (prefixWord ++ tailWord_2197433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197433).length < 2 ^ (prefixWord ++ tailWord_2197433).sum := by decide
  have hdescent : baseEnd_2197433 < baseStart_2197433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197491 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 6]
def baseStart_2197491 : Nat := 118140960795 + 2197491 * 2 ^ 59
def prefixEnd_2197491 : Nat := 4983230072969 + 3 ^ 40 * 2197491 * 2
def baseEnd_2197491 : Nat := 250748692650970453345873

theorem tailTrace_2197491 : CollatzResearch.WordTrace tailWord_2197491 prefixEnd_2197491 250748692650970453345873 := by
  unfold tailWord_2197491
  simp only [CollatzResearch.WordTrace]
  refine ⟨80149081281872883428624327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53432720854581922285749551 80149081281872883428624327)
  ·
    refine ⟨120223621922809325142936491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80149081281872883428624327 120223621922809325142936491)
    ·
      refine ⟨180335432884213987714404737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120223621922809325142936491 180335432884213987714404737)
      ·
        refine ⟨135251574663160490785803553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180335432884213987714404737 135251574663160490785803553)
        ·
          refine ⟨101438680997370368089352665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135251574663160490785803553 101438680997370368089352665)
          ·
            refine ⟨76079010748027776067014499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101438680997370368089352665 76079010748027776067014499)
            ·
              refine ⟨114118516122041664100521749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76079010748027776067014499 114118516122041664100521749)
              ·
                refine ⟨5349305443220703004711957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114118516122041664100521749 5349305443220703004711957)
                ·
                  refine ⟨250748692650970453345873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5349305443220703004711957 250748692650970453345873)
                  ·
                    rfl

theorem cell22_2197491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 6].length) (baseStart_2197491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197491 prefixEnd_2197491 := by exact prefixLift 2197491
  have htrace : WordTrace (prefixWord ++ tailWord_2197491) baseStart_2197491 baseEnd_2197491 := by
    simpa [prefixWord, tailWord_2197491, baseEnd_2197491] using wordTrace_append hprefix tailTrace_2197491
  have hstable : (prefixWord ++ tailWord_2197491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197491).length < 2 ^ (prefixWord ++ tailWord_2197491).sum := by decide
  have hdescent : baseEnd_2197491 < baseStart_2197491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197521 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_2197521 : Nat := 118140960795 + 2197521 * 2 ^ 59
def prefixEnd_2197521 : Nat := 4983230072969 + 3 ^ 40 * 2197521 * 2
def baseEnd_2197521 : Nat := 752256347566001281787527

theorem tailTrace_2197521 : CollatzResearch.WordTrace tailWord_2197521 prefixEnd_2197521 752256347566001281787527 := by
  unfold tailWord_2197521
  simp only [CollatzResearch.WordTrace]
  refine ⟨80150175471764198552216417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53433450314509465701477611 80150175471764198552216417)
  ·
    refine ⟨60112631603823148914162313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80150175471764198552216417 60112631603823148914162313)
    ·
      refine ⟨45084473702867361685621735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60112631603823148914162313 45084473702867361685621735)
      ·
        refine ⟨67626710554301042528432603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45084473702867361685621735 67626710554301042528432603)
        ·
          refine ⟨101440065831451563792648905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67626710554301042528432603 101440065831451563792648905)
          ·
            refine ⟨76080049373588672844486679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101440065831451563792648905 76080049373588672844486679)
            ·
              refine ⟨114120074060383009266730019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76080049373588672844486679 114120074060383009266730019)
              ·
                refine ⟨171180111090574513900095029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114120074060383009266730019 171180111090574513900095029)
                ·
                  refine ⟨16048135414741360678133909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 171180111090574513900095029 16048135414741360678133909)
                  ·
                    refine ⟨752256347566001281787527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16048135414741360678133909 752256347566001281787527)
                    ·
                      rfl

theorem cell22_2197521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_2197521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197521 prefixEnd_2197521 := by exact prefixLift 2197521
  have htrace : WordTrace (prefixWord ++ tailWord_2197521) baseStart_2197521 baseEnd_2197521 := by
    simpa [prefixWord, tailWord_2197521, baseEnd_2197521] using wordTrace_append hprefix tailTrace_2197521
  have hstable : (prefixWord ++ tailWord_2197521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197521).length < 2 ^ (prefixWord ++ tailWord_2197521).sum := by decide
  have hdescent : baseEnd_2197521 < baseStart_2197521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197523 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 4, 3]
def baseStart_2197523 : Nat := 118140960795 + 2197523 * 2 ^ 59
def prefixEnd_2197523 : Nat := 4983230072969 + 3 ^ 40 * 2197523 * 2
def baseEnd_2197523 : Nat := 752257032206873943237521

theorem tailTrace_2197523 : CollatzResearch.WordTrace tailWord_2197523 prefixEnd_2197523 752257032206873943237521 := by
  unfold tailWord_2197523
  simp only [CollatzResearch.WordTrace]
  refine ⟨80150248417756952893789223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53433498945171301929192815 80150248417756952893789223)
  ·
    refine ⟨120225372626635429340683835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80150248417756952893789223 120225372626635429340683835)
    ·
      refine ⟨180338058939953144011025753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120225372626635429340683835 180338058939953144011025753)
      ·
        refine ⟨135253544204964858008269315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180338058939953144011025753 135253544204964858008269315)
        ·
          refine ⟨202880316307447287012403973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135253544204964858008269315 202880316307447287012403973)
          ·
            refine ⟨38040059307646366314825745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202880316307447287012403973 38040059307646366314825745)
            ·
              refine ⟨28530044480734774736119309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38040059307646366314825745 28530044480734774736119309)
              ·
                refine ⟨10698766680275540526044741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28530044480734774736119309 10698766680275540526044741)
                ·
                  refine ⟨2006018752551663848633389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10698766680275540526044741 2006018752551663848633389)
                  ·
                    refine ⟨752257032206873943237521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006018752551663848633389 752257032206873943237521)
                    ·
                      rfl

theorem cell22_2197523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 3].length) (baseStart_2197523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197523 prefixEnd_2197523 := by exact prefixLift 2197523
  have htrace : WordTrace (prefixWord ++ tailWord_2197523) baseStart_2197523 baseEnd_2197523 := by
    simpa [prefixWord, tailWord_2197523, baseEnd_2197523] using wordTrace_append hprefix tailTrace_2197523
  have hstable : (prefixWord ++ tailWord_2197523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197523).length < 2 ^ (prefixWord ++ tailWord_2197523).sum := by decide
  have hdescent : baseEnd_2197523 < baseStart_2197523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197538 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2197538 : Nat := 118140960795 + 2197538 * 2 ^ 59
def prefixEnd_2197538 : Nat := 4983230072969 + 3 ^ 40 * 2197538 * 2
def baseEnd_2197538 : Nat := 752262167013418904112475

theorem tailTrace_2197538 : CollatzResearch.WordTrace tailWord_2197538 prefixEnd_2197538 752262167013418904112475 := by
  unfold tailWord_2197538
  simp only [CollatzResearch.WordTrace]
  refine ⟨20037698878175652613896317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53433863675135073637056845 20037698878175652613896317)
  ·
    refine ⟨7514137079315869730211119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20037698878175652613896317 7514137079315869730211119)
    ·
      refine ⟨11271205618973804595316679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7514137079315869730211119 11271205618973804595316679)
      ·
        refine ⟨16906808428460706892975019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11271205618973804595316679 16906808428460706892975019)
        ·
          refine ⟨25360212642691060339462529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16906808428460706892975019 25360212642691060339462529)
          ·
            refine ⟨19020159482018295254596897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25360212642691060339462529 19020159482018295254596897)
            ·
              refine ⟨14265119611513721440947673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19020159482018295254596897 14265119611513721440947673)
              ·
                refine ⟨10698839708635291080710755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14265119611513721440947673 10698839708635291080710755)
                ·
                  refine ⟨16048259562952936621066133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10698839708635291080710755 16048259562952936621066133)
                  ·
                    refine ⟨752262167013418904112475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16048259562952936621066133 752262167013418904112475)
                    ·
                      rfl

theorem cell22_2197538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2197538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197538 prefixEnd_2197538 := by exact prefixLift 2197538
  have htrace : WordTrace (prefixWord ++ tailWord_2197538) baseStart_2197538 baseEnd_2197538 := by
    simpa [prefixWord, tailWord_2197538, baseEnd_2197538] using wordTrace_append hprefix tailTrace_2197538
  have hstable : (prefixWord ++ tailWord_2197538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197538).length < 2 ^ (prefixWord ++ tailWord_2197538).sum := by decide
  have hdescent : baseEnd_2197538 < baseStart_2197538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197551 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 9]
def baseStart_2197551 : Nat := 118140960795 + 2197551 * 2 ^ 59
def prefixEnd_2197551 : Nat := 4983230072969 + 3 ^ 40 * 2197551 * 2
def baseEnd_2197551 : Nat := 752266617179091203537435

theorem tailTrace_2197551 : CollatzResearch.WordTrace tailWord_2197551 prefixEnd_2197551 752266617179091203537435 := by
  unfold tailWord_2197551
  simp only [CollatzResearch.WordTrace]
  refine ⟨80151269661655513675808507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53434179774437009117205671 80151269661655513675808507)
  ·
    refine ⟨120226904492483270513712761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80151269661655513675808507 120226904492483270513712761)
    ·
      refine ⟨90170178369362452885284571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120226904492483270513712761 90170178369362452885284571)
      ·
        refine ⟨135255267554043679327926857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90170178369362452885284571 135255267554043679327926857)
        ·
          refine ⟨101441450665532759495945143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135255267554043679327926857 101441450665532759495945143)
          ·
            refine ⟨152162175998299139243917715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101441450665532759495945143 152162175998299139243917715)
            ·
              refine ⟨228243263997448708865876573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152162175998299139243917715 228243263997448708865876573)
              ·
                refine ⟨85591223999043265824703715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228243263997448708865876573 85591223999043265824703715)
                ·
                  refine ⟨128386835998564898737055573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85591223999043265824703715 128386835998564898737055573)
                  ·
                    refine ⟨752266617179091203537435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 128386835998564898737055573 752266617179091203537435)
                    ·
                      rfl

theorem cell22_2197551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_2197551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197551 prefixEnd_2197551 := by exact prefixLift 2197551
  have htrace : WordTrace (prefixWord ++ tailWord_2197551) baseStart_2197551 baseEnd_2197551 := by
    simpa [prefixWord, tailWord_2197551, baseEnd_2197551] using wordTrace_append hprefix tailTrace_2197551
  have hstable : (prefixWord ++ tailWord_2197551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197551).length < 2 ^ (prefixWord ++ tailWord_2197551).sum := by decide
  have hdescent : baseEnd_2197551 < baseStart_2197551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197690 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_2197690 : Nat := 118140960795 + 2197690 * 2 ^ 59
def prefixEnd_2197690 : Nat := 4983230072969 + 3 ^ 40 * 2197690 * 2
def baseEnd_2197690 : Nat := 752314199719741174312009

theorem tailTrace_2197690 : CollatzResearch.WordTrace tailWord_2197690 prefixEnd_2197690 752314199719741174312009 := by
  unfold tailWord_2197690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20039084852037985103779631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53437559605434626943412349 20039084852037985103779631)
  ·
    refine ⟨30058627278056977655669447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20039084852037985103779631 30058627278056977655669447)
    ·
      refine ⟨45087940917085466483504171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30058627278056977655669447 45087940917085466483504171)
      ·
        refine ⟨67631911375628199725256257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45087940917085466483504171 67631911375628199725256257)
        ·
          refine ⟨50723933531721149793942193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67631911375628199725256257 50723933531721149793942193)
          ·
            refine ⟨38042950148790862345456645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50723933531721149793942193 38042950148790862345456645)
            ·
              refine ⟨7133053152898286689773121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38042950148790862345456645 7133053152898286689773121)
              ·
                refine ⟨5349789864673715017329841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7133053152898286689773121 5349789864673715017329841)
                ·
                  refine ⟨4012342398505286262997381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5349789864673715017329841 4012342398505286262997381)
                  ·
                    refine ⟨752314199719741174312009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012342398505286262997381 752314199719741174312009)
                    ·
                      rfl

theorem cell22_2197690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_2197690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197690 prefixEnd_2197690 := by exact prefixLift 2197690
  have htrace : WordTrace (prefixWord ++ tailWord_2197690) baseStart_2197690 baseEnd_2197690 := by
    simpa [prefixWord, tailWord_2197690, baseEnd_2197690] using wordTrace_append hprefix tailTrace_2197690
  have hstable : (prefixWord ++ tailWord_2197690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197690).length < 2 ^ (prefixWord ++ tailWord_2197690).sum := by decide
  have hdescent : baseEnd_2197690 < baseStart_2197690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197694 : List Nat := [4, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2197694 : Nat := 118140960795 + 2197694 * 2 ^ 59
def prefixEnd_2197694 : Nat := 4983230072969 + 3 ^ 40 * 2197694 * 2
def baseEnd_2197694 : Nat := 250771856333828832403999

theorem tailTrace_2197694 : CollatzResearch.WordTrace tailWord_2197694 prefixEnd_2197694 250771856333828832403999 := by
  unfold tailWord_2197694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10019560662517181137283017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53437656866758299398842757 10019560662517181137283017)
  ·
    refine ⟨7514670496887885852962263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10019560662517181137283017 7514670496887885852962263)
    ·
      refine ⟨11272005745331828779443395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7514670496887885852962263 11272005745331828779443395)
      ·
        refine ⟨16908008617997743169165093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272005745331828779443395 16908008617997743169165093)
        ·
          refine ⟨3170251615874576844218455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16908008617997743169165093 3170251615874576844218455)
          ·
            refine ⟨4755377423811865266327683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170251615874576844218455 4755377423811865266327683)
            ·
              refine ⟨7133066135717797899491525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4755377423811865266327683 7133066135717797899491525)
              ·
                refine ⟨1337449900447087106154661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7133066135717797899491525 1337449900447087106154661)
                ·
                  refine ⟨250771856333828832403999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1337449900447087106154661 250771856333828832403999)
                  ·
                    rfl

theorem cell22_2197694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2197694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197694 prefixEnd_2197694 := by exact prefixLift 2197694
  have htrace : WordTrace (prefixWord ++ tailWord_2197694) baseStart_2197694 baseEnd_2197694 := by
    simpa [prefixWord, tailWord_2197694, baseEnd_2197694] using wordTrace_append hprefix tailTrace_2197694
  have hstable : (prefixWord ++ tailWord_2197694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197694).length < 2 ^ (prefixWord ++ tailWord_2197694).sum := by decide
  have hdescent : baseEnd_2197694 < baseStart_2197694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197703 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2197703 : Nat := 118140960795 + 2197703 * 2 ^ 59
def prefixEnd_2197703 : Nat := 4983230072969 + 3 ^ 40 * 2197703 * 2
def baseEnd_2197703 : Nat := 752318649885413473736969

theorem tailTrace_2197703 : CollatzResearch.WordTrace tailWord_2197703 prefixEnd_2197703 752318649885413473736969 := by
  unfold tailWord_2197703
  simp only [CollatzResearch.WordTrace]
  refine ⟨80156813557104843635341763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53437875704736562423561175 80156813557104843635341763)
  ·
    refine ⟨120235220335657265453012645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80156813557104843635341763 120235220335657265453012645)
    ·
      refine ⟨22544103812935737272439871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120235220335657265453012645 22544103812935737272439871)
      ·
        refine ⟨33816155719403605908659807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22544103812935737272439871 33816155719403605908659807)
        ·
          refine ⟨50724233579105408862989711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33816155719403605908659807 50724233579105408862989711)
          ·
            refine ⟨76086350368658113294484567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50724233579105408862989711 76086350368658113294484567)
            ·
              refine ⟨114129525552987169941726851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76086350368658113294484567 114129525552987169941726851)
              ·
                refine ⟨171194288329480754912590277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114129525552987169941726851 171194288329480754912590277)
                ·
                  refine ⟨32098929061777641546110677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171194288329480754912590277 32098929061777641546110677)
                  ·
                    refine ⟨752318649885413473736969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32098929061777641546110677 752318649885413473736969)
                    ·
                      rfl

theorem cell22_2197703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2197703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197703 prefixEnd_2197703 := by exact prefixLift 2197703
  have htrace : WordTrace (prefixWord ++ tailWord_2197703) baseStart_2197703 baseEnd_2197703 := by
    simpa [prefixWord, tailWord_2197703, baseEnd_2197703] using wordTrace_append hprefix tailTrace_2197703
  have hstable : (prefixWord ++ tailWord_2197703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197703).length < 2 ^ (prefixWord ++ tailWord_2197703).sum := by decide
  have hdescent : baseEnd_2197703 < baseStart_2197703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197724 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2197724 : Nat := 118140960795 + 2197724 * 2 ^ 59
def prefixEnd_2197724 : Nat := 4983230072969 + 3 ^ 40 * 2197724 * 2
def baseEnd_2197724 : Nat := 752325838614576418961905

theorem tailTrace_2197724 : CollatzResearch.WordTrace tailWord_2197724 prefixEnd_2197724 752325838614576418961905 := by
  unfold tailWord_2197724
  simp only [CollatzResearch.WordTrace]
  refine ⟨40078789745014382110928113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53438386326685842814570817 40078789745014382110928113)
  ·
    refine ⟨30059092308760786583196085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40078789745014382110928113 30059092308760786583196085)
    ·
      refine ⟨2818039903946323742174633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30059092308760786583196085 2818039903946323742174633)
      ·
        refine ⟨2113529927959742806630975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2818039903946323742174633 2113529927959742806630975)
        ·
          refine ⟨3170294891939614209946463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113529927959742806630975 3170294891939614209946463)
          ·
            refine ⟨4755442337909421314919695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170294891939614209946463 4755442337909421314919695)
            ·
              refine ⟨7133163506864131972379543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4755442337909421314919695 7133163506864131972379543)
              ·
                refine ⟨10699745260296197958569315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7133163506864131972379543 10699745260296197958569315)
                ·
                  refine ⟨16049617890444296937853973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10699745260296197958569315 16049617890444296937853973)
                  ·
                    refine ⟨752325838614576418961905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16049617890444296937853973 752325838614576418961905)
                    ·
                      rfl

theorem cell22_2197724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2197724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197724 prefixEnd_2197724 := by exact prefixLift 2197724
  have htrace : WordTrace (prefixWord ++ tailWord_2197724) baseStart_2197724 baseEnd_2197724 := by
    simpa [prefixWord, tailWord_2197724, baseEnd_2197724] using wordTrace_append hprefix tailTrace_2197724
  have hstable : (prefixWord ++ tailWord_2197724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197724).length < 2 ^ (prefixWord ++ tailWord_2197724).sum := by decide
  have hdescent : baseEnd_2197724 < baseStart_2197724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197730 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2197730 : Nat := 118140960795 + 2197730 * 2 ^ 59
def prefixEnd_2197730 : Nat := 4983230072969 + 3 ^ 40 * 2197730 * 2
def baseEnd_2197730 : Nat := 752327892537194403311887

theorem tailTrace_2197730 : CollatzResearch.WordTrace tailWord_2197730 prefixEnd_2197730 752327892537194403311887 := by
  unfold tailWord_2197730
  simp only [CollatzResearch.WordTrace]
  refine ⟨20039449582001756811643661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53438532218671351497716429 20039449582001756811643661)
  ·
    refine ⟨7514793593250658804366373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20039449582001756811643661 7514793593250658804366373)
    ·
      refine ⟨1409023798734498525818695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7514793593250658804366373 1409023798734498525818695)
      ·
        refine ⟨2113535698101747788728043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1409023798734498525818695 2113535698101747788728043)
        ·
          refine ⟨3170303547152621683092065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113535698101747788728043 3170303547152621683092065)
          ·
            refine ⟨2377727660364466262319049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3170303547152621683092065 2377727660364466262319049)
            ·
              refine ⟨1783295745273349696739287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2377727660364466262319049 1783295745273349696739287)
              ·
                refine ⟨2674943617910024545108931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1783295745273349696739287 2674943617910024545108931)
                ·
                  refine ⟨4012415426865036817663397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674943617910024545108931 4012415426865036817663397)
                  ·
                    refine ⟨752327892537194403311887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012415426865036817663397 752327892537194403311887)
                    ·
                      rfl

theorem cell22_2197730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2197730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197730 prefixEnd_2197730 := by exact prefixLift 2197730
  have htrace : WordTrace (prefixWord ++ tailWord_2197730) baseStart_2197730 baseEnd_2197730 := by
    simpa [prefixWord, tailWord_2197730, baseEnd_2197730] using wordTrace_append hprefix tailTrace_2197730
  have hstable : (prefixWord ++ tailWord_2197730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197730).length < 2 ^ (prefixWord ++ tailWord_2197730).sum := by decide
  have hdescent : baseEnd_2197730 < baseStart_2197730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197754 : List Nat := [3, 1, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_2197754 : Nat := 118140960795 + 2197754 * 2 ^ 59
def prefixEnd_2197754 : Nat := 4983230072969 + 3 ^ 40 * 2197754 * 2
def baseEnd_2197754 : Nat := 752336108227666340711813

theorem tailTrace_2197754 : CollatzResearch.WordTrace tailWord_2197754 prefixEnd_2197754 752336108227666340711813 := by
  unfold tailWord_2197754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20039668419980019836362079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53439115786613386230298877 20039668419980019836362079)
  ·
    refine ⟨30059502629970029754543119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20039668419980019836362079 30059502629970029754543119)
    ·
      refine ⟨45089253944955044631814679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30059502629970029754543119 45089253944955044631814679)
      ·
        refine ⟨67633880917432566947722019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45089253944955044631814679 67633880917432566947722019)
        ·
          refine ⟨101450821376148850421583029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67633880917432566947722019 101450821376148850421583029)
          ·
            refine ⟨9511014504013954727023409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101450821376148850421583029 9511014504013954727023409)
            ·
              refine ⟨7133260878010466045267557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9511014504013954727023409 7133260878010466045267557)
              ·
                refine ⟨1337486414626962383487667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7133260878010466045267557 1337486414626962383487667)
                ·
                  refine ⟨2006229621940443575231501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337486414626962383487667 2006229621940443575231501)
                  ·
                    refine ⟨752336108227666340711813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006229621940443575231501 752336108227666340711813)
                    ·
                      rfl

theorem cell22_2197754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_2197754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197754 prefixEnd_2197754 := by exact prefixLift 2197754
  have htrace : WordTrace (prefixWord ++ tailWord_2197754) baseStart_2197754 baseEnd_2197754 := by
    simpa [prefixWord, tailWord_2197754, baseEnd_2197754] using wordTrace_append hprefix tailTrace_2197754
  have hstable : (prefixWord ++ tailWord_2197754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197754).length < 2 ^ (prefixWord ++ tailWord_2197754).sum := by decide
  have hdescent : baseEnd_2197754 < baseStart_2197754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197805 : List Nat := [1, 5, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2197805 : Nat := 118140960795 + 2197805 * 2 ^ 59
def prefixEnd_2197805 : Nat := 4983230072969 + 3 ^ 40 * 2197805 * 2
def baseEnd_2197805 : Nat := 752353566569919207686657

theorem tailTrace_2197805 : CollatzResearch.WordTrace tailWord_2197805 prefixEnd_2197805 752353566569919207686657 := by
  unfold tailWord_2197805
  simp only [CollatzResearch.WordTrace]
  refine ⟨80160533802735315055554869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53440355868490210037036579 80160533802735315055554869)
  ·
    refine ⟨7515050044006435786458269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80160533802735315055554869 7515050044006435786458269)
    ·
      refine ⟨2818143766502413419921851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7515050044006435786458269 2818143766502413419921851)
      ·
        refine ⟨4227215649753620129882777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2818143766502413419921851 4227215649753620129882777)
        ·
          refine ⟨3170411737315215097412083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4227215649753620129882777 3170411737315215097412083)
          ·
            refine ⟨4755617605972822646118125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170411737315215097412083 4755617605972822646118125)
            ·
              refine ⟨1783356602239808492294297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4755617605972822646118125 1783356602239808492294297)
              ·
                refine ⟨1337517451679856369220723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1783356602239808492294297 1337517451679856369220723)
                ·
                  refine ⟨2006276177519784553831085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337517451679856369220723 2006276177519784553831085)
                  ·
                    refine ⟨752353566569919207686657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006276177519784553831085 752353566569919207686657)
                    ·
                      rfl

theorem cell22_2197805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2197805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197805 prefixEnd_2197805 := by exact prefixLift 2197805
  have htrace : WordTrace (prefixWord ++ tailWord_2197805) baseStart_2197805 baseEnd_2197805 := by
    simpa [prefixWord, tailWord_2197805, baseEnd_2197805] using wordTrace_append hprefix tailTrace_2197805
  have hstable : (prefixWord ++ tailWord_2197805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197805).length < 2 ^ (prefixWord ++ tailWord_2197805).sum := by decide
  have hdescent : baseEnd_2197805 < baseStart_2197805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197840 : List Nat := [2, 1, 1, 1, 1, 6, 2, 8]
def baseStart_2197840 : Nat := 118140960795 + 2197840 * 2 ^ 59
def prefixEnd_2197840 : Nat := 4983230072969 + 3 ^ 40 * 2197840 * 2
def baseEnd_2197840 : Nat := 83596171976132309229061

theorem tailTrace_2197840 : CollatzResearch.WordTrace tailWord_2197840 prefixEnd_2197840 83596171976132309229061 := by
  unfold tailWord_2197840
  simp only [CollatzResearch.WordTrace]
  refine ⟨40080905178804258016539487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53441206905072344022052649 40080905178804258016539487)
  ·
    refine ⟨60121357768206387024809231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40080905178804258016539487 60121357768206387024809231)
    ·
      refine ⟨90182036652309580537213847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60121357768206387024809231 90182036652309580537213847)
      ·
        refine ⟨135273054978464370805820771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90182036652309580537213847 135273054978464370805820771)
        ·
          refine ⟨202909582467696556208731157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135273054978464370805820771 202909582467696556208731157)
          ·
            refine ⟨9511386678173276072284273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 202909582467696556208731157 9511386678173276072284273)
            ·
              refine ⟨7133540008629957054213205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9511386678173276072284273 7133540008629957054213205)
              ·
                refine ⟨83596171976132309229061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7133540008629957054213205 83596171976132309229061)
                ·
                  rfl

theorem cell22_2197840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 8].length) (baseStart_2197840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197840 prefixEnd_2197840 := by exact prefixLift 2197840
  have htrace : WordTrace (prefixWord ++ tailWord_2197840) baseStart_2197840 baseEnd_2197840 := by
    simpa [prefixWord, tailWord_2197840, baseEnd_2197840] using wordTrace_append hprefix tailTrace_2197840
  have hstable : (prefixWord ++ tailWord_2197840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197840).length < 2 ^ (prefixWord ++ tailWord_2197840).sum := by decide
  have hdescent : baseEnd_2197840 < baseStart_2197840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197842 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_2197842 : Nat := 118140960795 + 2197842 * 2 ^ 59
def prefixEnd_2197842 : Nat := 4983230072969 + 3 ^ 40 * 2197842 * 2
def baseEnd_2197842 : Nat := 752366232426063444511543

theorem tailTrace_2197842 : CollatzResearch.WordTrace tailWord_2197842 prefixEnd_2197842 752366232426063444511543 := by
  unfold tailWord_2197842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20040470825900317593662945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53441255535734180249767853 20040470825900317593662945)
  ·
    refine ⟨15030353119425238195247209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20040470825900317593662945 15030353119425238195247209)
    ·
      refine ⟨11272764839568928646435407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15030353119425238195247209 11272764839568928646435407)
      ·
        refine ⟨16909147259353392969653111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272764839568928646435407 16909147259353392969653111)
        ·
          refine ⟨25363720889030089454479667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16909147259353392969653111 25363720889030089454479667)
          ·
            refine ⟨38045581333545134181719501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25363720889030089454479667 38045581333545134181719501)
            ·
              refine ⟨14267093000079425318144813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38045581333545134181719501 14267093000079425318144813)
              ·
                refine ⟨5350159875029784494304305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14267093000079425318144813 5350159875029784494304305)
                ·
                  refine ⟨4012619906272338370728229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5350159875029784494304305 4012619906272338370728229)
                  ·
                    refine ⟨752366232426063444511543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012619906272338370728229 752366232426063444511543)
                    ·
                      rfl

theorem cell22_2197842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_2197842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197842 prefixEnd_2197842 := by exact prefixLift 2197842
  have htrace : WordTrace (prefixWord ++ tailWord_2197842) baseStart_2197842 baseEnd_2197842 := by
    simpa [prefixWord, tailWord_2197842, baseEnd_2197842] using wordTrace_append hprefix tailTrace_2197842
  have hstable : (prefixWord ++ tailWord_2197842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197842).length < 2 ^ (prefixWord ++ tailWord_2197842).sum := by decide
  have hdescent : baseEnd_2197842 < baseStart_2197842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197889 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2197889 : Nat := 118140960795 + 2197889 * 2 ^ 59
def prefixEnd_2197889 : Nat := 4983230072969 + 3 ^ 40 * 2197889 * 2
def baseEnd_2197889 : Nat := 752382321486570988586399

theorem tailTrace_2197889 : CollatzResearch.WordTrace tailWord_2197889 prefixEnd_2197889 752382321486570988586399 := by
  unfold tailWord_2197889
  simp only [CollatzResearch.WordTrace]
  refine ⟨80163597534430997401612721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53442398356287331601075147 80163597534430997401612721)
  ·
    refine ⟨60122698150823248051209541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80163597534430997401612721 60122698150823248051209541)
    ·
      refine ⟨11273005903279359009601789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60122698150823248051209541 11273005903279359009601789)
      ·
        refine ⟨4227377213729759628600671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11273005903279359009601789 4227377213729759628600671)
        ·
          refine ⟨6341065820594639442901007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4227377213729759628600671 6341065820594639442901007)
          ·
            refine ⟨9511598730891959164351511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6341065820594639442901007 9511598730891959164351511)
            ·
              refine ⟨14267398096337938746527267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9511598730891959164351511 14267398096337938746527267)
              ·
                refine ⟨21401097144506908119790901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14267398096337938746527267 21401097144506908119790901)
                ·
                  refine ⟨2006352857297522636230397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21401097144506908119790901 2006352857297522636230397)
                  ·
                    refine ⟨752382321486570988586399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006352857297522636230397 752382321486570988586399)
                    ·
                      rfl

theorem cell22_2197889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2197889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197889 prefixEnd_2197889 := by exact prefixLift 2197889
  have htrace : WordTrace (prefixWord ++ tailWord_2197889) baseStart_2197889 baseEnd_2197889 := by
    simpa [prefixWord, tailWord_2197889, baseEnd_2197889] using wordTrace_append hprefix tailTrace_2197889
  have hstable : (prefixWord ++ tailWord_2197889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197889).length < 2 ^ (prefixWord ++ tailWord_2197889).sum := by decide
  have hdescent : baseEnd_2197889 < baseStart_2197889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197949 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_2197949 : Nat := 118140960795 + 2197949 * 2 ^ 59
def prefixEnd_2197949 : Nat := 4983230072969 + 3 ^ 40 * 2197949 * 2
def baseEnd_2197949 : Nat := 752402860712750832086215

theorem tailTrace_2197949 : CollatzResearch.WordTrace tailWord_2197949 prefixEnd_2197949 752402860712750832086215 := by
  unfold tailWord_2197949
  simp only [CollatzResearch.WordTrace]
  refine ⟨80165785914213627648796901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53443857276142418432531267 80165785914213627648796901)
  ·
    refine ⟨15031084858915055184149419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80165785914213627648796901 15031084858915055184149419)
    ·
      refine ⟨22546627288372582776224129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15031084858915055184149419 22546627288372582776224129)
      ·
        refine ⟨16909970466279437082168097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22546627288372582776224129 16909970466279437082168097)
        ·
          refine ⟨12682477849709577811626073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16909970466279437082168097 12682477849709577811626073)
          ·
            refine ⟨9511858387282183358719555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12682477849709577811626073 9511858387282183358719555)
            ·
              refine ⟨14267787580923275038079333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9511858387282183358719555 14267787580923275038079333)
              ·
                refine ⟨2675210171423114069639875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14267787580923275038079333 2675210171423114069639875)
                ·
                  refine ⟨4012815257134671104459813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675210171423114069639875 4012815257134671104459813)
                  ·
                    refine ⟨752402860712750832086215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012815257134671104459813 752402860712750832086215)
                    ·
                      rfl

theorem cell22_2197949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_2197949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197949 prefixEnd_2197949 := by exact prefixLift 2197949
  have htrace : WordTrace (prefixWord ++ tailWord_2197949) baseStart_2197949 baseEnd_2197949 := by
    simpa [prefixWord, tailWord_2197949, baseEnd_2197949] using wordTrace_append hprefix tailTrace_2197949
  have hstable : (prefixWord ++ tailWord_2197949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197949).length < 2 ^ (prefixWord ++ tailWord_2197949).sum := by decide
  have hdescent : baseEnd_2197949 < baseStart_2197949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197962 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_2197962 : Nat := 118140960795 + 2197962 * 2 ^ 59
def prefixEnd_2197962 : Nat := 4983230072969 + 3 ^ 40 * 2197962 * 2
def baseEnd_2197962 : Nat := 752407310878423131511175

theorem tailTrace_2197962 : CollatzResearch.WordTrace tailWord_2197962 prefixEnd_2197962 752407310878423131511175 := by
  unfold tailWord_2197962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20041565015791632717255035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53444173375444353912680093 20041565015791632717255035)
  ·
    refine ⟨30062347523687449075882553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20041565015791632717255035 30062347523687449075882553)
    ·
      refine ⟨22546760642765586806911915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30062347523687449075882553 22546760642765586806911915)
      ·
        refine ⟨33820140964148380210367873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22546760642765586806911915 33820140964148380210367873)
        ·
          refine ⟨25365105723111285157775905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33820140964148380210367873 25365105723111285157775905)
          ·
            refine ⟨19023829292333463868331929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25365105723111285157775905 19023829292333463868331929)
            ·
              refine ⟨14267871969250097901248947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19023829292333463868331929 14267871969250097901248947)
              ·
                refine ⟨21401807953875146851873421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14267871969250097901248947 21401807953875146851873421)
                ·
                  refine ⟨8025677982703180069452533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21401807953875146851873421 8025677982703180069452533)
                  ·
                    refine ⟨752407310878423131511175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8025677982703180069452533 752407310878423131511175)
                    ·
                      rfl

theorem cell22_2197962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_2197962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197962 prefixEnd_2197962 := by exact prefixLift 2197962
  have htrace : WordTrace (prefixWord ++ tailWord_2197962) baseStart_2197962 baseEnd_2197962 := by
    simpa [prefixWord, tailWord_2197962, baseEnd_2197962] using wordTrace_append hprefix tailTrace_2197962
  have hstable : (prefixWord ++ tailWord_2197962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197962).length < 2 ^ (prefixWord ++ tailWord_2197962).sum := by decide
  have hdescent : baseEnd_2197962 < baseStart_2197962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197992 : List Nat := [2, 1, 4, 1, 1, 3, 1, 9]
def baseStart_2197992 : Nat := 118140960795 + 2197992 * 2 ^ 59
def prefixEnd_2197992 : Nat := 4983230072969 + 3 ^ 40 * 2197992 * 2
def baseEnd_2197992 : Nat := 83601953387945894806787

theorem tailTrace_2197992 : CollatzResearch.WordTrace tailWord_2197992 prefixEnd_2197992 83601953387945894806787 := by
  unfold tailWord_2197992
  simp only [CollatzResearch.WordTrace]
  refine ⟨40083677126528922996306115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53444902835371897328408153 40083677126528922996306115)
  ·
    refine ⟨60125515689793384494459173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40083677126528922996306115 60125515689793384494459173)
    ·
      refine ⟨11273534191836259592711095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60125515689793384494459173 11273534191836259592711095)
      ·
        refine ⟨16910301287754389389066643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11273534191836259592711095 16910301287754389389066643)
        ·
          refine ⟨25365451931631584083599965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16910301287754389389066643 25365451931631584083599965)
          ·
            refine ⟨9512044474361844031349987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25365451931631584083599965 9512044474361844031349987)
            ·
              refine ⟨14268066711542766047024981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9512044474361844031349987 14268066711542766047024981)
              ·
                refine ⟨83601953387945894806787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14268066711542766047024981 83601953387945894806787)
                ·
                  rfl

theorem cell22_2197992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 9].length) (baseStart_2197992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2197992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2197992 prefixEnd_2197992 := by exact prefixLift 2197992
  have htrace : WordTrace (prefixWord ++ tailWord_2197992) baseStart_2197992 baseEnd_2197992 := by
    simpa [prefixWord, tailWord_2197992, baseEnd_2197992] using wordTrace_append hprefix tailTrace_2197992
  have hstable : (prefixWord ++ tailWord_2197992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197992).length < 2 ^ (prefixWord ++ tailWord_2197992).sum := by decide
  have hdescent : baseEnd_2197992 < baseStart_2197992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198041 : List Nat := [1, 2, 1, 2, 1, 1, 2, 8, 1, 3]
def baseStart_2198041 : Nat := 118140960795 + 2198041 * 2 ^ 59
def prefixEnd_2198041 : Nat := 4983230072969 + 3 ^ 40 * 2198041 * 2
def baseEnd_2198041 : Nat := 752434354192893258785933

theorem tailTrace_2198041 : CollatzResearch.WordTrace tailWord_2198041 prefixEnd_2198041 752434354192893258785933 := by
  unfold tailWord_2198041
  simp only [CollatzResearch.WordTrace]
  refine ⟨80169141429880327361145977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53446094286586884907430651 80169141429880327361145977)
  ·
    refine ⟨60126856072410245520859483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80169141429880327361145977 60126856072410245520859483)
    ·
      refine ⟨90190284108615368281289225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60126856072410245520859483 90190284108615368281289225)
      ·
        refine ⟨67642713081461526210966919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90190284108615368281289225 67642713081461526210966919)
        ·
          refine ⟨101464069622192289316450379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67642713081461526210966919 101464069622192289316450379)
          ·
            refine ⟨152196104433288433974675569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101464069622192289316450379 152196104433288433974675569)
            ·
              refine ⟨114147078324966325481006677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152196104433288433974675569 114147078324966325481006677)
              ·
                refine ⟨1337661074120699126730547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 114147078324966325481006677 1337661074120699126730547)
                ·
                  refine ⟨2006491611181048690095821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337661074120699126730547 2006491611181048690095821)
                  ·
                    refine ⟨752434354192893258785933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006491611181048690095821 752434354192893258785933)
                    ·
                      rfl

theorem cell22_2198041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 3].length) (baseStart_2198041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198041 prefixEnd_2198041 := by exact prefixLift 2198041
  have htrace : WordTrace (prefixWord ++ tailWord_2198041) baseStart_2198041 baseEnd_2198041 := by
    simpa [prefixWord, tailWord_2198041, baseEnd_2198041] using wordTrace_append hprefix tailTrace_2198041
  have hstable : (prefixWord ++ tailWord_2198041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198041).length < 2 ^ (prefixWord ++ tailWord_2198041).sum := by decide
  have hdescent : baseEnd_2198041 < baseStart_2198041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198144 : List Nat := [2, 1, 1, 2, 1, 7, 8]
def baseStart_2198144 : Nat := 118140960795 + 2198144 * 2 ^ 59
def prefixEnd_2198144 : Nat := 4983230072969 + 3 ^ 40 * 2198144 * 2
def baseEnd_2198144 : Nat := 27869244933253160128171

theorem tailTrace_2198144 : CollatzResearch.WordTrace tailWord_2198144 prefixEnd_2198144 27869244933253160128171 := by
  unfold tailWord_2198144
  simp only [CollatzResearch.WordTrace]
  refine ⟨40086449074253587976072743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53448598765671450634763657 40086449074253587976072743)
  ·
    refine ⟨60129673611380381964109115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40086449074253587976072743 60129673611380381964109115)
    ·
      refine ⟨90194510417070572946163673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60129673611380381964109115 90194510417070572946163673)
      ·
        refine ⟨67645882812802929709622755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90194510417070572946163673 67645882812802929709622755)
        ·
          refine ⟨101468824219204394564434133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67645882812802929709622755 101468824219204394564434133)
          ·
            refine ⟨2378175567637602997603925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 101468824219204394564434133 2378175567637602997603925)
            ·
              refine ⟨27869244933253160128171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2378175567637602997603925 27869244933253160128171)
              ·
                rfl

theorem cell22_2198144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 8].length) (baseStart_2198144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198144 prefixEnd_2198144 := by exact prefixLift 2198144
  have htrace : WordTrace (prefixWord ++ tailWord_2198144) baseStart_2198144 baseEnd_2198144 := by
    simpa [prefixWord, tailWord_2198144, baseEnd_2198144] using wordTrace_append hprefix tailTrace_2198144
  have hstable : (prefixWord ++ tailWord_2198144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198144).length < 2 ^ (prefixWord ++ tailWord_2198144).sum := by decide
  have hdescent : baseEnd_2198144 < baseStart_2198144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198253 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2198253 : Nat := 118140960795 + 2198253 * 2 ^ 59
def prefixEnd_2198253 : Nat := 4983230072969 + 3 ^ 40 * 2198253 * 2
def baseEnd_2198253 : Nat := 752506926125395372485283

theorem tailTrace_2198253 : CollatzResearch.WordTrace tailWord_2198253 prefixEnd_2198253 752506926125395372485283 := by
  unfold tailWord_2198253
  simp only [CollatzResearch.WordTrace]
  refine ⟨80176873705112287567863413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53451249136741525045242275 80176873705112287567863413)
  ·
    refine ⟨7516581909854276959487195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80176873705112287567863413 7516581909854276959487195)
    ·
      refine ⟨11274872864781415439230793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7516581909854276959487195 11274872864781415439230793)
      ·
        refine ⟨8456154648586061579423095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11274872864781415439230793 8456154648586061579423095)
        ·
          refine ⟨12684231972879092369134643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8456154648586061579423095 12684231972879092369134643)
          ·
            refine ⟨19026347959318638553701965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12684231972879092369134643 19026347959318638553701965)
            ·
              refine ⟨7134880484744489457638237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19026347959318638553701965 7134880484744489457638237)
              ·
                refine ⟨2675580181779183546614339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7134880484744489457638237 2675580181779183546614339)
                ·
                  refine ⟨4013370272668775319921509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675580181779183546614339 4013370272668775319921509)
                  ·
                    refine ⟨752506926125395372485283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4013370272668775319921509 752506926125395372485283)
                    ·
                      rfl

theorem cell22_2198253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2198253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198253 prefixEnd_2198253 := by exact prefixLift 2198253
  have htrace : WordTrace (prefixWord ++ tailWord_2198253) baseStart_2198253 baseEnd_2198253 := by
    simpa [prefixWord, tailWord_2198253, baseEnd_2198253] using wordTrace_append hprefix tailTrace_2198253
  have hstable : (prefixWord ++ tailWord_2198253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198253).length < 2 ^ (prefixWord ++ tailWord_2198253).sum := by decide
  have hdescent : baseEnd_2198253 < baseStart_2198253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198268 : List Nat := [2, 2, 2, 1, 3, 2, 2, 4, 4]
def baseStart_2198268 : Nat := 118140960795 + 2198268 * 2 ^ 59
def prefixEnd_2198268 : Nat := 4983230072969 + 3 ^ 40 * 2198268 * 2
def baseEnd_2198268 : Nat := 250837353643980111120079

theorem tailTrace_2198268 : CollatzResearch.WordTrace tailWord_2198268 prefixEnd_2198268 250837353643980111120079 := by
  unfold tailWord_2198268
  simp only [CollatzResearch.WordTrace]
  refine ⟨40088710400028972564829729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53451613866705296753106305 40088710400028972564829729)
  ·
    refine ⟨30066532800021729423622297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40088710400028972564829729 30066532800021729423622297)
    ·
      refine ⟨22549899600016297067716723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30066532800021729423622297 22549899600016297067716723)
      ·
        refine ⟨33824849400024445601575085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22549899600016297067716723 33824849400024445601575085)
        ·
          refine ⟨12684318525009167100590657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33824849400024445601575085 12684318525009167100590657)
          ·
            refine ⟨9513238893756875325442993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12684318525009167100590657 9513238893756875325442993)
            ·
              refine ⟨7134929170317656494082245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9513238893756875325442993 7134929170317656494082245)
              ·
                refine ⟨1337799219434560592640421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7134929170317656494082245 1337799219434560592640421)
                ·
                  refine ⟨250837353643980111120079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1337799219434560592640421 250837353643980111120079)
                  ·
                    rfl

theorem cell22_2198268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_2198268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198268 prefixEnd_2198268 := by exact prefixLift 2198268
  have htrace : WordTrace (prefixWord ++ tailWord_2198268) baseStart_2198268 baseEnd_2198268 := by
    simpa [prefixWord, tailWord_2198268, baseEnd_2198268] using wordTrace_append hprefix tailTrace_2198268
  have hstable : (prefixWord ++ tailWord_2198268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198268).length < 2 ^ (prefixWord ++ tailWord_2198268).sum := by decide
  have hdescent : baseEnd_2198268 < baseStart_2198268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198334 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_2198334 : Nat := 118140960795 + 2198334 * 2 ^ 59
def prefixEnd_2198334 : Nat := 4983230072969 + 3 ^ 40 * 2198334 * 2
def baseEnd_2198334 : Nat := 752534654080738161210035

theorem tailTrace_2198334 : CollatzResearch.WordTrace tailWord_2198334 prefixEnd_2198334 752534654080738161210035 := by
  unfold tailWord_2198334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10022478502227354800195257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53453218678545892267708037 10022478502227354800195257)
  ·
    refine ⟨7516858876670516100146443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10022478502227354800195257 7516858876670516100146443)
    ·
      refine ⟨11275288315005774150219665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7516858876670516100146443 11275288315005774150219665)
      ·
        refine ⟨8456466236254330612664749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11275288315005774150219665 8456466236254330612664749)
        ·
          refine ⟨3171174838595373979749281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8456466236254330612664749 3171174838595373979749281)
          ·
            refine ⟨2378381128946530484811961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3171174838595373979749281 2378381128946530484811961)
            ·
              refine ⟨1783785846709897863608971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2378381128946530484811961 1783785846709897863608971)
              ·
                refine ⟨2675678770064846795413457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1783785846709897863608971 2675678770064846795413457)
                ·
                  refine ⟨2006759077548635096560093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2675678770064846795413457 2006759077548635096560093)
                  ·
                    refine ⟨752534654080738161210035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006759077548635096560093 752534654080738161210035)
                    ·
                      rfl

theorem cell22_2198334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_2198334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198334 prefixEnd_2198334 := by exact prefixLift 2198334
  have htrace : WordTrace (prefixWord ++ tailWord_2198334) baseStart_2198334 baseEnd_2198334 := by
    simpa [prefixWord, tailWord_2198334, baseEnd_2198334] using wordTrace_append hprefix tailTrace_2198334
  have hstable : (prefixWord ++ tailWord_2198334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198334).length < 2 ^ (prefixWord ++ tailWord_2198334).sum := by decide
  have hdescent : baseEnd_2198334 < baseStart_2198334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198390 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2198390 : Nat := 118140960795 + 2198390 * 2 ^ 59
def prefixEnd_2198390 : Nat := 4983230072969 + 3 ^ 40 * 2198390 * 2
def baseEnd_2198390 : Nat := 752553824025172681809863

theorem tailTrace_2198390 : CollatzResearch.WordTrace tailWord_2198390 prefixEnd_2198390 752553824025172681809863 := by
  unfold tailWord_2198390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011366906600997497850039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53454580337077306643733749 5011366906600997497850039)
  ·
    refine ⟨7517050359901496246775059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5011366906600997497850039 7517050359901496246775059)
    ·
      refine ⟨11275575539852244370162589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7517050359901496246775059 11275575539852244370162589)
      ·
        refine ⟨4228340827444591638810971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11275575539852244370162589 4228340827444591638810971)
        ·
          refine ⟨6342511241166887458216457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228340827444591638810971 6342511241166887458216457)
          ·
            refine ⟨4756883430875165593662343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6342511241166887458216457 4756883430875165593662343)
            ·
              refine ⟨7135325146312748390493515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4756883430875165593662343 7135325146312748390493515)
              ·
                refine ⟨10702987719469122585740273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7135325146312748390493515 10702987719469122585740273)
                ·
                  refine ⟨8027240789601841939305205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10702987719469122585740273 8027240789601841939305205)
                  ·
                    refine ⟨752553824025172681809863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8027240789601841939305205 752553824025172681809863)
                    ·
                      rfl

theorem cell22_2198390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2198390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198390 prefixEnd_2198390 := by exact prefixLift 2198390
  have htrace : WordTrace (prefixWord ++ tailWord_2198390) baseStart_2198390 baseEnd_2198390 := by
    simpa [prefixWord, tailWord_2198390, baseEnd_2198390] using wordTrace_append hprefix tailTrace_2198390
  have hstable : (prefixWord ++ tailWord_2198390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198390).length < 2 ^ (prefixWord ++ tailWord_2198390).sum := by decide
  have hdescent : baseEnd_2198390 < baseStart_2198390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198435 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 2, 3]
def baseStart_2198435 : Nat := 118140960795 + 2198435 * 2 ^ 59
def prefixEnd_2198435 : Nat := 4983230072969 + 3 ^ 40 * 2198435 * 2
def baseEnd_2198435 : Nat := 752569228444807564434725

theorem tailTrace_2198435 : CollatzResearch.WordTrace tailWord_2198435 prefixEnd_2198435 752569228444807564434725 := by
  unfold tailWord_2198435
  simp only [CollatzResearch.WordTrace]
  refine ⟨80183511790452932650988759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53455674526968621767325839 80183511790452932650988759)
  ·
    refine ⟨120275267685679398976483139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80183511790452932650988759 120275267685679398976483139)
    ·
      refine ⟨180412901528519098464724709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120275267685679398976483139 180412901528519098464724709)
      ·
        refine ⟨33827419036597330962135883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180412901528519098464724709 33827419036597330962135883)
        ·
          refine ⟨50741128554895996443203825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33827419036597330962135883 50741128554895996443203825)
          ·
            refine ⟨38055846416171997332402869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50741128554895996443203825 38055846416171997332402869)
            ·
              refine ⟨3567735601516124749912769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38055846416171997332402869 3567735601516124749912769)
              ·
                refine ⟨2675801701137093562434577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3567735601516124749912769 2675801701137093562434577)
                ·
                  refine ⟨2006851275852820171825933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2675801701137093562434577 2006851275852820171825933)
                  ·
                    refine ⟨752569228444807564434725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006851275852820171825933 752569228444807564434725)
                    ·
                      rfl

theorem cell22_2198435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 3].length) (baseStart_2198435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198435 prefixEnd_2198435 := by exact prefixLift 2198435
  have htrace : WordTrace (prefixWord ++ tailWord_2198435) baseStart_2198435 baseEnd_2198435 := by
    simpa [prefixWord, tailWord_2198435, baseEnd_2198435] using wordTrace_append hprefix tailTrace_2198435
  have hstable : (prefixWord ++ tailWord_2198435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198435).length < 2 ^ (prefixWord ++ tailWord_2198435).sum := by decide
  have hdescent : baseEnd_2198435 < baseStart_2198435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198452 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2198452 : Nat := 118140960795 + 2198452 * 2 ^ 59
def prefixEnd_2198452 : Nat := 4983230072969 + 3 ^ 40 * 2198452 * 2
def baseEnd_2198452 : Nat := 752575047892225186759673

theorem tailTrace_2198452 : CollatzResearch.WordTrace tailWord_2198452 prefixEnd_2198452 752575047892225186759673 := by
  unfold tailWord_2198452
  simp only [CollatzResearch.WordTrace]
  refine ⟨40092065915695672277178805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53456087887594229702905073 40092065915695672277178805)
  ·
    refine ⟨3758631179596469275985513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40092065915695672277178805 3758631179596469275985513)
    ·
      refine ⟨2818973384697351956989135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3758631179596469275985513 2818973384697351956989135)
      ·
        refine ⟨4228460077046027935483703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2818973384697351956989135 4228460077046027935483703)
        ·
          refine ⟨6342690115569041903225555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228460077046027935483703 6342690115569041903225555)
          ·
            refine ⟨9514035173353562854838333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6342690115569041903225555 9514035173353562854838333)
            ·
              refine ⟨3567763190007586070564375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9514035173353562854838333 3567763190007586070564375)
              ·
                refine ⟨5351644785011379105846563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567763190007586070564375 5351644785011379105846563)
                ·
                  refine ⟨8027467177517068658769845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5351644785011379105846563 8027467177517068658769845)
                  ·
                    refine ⟨752575047892225186759673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8027467177517068658769845 752575047892225186759673)
                    ·
                      rfl

theorem cell22_2198452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2198452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198452 prefixEnd_2198452 := by exact prefixLift 2198452
  have htrace : WordTrace (prefixWord ++ tailWord_2198452) baseStart_2198452 baseEnd_2198452 := by
    simpa [prefixWord, tailWord_2198452, baseEnd_2198452] using wordTrace_append hprefix tailTrace_2198452
  have hstable : (prefixWord ++ tailWord_2198452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198452).length < 2 ^ (prefixWord ++ tailWord_2198452).sum := by decide
  have hdescent : baseEnd_2198452 < baseStart_2198452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198463 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 5, 3]
def baseStart_2198463 : Nat := 118140960795 + 2198463 * 2 ^ 59
def prefixEnd_2198463 : Nat := 4983230072969 + 3 ^ 40 * 2198463 * 2
def baseEnd_2198463 : Nat := 752578813417024824734639

theorem tailTrace_2198463 : CollatzResearch.WordTrace tailWord_2198463 prefixEnd_2198463 752578813417024824734639 := by
  unfold tailWord_2198463
  simp only [CollatzResearch.WordTrace]
  refine ⟨80184533034351493433008043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53456355356234328955338695 80184533034351493433008043)
  ·
    refine ⟨120276799551527240149512065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80184533034351493433008043 120276799551527240149512065)
    ·
      refine ⟨90207599663645430112134049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120276799551527240149512065 90207599663645430112134049)
      ·
        refine ⟨67655699747734072584100537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90207599663645430112134049 67655699747734072584100537)
        ·
          refine ⟨50741774810800554438075403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67655699747734072584100537 50741774810800554438075403)
          ·
            refine ⟨76112662216200831657113105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50741774810800554438075403 76112662216200831657113105)
            ·
              refine ⟨57084496662150623742834829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76112662216200831657113105 57084496662150623742834829)
              ·
                refine ⟨21406686248306483903563061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57084496662150623742834829 21406686248306483903563061)
                ·
                  refine ⟨2006876835778732865959037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21406686248306483903563061 2006876835778732865959037)
                  ·
                    refine ⟨752578813417024824734639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006876835778732865959037 752578813417024824734639)
                    ·
                      rfl

theorem cell22_2198463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_2198463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198463 prefixEnd_2198463 := by exact prefixLift 2198463
  have htrace : WordTrace (prefixWord ++ tailWord_2198463) baseStart_2198463 baseEnd_2198463 := by
    simpa [prefixWord, tailWord_2198463, baseEnd_2198463] using wordTrace_append hprefix tailTrace_2198463
  have hstable : (prefixWord ++ tailWord_2198463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198463).length < 2 ^ (prefixWord ++ tailWord_2198463).sum := by decide
  have hdescent : baseEnd_2198463 < baseStart_2198463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198585 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_2198585 : Nat := 118140960795 + 2198585 * 2 ^ 59
def prefixEnd_2198585 : Nat := 4983230072969 + 3 ^ 40 * 2198585 * 2
def baseEnd_2198585 : Nat := 752620576510257173184265

theorem tailTrace_2198585 : CollatzResearch.WordTrace tailWord_2198585 prefixEnd_2198585 752620576510257173184265 := by
  unfold tailWord_2198585
  simp only [CollatzResearch.WordTrace]
  refine ⟨80188982739909508268949209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53459321826606338845966139 80188982739909508268949209)
  ·
    refine ⟨60141737054932131201711907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80188982739909508268949209 60141737054932131201711907)
    ·
      refine ⟨90212605582398196802567861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60141737054932131201711907 90212605582398196802567861)
      ·
        refine ⟨8457431773349830950240737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90212605582398196802567861 8457431773349830950240737)
        ·
          refine ⟨6343073830012373212680553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8457431773349830950240737 6343073830012373212680553)
          ·
            refine ⟨4757305372509279909510415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6343073830012373212680553 4757305372509279909510415)
            ·
              refine ⟨7135958058763919864265623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757305372509279909510415 7135958058763919864265623)
              ·
                refine ⟨10703937088145879796398435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7135958058763919864265623 10703937088145879796398435)
                ·
                  refine ⟨16055905632218819694597653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10703937088145879796398435 16055905632218819694597653)
                  ·
                    refine ⟨752620576510257173184265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16055905632218819694597653 752620576510257173184265)
                    ·
                      rfl

theorem cell22_2198585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_2198585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198585 prefixEnd_2198585 := by exact prefixLift 2198585
  have htrace : WordTrace (prefixWord ++ tailWord_2198585) baseStart_2198585 baseEnd_2198585 := by
    simpa [prefixWord, tailWord_2198585, baseEnd_2198585] using wordTrace_append hprefix tailTrace_2198585
  have hstable : (prefixWord ++ tailWord_2198585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198585).length < 2 ^ (prefixWord ++ tailWord_2198585).sum := by decide
  have hdescent : baseEnd_2198585 < baseStart_2198585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198621 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2198621 : Nat := 118140960795 + 2198621 * 2 ^ 59
def prefixEnd_2198621 : Nat := 4983230072969 + 3 ^ 40 * 2198621 * 2
def baseEnd_2198621 : Nat := 752632900045965079284155

theorem tailTrace_2198621 : CollatzResearch.WordTrace tailWord_2198621 prefixEnd_2198621 752632900045965079284155 := by
  unfold tailWord_2198621
  simp only [CollatzResearch.WordTrace]
  refine ⟨80190295767779086417259717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53460197178519390944839811 80190295767779086417259717)
  ·
    refine ⟨15035680456458578703236197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80190295767779086417259717 15035680456458578703236197)
    ·
      refine ⟨2819190085585983506856787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15035680456458578703236197 2819190085585983506856787)
      ·
        refine ⟨4228785128378975260285181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819190085585983506856787 4228785128378975260285181)
        ·
          refine ⟨1585794423142115722606943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4228785128378975260285181 1585794423142115722606943)
          ·
            refine ⟨2378691634713173583910415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585794423142115722606943 2378691634713173583910415)
            ·
              refine ⟨3568037452069760375865623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378691634713173583910415 3568037452069760375865623)
              ·
                refine ⟨5352056178104640563798435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3568037452069760375865623 5352056178104640563798435)
                ·
                  refine ⟨8028084267156960845697653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5352056178104640563798435 8028084267156960845697653)
                  ·
                    refine ⟨752632900045965079284155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8028084267156960845697653 752632900045965079284155)
                    ·
                      rfl

theorem cell22_2198621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2198621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198621 prefixEnd_2198621 := by exact prefixLift 2198621
  have htrace : WordTrace (prefixWord ++ tailWord_2198621) baseStart_2198621 baseEnd_2198621 := by
    simpa [prefixWord, tailWord_2198621, baseEnd_2198621] using wordTrace_append hprefix tailTrace_2198621
  have hstable : (prefixWord ++ tailWord_2198621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198621).length < 2 ^ (prefixWord ++ tailWord_2198621).sum := by decide
  have hdescent : baseEnd_2198621 < baseStart_2198621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198666 : List Nat := [3, 1, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_2198666 : Nat := 118140960795 + 2198666 * 2 ^ 59
def prefixEnd_2198666 : Nat := 4983230072969 + 3 ^ 40 * 2198666 * 2
def baseEnd_2198666 : Nat := 752648304465599961909017

theorem tailTrace_2198666 : CollatzResearch.WordTrace tailWord_2198666 prefixEnd_2198666 752648304465599961909017 := by
  unfold tailWord_2198666
  simp only [CollatzResearch.WordTrace]
  refine ⟨20047984263154014775661963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53461291368410706068431901 20047984263154014775661963)
  ·
    refine ⟨30071976394731022163492945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20047984263154014775661963 30071976394731022163492945)
    ·
      refine ⟨22553982296048266622619709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30071976394731022163492945 22553982296048266622619709)
      ·
        refine ⟨8457743361018099983482391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22553982296048266622619709 8457743361018099983482391)
        ·
          refine ⟨12686615041527149975223587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8457743361018099983482391 12686615041527149975223587)
          ·
            refine ⟨19029922562290724962835381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12686615041527149975223587 19029922562290724962835381)
            ·
              refine ⟨1784055240214755465265817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19029922562290724962835381 1784055240214755465265817)
              ·
                refine ⟨1338041430161066598949363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784055240214755465265817 1338041430161066598949363)
                ·
                  refine ⟨2007062145241599898424045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338041430161066598949363 2007062145241599898424045)
                  ·
                    refine ⟨752648304465599961909017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007062145241599898424045 752648304465599961909017)
                    ·
                      rfl

theorem cell22_2198666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_2198666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198666 prefixEnd_2198666 := by exact prefixLift 2198666
  have htrace : WordTrace (prefixWord ++ tailWord_2198666) baseStart_2198666 baseEnd_2198666 := by
    simpa [prefixWord, tailWord_2198666, baseEnd_2198666] using wordTrace_append hprefix tailTrace_2198666
  have hstable : (prefixWord ++ tailWord_2198666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198666).length < 2 ^ (prefixWord ++ tailWord_2198666).sum := by decide
  have hdescent : baseEnd_2198666 < baseStart_2198666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198679 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 5]
def baseStart_2198679 : Nat := 118140960795 + 2198679 * 2 ^ 59
def prefixEnd_2198679 : Nat := 4983230072969 + 3 ^ 40 * 2198679 * 2
def baseEnd_2198679 : Nat := 250884251543757420444659

theorem tailTrace_2198679 : CollatzResearch.WordTrace tailWord_2198679 prefixEnd_2198679 250884251543757420444659 := by
  unfold tailWord_2198679
  simp only [CollatzResearch.WordTrace]
  refine ⟨80192411201568962322871091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53461607467712641548580727 80192411201568962322871091)
  ·
    refine ⟨120288616802353443484306637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80192411201568962322871091 120288616802353443484306637)
    ·
      refine ⟨45108231300882541306614989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120288616802353443484306637 45108231300882541306614989)
      ·
        refine ⟨16915586737830952989980621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45108231300882541306614989 16915586737830952989980621)
        ·
          refine ⟨6343345026686607371242733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16915586737830952989980621 6343345026686607371242733)
          ·
            refine ⟨2378754385007477764216025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6343345026686607371242733 2378754385007477764216025)
            ·
              refine ⟨1784065788755608323162019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2378754385007477764216025 1784065788755608323162019)
              ·
                refine ⟨2676098683133412484743029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784065788755608323162019 2676098683133412484743029)
                ·
                  refine ⟨250884251543757420444659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2676098683133412484743029 250884251543757420444659)
                  ·
                    rfl

theorem cell22_2198679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 5].length) (baseStart_2198679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198679 prefixEnd_2198679 := by exact prefixLift 2198679
  have htrace : WordTrace (prefixWord ++ tailWord_2198679) baseStart_2198679 baseEnd_2198679 := by
    simpa [prefixWord, tailWord_2198679, baseEnd_2198679] using wordTrace_append hprefix tailTrace_2198679
  have hstable : (prefixWord ++ tailWord_2198679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198679).length < 2 ^ (prefixWord ++ tailWord_2198679).sum := by decide
  have hdescent : baseEnd_2198679 < baseStart_2198679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198692 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_2198692 : Nat := 118140960795 + 2198692 * 2 ^ 59
def prefixEnd_2198692 : Nat := 4983230072969 + 3 ^ 40 * 2198692 * 2
def baseEnd_2198692 : Nat := 752657204796944560758937

theorem tailTrace_2198692 : CollatzResearch.WordTrace tailWord_2198692 prefixEnd_2198692 752657204796944560758937 := by
  unfold tailWord_2198692
  simp only [CollatzResearch.WordTrace]
  refine ⟨40096442675260932771547165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53461923567014577028729553 40096442675260932771547165)
  ·
    refine ⟨15036166003222849789330187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40096442675260932771547165 15036166003222849789330187)
    ·
      refine ⟨22554249004834274683995281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15036166003222849789330187 22554249004834274683995281)
      ·
        refine ⟨16915686753625706012996461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22554249004834274683995281 16915686753625706012996461)
        ·
          refine ⟨6343382532609639754873673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16915686753625706012996461 6343382532609639754873673)
          ·
            refine ⟨4757536899457229816155255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6343382532609639754873673 4757536899457229816155255)
            ·
              refine ⟨7136305349185844724232883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757536899457229816155255 7136305349185844724232883)
              ·
                refine ⟨10704458023778767086349325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7136305349185844724232883 10704458023778767086349325)
                ·
                  refine ⟨4014171758917037657380997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10704458023778767086349325 4014171758917037657380997)
                  ·
                    refine ⟨752657204796944560758937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4014171758917037657380997 752657204796944560758937)
                    ·
                      rfl

theorem cell22_2198692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_2198692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198692 prefixEnd_2198692 := by exact prefixLift 2198692
  have htrace : WordTrace (prefixWord ++ tailWord_2198692) baseStart_2198692 baseEnd_2198692 := by
    simpa [prefixWord, tailWord_2198692, baseEnd_2198692] using wordTrace_append hprefix tailTrace_2198692
  have hstable : (prefixWord ++ tailWord_2198692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198692).length < 2 ^ (prefixWord ++ tailWord_2198692).sum := by decide
  have hdescent : baseEnd_2198692 < baseStart_2198692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198752 : List Nat := [2, 1, 1, 3, 1, 5, 3, 6]
def baseStart_2198752 : Nat := 118140960795 + 2198752 * 2 ^ 59
def prefixEnd_2198752 : Nat := 4983230072969 + 3 ^ 40 * 2198752 * 2
def baseEnd_2198752 : Nat := 83630860447013822695417

theorem tailTrace_2198752 : CollatzResearch.WordTrace tailWord_2198752 prefixEnd_2198752 83630860447013822695417 := by
  unfold tailWord_2198752
  simp only [CollatzResearch.WordTrace]
  refine ⟨40097536865152247895139255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53463382486869663860185673 40097536865152247895139255)
  ·
    refine ⟨60146305297728371842708883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40097536865152247895139255 60146305297728371842708883)
    ·
      refine ⟨90219457946592557764063325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60146305297728371842708883 90219457946592557764063325)
      ·
        refine ⟨33832296729972209161523747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90219457946592557764063325 33832296729972209161523747)
        ·
          refine ⟨50748445094958313742285621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33832296729972209161523747 50748445094958313742285621)
          ·
            refine ⟨4757666727652341913339277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50748445094958313742285621 4757666727652341913339277)
            ·
              refine ⟨1784125022869628217502229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4757666727652341913339277 1784125022869628217502229)
              ·
                refine ⟨83630860447013822695417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1784125022869628217502229 83630860447013822695417)
                ·
                  rfl

theorem cell22_2198752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 6].length) (baseStart_2198752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198752 prefixEnd_2198752 := by exact prefixLift 2198752
  have htrace : WordTrace (prefixWord ++ tailWord_2198752) baseStart_2198752 baseEnd_2198752 := by
    simpa [prefixWord, tailWord_2198752, baseEnd_2198752] using wordTrace_append hprefix tailTrace_2198752
  have hstable : (prefixWord ++ tailWord_2198752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198752).length < 2 ^ (prefixWord ++ tailWord_2198752).sum := by decide
  have hdescent : baseEnd_2198752 < baseStart_2198752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198887 : List Nat := [1, 1, 5, 1, 4, 10]
def baseStart_2198887 : Nat := 118140960795 + 2198887 * 2 ^ 59
def prefixEnd_2198887 : Nat := 4983230072969 + 3 ^ 40 * 2198887 * 2
def baseEnd_2198887 : Nat := 9292888361506531507819

theorem tailTrace_2198887 : CollatzResearch.WordTrace tailWord_2198887 prefixEnd_2198887 9292888361506531507819 := by
  unfold tailWord_2198887
  simp only [CollatzResearch.WordTrace]
  refine ⟨80199997584815413846442915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53466665056543609230961943 80199997584815413846442915)
  ·
    refine ⟨120299996377223120769664373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80199997584815413846442915 120299996377223120769664373)
    ·
      refine ⟨11278124660364667572156035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120299996377223120769664373 11278124660364667572156035)
      ·
        refine ⟨16917186990547001358234053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11278124660364667572156035 16917186990547001358234053)
        ·
          refine ⟨3171972560727562754668885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16917186990547001358234053 3171972560727562754668885)
          ·
            refine ⟨9292888361506531507819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3171972560727562754668885 9292888361506531507819)
            ·
              rfl

theorem cell22_2198887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 10].length) (baseStart_2198887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198887 prefixEnd_2198887 := by exact prefixLift 2198887
  have htrace : WordTrace (prefixWord ++ tailWord_2198887) baseStart_2198887 baseEnd_2198887 := by
    simpa [prefixWord, tailWord_2198887, baseEnd_2198887] using wordTrace_append hprefix tailTrace_2198887
  have hstable : (prefixWord ++ tailWord_2198887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198887).length < 2 ^ (prefixWord ++ tailWord_2198887).sum := by decide
  have hdescent : baseEnd_2198887 < baseStart_2198887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198893 : List Nat := [1, 5, 1, 1, 1, 5, 2, 2, 4]
def baseStart_2198893 : Nat := 118140960795 + 2198893 * 2 ^ 59
def prefixEnd_2198893 : Nat := 4983230072969 + 3 ^ 40 * 2198893 * 2
def baseEnd_2198893 : Nat := 250908670401549012161107

theorem tailTrace_2198893 : CollatzResearch.WordTrace tailWord_2198893 prefixEnd_2198893 250908670401549012161107 := by
  unfold tailWord_2198893
  simp only [CollatzResearch.WordTrace]
  refine ⟨80200216422793676871161333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53466810948529117914107555 80200216422793676871161333)
  ·
    refine ⟨7518770289636907206671375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80200216422793676871161333 7518770289636907206671375)
    ·
      refine ⟨11278155434455360810007063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7518770289636907206671375 11278155434455360810007063)
      ·
        refine ⟨16917233151683041215010595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11278155434455360810007063 16917233151683041215010595)
        ·
          refine ⟨25375849727524561822515893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16917233151683041215010595 25375849727524561822515893)
          ·
            refine ⟨2378985911955427670860865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25375849727524561822515893 2378985911955427670860865)
            ·
              refine ⟨1784239433966570753145649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2378985911955427670860865 1784239433966570753145649)
              ·
                refine ⟨1338179575474928064859237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784239433966570753145649 1338179575474928064859237)
                ·
                  refine ⟨250908670401549012161107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338179575474928064859237 250908670401549012161107)
                  ·
                    rfl

theorem cell22_2198893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_2198893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198893 prefixEnd_2198893 := by exact prefixLift 2198893
  have htrace : WordTrace (prefixWord ++ tailWord_2198893) baseStart_2198893 baseEnd_2198893 := by
    simpa [prefixWord, tailWord_2198893, baseEnd_2198893] using wordTrace_append hprefix tailTrace_2198893
  have hstable : (prefixWord ++ tailWord_2198893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198893).length < 2 ^ (prefixWord ++ tailWord_2198893).sum := by decide
  have hdescent : baseEnd_2198893 < baseStart_2198893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198919 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 5, 3]
def baseStart_2198919 : Nat := 118140960795 + 2198919 * 2 ^ 59
def prefixEnd_2198919 : Nat := 4983230072969 + 3 ^ 40 * 2198919 * 2
def baseEnd_2198919 : Nat := 752734911535991635333241

theorem tailTrace_2198919 : CollatzResearch.WordTrace tailWord_2198919 prefixEnd_2198919 752734911535991635333241 := by
  unfold tailWord_2198919
  simp only [CollatzResearch.WordTrace]
  refine ⟨80201164720699483311607811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53467443147132988874405207 80201164720699483311607811)
  ·
    refine ⟨120301747081049224967411717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80201164720699483311607811 120301747081049224967411717)
    ·
      refine ⟨22556577577696729681389697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120301747081049224967411717 22556577577696729681389697)
      ·
        refine ⟨16917433183272547261042273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22556577577696729681389697 16917433183272547261042273)
        ·
          refine ⟨12688074887454410445781705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16917433183272547261042273 12688074887454410445781705)
          ·
            refine ⟨9516056165590807834336279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12688074887454410445781705 9516056165590807834336279)
            ·
              refine ⟨14274084248386211751504419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9516056165590807834336279 14274084248386211751504419)
              ·
                refine ⟨21411126372579317627256629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14274084248386211751504419 21411126372579317627256629)
                ·
                  refine ⟨2007293097429311027555309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21411126372579317627256629 2007293097429311027555309)
                  ·
                    refine ⟨752734911535991635333241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007293097429311027555309 752734911535991635333241)
                    ·
                      rfl

theorem cell22_2198919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_2198919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198919 prefixEnd_2198919 := by exact prefixLift 2198919
  have htrace : WordTrace (prefixWord ++ tailWord_2198919) baseStart_2198919 baseEnd_2198919 := by
    simpa [prefixWord, tailWord_2198919, baseEnd_2198919] using wordTrace_append hprefix tailTrace_2198919
  have hstable : (prefixWord ++ tailWord_2198919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198919).length < 2 ^ (prefixWord ++ tailWord_2198919).sum := by decide
  have hdescent : baseEnd_2198919 < baseStart_2198919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198942 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2198942 : Nat := 118140960795 + 2198942 * 2 ^ 59
def prefixEnd_2198942 : Nat := 4983230072969 + 3 ^ 40 * 2198942 * 2
def baseEnd_2198942 : Nat := 752742784906027242008171

theorem tailTrace_2198942 : CollatzResearch.WordTrace tailWord_2198942 prefixEnd_2198942 752742784906027242008171 := by
  unfold tailWord_2198942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10025250449952019779961885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53468002399744105493130053 10025250449952019779961885)
  ·
    refine ⟨3759468918732007417485707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10025250449952019779961885 3759468918732007417485707)
    ·
      refine ⟨5639203378098011126228561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3759468918732007417485707 5639203378098011126228561)
      ·
        refine ⟨4229402533573508344671421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5639203378098011126228561 4229402533573508344671421)
        ·
          refine ⟨1586025950090065629251783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4229402533573508344671421 1586025950090065629251783)
          ·
            refine ⟨2379038925135098443877675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586025950090065629251783 2379038925135098443877675)
            ·
              refine ⟨3568558387702647665816513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2379038925135098443877675 3568558387702647665816513)
              ·
                refine ⟨2676418790776985749362385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3568558387702647665816513 2676418790776985749362385)
                ·
                  refine ⟨2007314093082739312021789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2676418790776985749362385 2007314093082739312021789)
                  ·
                    refine ⟨752742784906027242008171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007314093082739312021789 752742784906027242008171)
                    ·
                      rfl

theorem cell22_2198942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2198942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198942 prefixEnd_2198942 := by exact prefixLift 2198942
  have htrace : WordTrace (prefixWord ++ tailWord_2198942) baseStart_2198942 baseEnd_2198942 := by
    simpa [prefixWord, tailWord_2198942, baseEnd_2198942] using wordTrace_append hprefix tailTrace_2198942
  have hstable : (prefixWord ++ tailWord_2198942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198942).length < 2 ^ (prefixWord ++ tailWord_2198942).sum := by decide
  have hdescent : baseEnd_2198942 < baseStart_2198942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198947 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 4, 5]
def baseStart_2198947 : Nat := 118140960795 + 2198947 * 2 ^ 59
def prefixEnd_2198947 : Nat := 4983230072969 + 3 ^ 40 * 2198947 * 2
def baseEnd_2198947 : Nat := 752744496508208895633155

theorem tailTrace_2198947 : CollatzResearch.WordTrace tailWord_2198947 prefixEnd_2198947 752744496508208895633155 := by
  unfold tailWord_2198947
  simp only [CollatzResearch.WordTrace]
  refine ⟨80202185964598044093627095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53468123976398696062418063 80202185964598044093627095)
  ·
    refine ⟨120303278946897066140440643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80202185964598044093627095 120303278946897066140440643)
    ·
      refine ⟨180454918420345599210660965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120303278946897066140440643 180454918420345599210660965)
      ·
        refine ⟨33835297203814799851998931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180454918420345599210660965 33835297203814799851998931)
        ·
          refine ⟨50752945805722199777998397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33835297203814799851998931 50752945805722199777998397)
          ·
            refine ⟨19032354677145824916749399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50752945805722199777998397 19032354677145824916749399)
            ·
              refine ⟨28548532015718737375124099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19032354677145824916749399 28548532015718737375124099)
              ·
                refine ⟨42822798023578106062686149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28548532015718737375124099 42822798023578106062686149)
                ·
                  refine ⟨8029274629420894886753653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42822798023578106062686149 8029274629420894886753653)
                  ·
                    refine ⟨752744496508208895633155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8029274629420894886753653 752744496508208895633155)
                    ·
                      rfl

theorem cell22_2198947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_2198947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198947 prefixEnd_2198947 := by exact prefixLift 2198947
  have htrace : WordTrace (prefixWord ++ tailWord_2198947) baseStart_2198947 baseEnd_2198947 := by
    simpa [prefixWord, tailWord_2198947, baseEnd_2198947] using wordTrace_append hprefix tailTrace_2198947
  have hstable : (prefixWord ++ tailWord_2198947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198947).length < 2 ^ (prefixWord ++ tailWord_2198947).sum := by decide
  have hdescent : baseEnd_2198947 < baseStart_2198947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198962 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_2198962 : Nat := 118140960795 + 2198962 * 2 ^ 59
def prefixEnd_2198962 : Nat := 4983230072969 + 3 ^ 40 * 2198962 * 2
def baseEnd_2198962 : Nat := 752749631314753856508109

theorem tailTrace_2198962 : CollatzResearch.WordTrace tailWord_2198962 prefixEnd_2198962 752749631314753856508109 := by
  unfold tailWord_2198962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20050683264885925413855785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53468488706362467770282093 20050683264885925413855785)
  ·
    refine ⟨15038012448664444060391839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20050683264885925413855785 15038012448664444060391839)
    ·
      refine ⟨22557018672996666090587759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15038012448664444060391839 22557018672996666090587759)
      ·
        refine ⟨33835528009494999135881639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22557018672996666090587759 33835528009494999135881639)
        ·
          refine ⟨50753292014242498703822459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33835528009494999135881639 50753292014242498703822459)
          ·
            refine ⟨76129938021363748055733689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50753292014242498703822459 76129938021363748055733689)
            ·
              refine ⟨57097453516022811041800267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76129938021363748055733689 57097453516022811041800267)
              ·
                refine ⟨85646180274034216562700401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57097453516022811041800267 85646180274034216562700401)
                ·
                  refine ⟨64234635205525662422025301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85646180274034216562700401 64234635205525662422025301)
                  ·
                    refine ⟨752749631314753856508109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64234635205525662422025301 752749631314753856508109)
                    ·
                      rfl

theorem cell22_2198962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_2198962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198962 prefixEnd_2198962 := by exact prefixLift 2198962
  have htrace : WordTrace (prefixWord ++ tailWord_2198962) baseStart_2198962 baseEnd_2198962 := by
    simpa [prefixWord, tailWord_2198962, baseEnd_2198962] using wordTrace_append hprefix tailTrace_2198962
  have hstable : (prefixWord ++ tailWord_2198962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198962).length < 2 ^ (prefixWord ++ tailWord_2198962).sum := by decide
  have hdescent : baseEnd_2198962 < baseStart_2198962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198979 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 1, 4]
def baseStart_2198979 : Nat := 118140960795 + 2198979 * 2 ^ 59
def prefixEnd_2198979 : Nat := 4983230072969 + 3 ^ 40 * 2198979 * 2
def baseEnd_2198979 : Nat := 752755450762171478833057

theorem tailTrace_2198979 : CollatzResearch.WordTrace tailWord_2198979 prefixEnd_2198979 752755450762171478833057 := by
  unfold tailWord_2198979
  simp only [CollatzResearch.WordTrace]
  refine ⟨80203353100482113558791991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53468902066988075705861327 80203353100482113558791991)
  ·
    refine ⟨120305029650723170338187987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80203353100482113558791991 120305029650723170338187987)
    ·
      refine ⟨180457544476084755507281981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120305029650723170338187987 180457544476084755507281981)
      ·
        refine ⟨67671579178531783315230743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180457544476084755507281981 67671579178531783315230743)
        ·
          refine ⟨101507368767797674972846115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67671579178531783315230743 101507368767797674972846115)
          ·
            refine ⟨152261053151696512459269173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101507368767797674972846115 152261053151696512459269173)
            ·
              refine ⟨14274473732971548043056485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152261053151696512459269173 14274473732971548043056485)
              ·
                refine ⟨2676463824932165258073091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14274473732971548043056485 2676463824932165258073091)
                ·
                  refine ⟨4014695737398247887109637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676463824932165258073091 4014695737398247887109637)
                  ·
                    refine ⟨752755450762171478833057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4014695737398247887109637 752755450762171478833057)
                    ·
                      rfl

theorem cell22_2198979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 4].length) (baseStart_2198979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2198979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2198979 prefixEnd_2198979 := by exact prefixLift 2198979
  have htrace : WordTrace (prefixWord ++ tailWord_2198979) baseStart_2198979 baseEnd_2198979 := by
    simpa [prefixWord, tailWord_2198979, baseEnd_2198979] using wordTrace_append hprefix tailTrace_2198979
  have hstable : (prefixWord ++ tailWord_2198979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198979).length < 2 ^ (prefixWord ++ tailWord_2198979).sum := by decide
  have hdescent : baseEnd_2198979 < baseStart_2198979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199011 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 6]
def baseStart_2199011 : Nat := 118140960795 + 2199011 * 2 ^ 59
def prefixEnd_2199011 : Nat := 4983230072969 + 3 ^ 40 * 2199011 * 2
def baseEnd_2199011 : Nat := 250922135005378020677653

theorem tailTrace_2199011 : CollatzResearch.WordTrace tailWord_2199011 prefixEnd_2199011 250922135005378020677653 := by
  unfold tailWord_2199011
  simp only [CollatzResearch.WordTrace]
  refine ⟨80204520236366183023956887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53469680157577455349304591 80204520236366183023956887)
  ·
    refine ⟨120306780354549274535935331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80204520236366183023956887 120306780354549274535935331)
    ·
      refine ⟨180460170531823911803902997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120306780354549274535935331 180460170531823911803902997)
      ·
        refine ⟨8459070493679245865807953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 180460170531823911803902997 8459070493679245865807953)
        ·
          refine ⟨6344302870259434399355965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8459070493679245865807953 6344302870259434399355965)
          ·
            refine ⟨2379113576347287899758487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6344302870259434399355965 2379113576347287899758487)
            ·
              refine ⟨3568670364520931849637731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2379113576347287899758487 3568670364520931849637731)
              ·
                refine ⟨5353005546781397774456597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3568670364520931849637731 5353005546781397774456597)
                ·
                  refine ⟨250922135005378020677653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5353005546781397774456597 250922135005378020677653)
                  ·
                    rfl

theorem cell22_2199011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 6].length) (baseStart_2199011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199011 prefixEnd_2199011 := by exact prefixLift 2199011
  have htrace : WordTrace (prefixWord ++ tailWord_2199011) baseStart_2199011 baseEnd_2199011 := by
    simpa [prefixWord, tailWord_2199011, baseEnd_2199011] using wordTrace_append hprefix tailTrace_2199011
  have hstable : (prefixWord ++ tailWord_2199011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199011).length < 2 ^ (prefixWord ++ tailWord_2199011).sum := by decide
  have hdescent : baseEnd_2199011 < baseStart_2199011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199069 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2199069 : Nat := 118140960795 + 2199069 * 2 ^ 59
def prefixEnd_2199069 : Nat := 4983230072969 + 3 ^ 40 * 2199069 * 2
def baseEnd_2199069 : Nat := 752786259601441244082781

theorem tailTrace_2199069 : CollatzResearch.WordTrace tailWord_2199069 prefixEnd_2199069 752786259601441244082781 := by
  unfold tailWord_2199069
  simp only [CollatzResearch.WordTrace]
  refine ⟨80206635670156058929568261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53471090446770705953045507 80206635670156058929568261)
  ·
    refine ⟨15038744188154261049294049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80206635670156058929568261 15038744188154261049294049)
    ·
      refine ⟨11279058141115695786970537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15038744188154261049294049 11279058141115695786970537)
      ·
        refine ⟨8459293605836771840227903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11279058141115695786970537 8459293605836771840227903)
        ·
          refine ⟨12688940408755157760341855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8459293605836771840227903 12688940408755157760341855)
          ·
            refine ⟨19033410613132736640512783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12688940408755157760341855 19033410613132736640512783)
            ·
              refine ⟨28550115919699104960769175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19033410613132736640512783 28550115919699104960769175)
              ·
                refine ⟨42825173879548657441153763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28550115919699104960769175 42825173879548657441153763)
                ·
                  refine ⟨64237760819322986161730645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42825173879548657441153763 64237760819322986161730645)
                  ·
                    refine ⟨752786259601441244082781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64237760819322986161730645 752786259601441244082781)
                    ·
                      rfl

theorem cell22_2199069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2199069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199069 prefixEnd_2199069 := by exact prefixLift 2199069
  have htrace : WordTrace (prefixWord ++ tailWord_2199069) baseStart_2199069 baseEnd_2199069 := by
    simpa [prefixWord, tailWord_2199069, baseEnd_2199069] using wordTrace_append hprefix tailTrace_2199069
  have hstable : (prefixWord ++ tailWord_2199069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199069).length < 2 ^ (prefixWord ++ tailWord_2199069).sum := by decide
  have hdescent : baseEnd_2199069 < baseStart_2199069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199105 : List Nat := [1, 2, 5, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2199105 : Nat := 118140960795 + 2199105 * 2 ^ 59
def prefixEnd_2199105 : Nat := 4983230072969 + 3 ^ 40 * 2199105 * 2
def baseEnd_2199105 : Nat := 752798583137149150182671

theorem tailTrace_2199105 : CollatzResearch.WordTrace tailWord_2199105 prefixEnd_2199105 752798583137149150182671 := by
  unfold tailWord_2199105
  simp only [CollatzResearch.WordTrace]
  refine ⟨80207948698025637077878769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53471965798683758051919179 80207948698025637077878769)
  ·
    refine ⟨60155961523519227808409077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80207948698025637077878769 60155961523519227808409077)
    ·
      refine ⟨5639621392829927607038351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60155961523519227808409077 5639621392829927607038351)
      ·
        refine ⟨8459432089244891410557527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5639621392829927607038351 8459432089244891410557527)
        ·
          refine ⟨12689148133867337115836291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8459432089244891410557527 12689148133867337115836291)
          ·
            refine ⟨19033722200801005673754437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12689148133867337115836291 19033722200801005673754437)
            ·
              refine ⟨3568822912650188563828957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19033722200801005673754437 3568822912650188563828957)
              ·
                refine ⟨1338308592243820711435859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3568822912650188563828957 1338308592243820711435859)
                ·
                  refine ⟨2007462888365731067153789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338308592243820711435859 2007462888365731067153789)
                  ·
                    refine ⟨752798583137149150182671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007462888365731067153789 752798583137149150182671)
                    ·
                      rfl

theorem cell22_2199105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2199105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199105 prefixEnd_2199105 := by exact prefixLift 2199105
  have htrace : WordTrace (prefixWord ++ tailWord_2199105) baseStart_2199105 baseEnd_2199105 := by
    simpa [prefixWord, tailWord_2199105, baseEnd_2199105] using wordTrace_append hprefix tailTrace_2199105
  have hstable : (prefixWord ++ tailWord_2199105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199105).length < 2 ^ (prefixWord ++ tailWord_2199105).sum := by decide
  have hdescent : baseEnd_2199105 < baseStart_2199105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199146 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_2199146 : Nat := 118140960795 + 2199146 * 2 ^ 59
def prefixEnd_2199146 : Nat := 4983230072969 + 3 ^ 40 * 2199146 * 2
def baseEnd_2199146 : Nat := 250937539425012903302515

theorem tailTrace_2199146 : CollatzResearch.WordTrace tailWord_2199146 prefixEnd_2199146 250937539425012903302515 := by
  unfold tailWord_2199146
  simp only [CollatzResearch.WordTrace]
  refine ⟨20052361022719275270030323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53472962727251400720080861 20052361022719275270030323)
  ·
    refine ⟨30078541534078912905045485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20052361022719275270030323 30078541534078912905045485)
    ·
      refine ⟨11279453075279592339392057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30078541534078912905045485 11279453075279592339392057)
      ·
        refine ⟨8459589806459694254544043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11279453075279592339392057 8459589806459694254544043)
        ·
          refine ⟨12689384709689541381816065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8459589806459694254544043 12689384709689541381816065)
          ·
            refine ⟨9517038532267156036362049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12689384709689541381816065 9517038532267156036362049)
            ·
              refine ⟨7137778899200367027271537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9517038532267156036362049 7137778899200367027271537)
              ·
                refine ⟨5353334174400275270453653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7137778899200367027271537 5353334174400275270453653)
                ·
                  refine ⟨250937539425012903302515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5353334174400275270453653 250937539425012903302515)
                  ·
                    rfl

theorem cell22_2199146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_2199146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199146 prefixEnd_2199146 := by exact prefixLift 2199146
  have htrace : WordTrace (prefixWord ++ tailWord_2199146) baseStart_2199146 baseEnd_2199146 := by
    simpa [prefixWord, tailWord_2199146, baseEnd_2199146] using wordTrace_append hprefix tailTrace_2199146
  have hstable : (prefixWord ++ tailWord_2199146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199146).length < 2 ^ (prefixWord ++ tailWord_2199146).sum := by decide
  have hdescent : baseEnd_2199146 < baseStart_2199146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199161 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 6, 3]
def baseStart_2199161 : Nat := 118140960795 + 2199161 * 2 ^ 59
def prefixEnd_2199161 : Nat := 4983230072969 + 3 ^ 40 * 2199161 * 2
def baseEnd_2199161 : Nat := 752817753081583670782499

theorem tailTrace_2199161 : CollatzResearch.WordTrace tailWord_2199161 prefixEnd_2199161 752817753081583670782499 := by
  unfold tailWord_2199161
  simp only [CollatzResearch.WordTrace]
  refine ⟨80209991185822758641917337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53473327457215172427944891 80209991185822758641917337)
  ·
    refine ⟨60157493389367068981438003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80209991185822758641917337 60157493389367068981438003)
    ·
      refine ⟨90236240084050603472157005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60157493389367068981438003 90236240084050603472157005)
      ·
        refine ⟨33838590031518976302058877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90236240084050603472157005 33838590031518976302058877)
        ·
          refine ⟨12689471261819616113272079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33838590031518976302058877 12689471261819616113272079)
          ·
            refine ⟨19034206892729424169908119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12689471261819616113272079 19034206892729424169908119)
            ·
              refine ⟨28551310339094136254862179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19034206892729424169908119 28551310339094136254862179)
              ·
                refine ⟨42826965508641204382293269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28551310339094136254862179 42826965508641204382293269)
                ·
                  refine ⟨2007514008217556455419997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42826965508641204382293269 2007514008217556455419997)
                  ·
                    refine ⟨752817753081583670782499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007514008217556455419997 752817753081583670782499)
                    ·
                      rfl

theorem cell22_2199161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_2199161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199161 prefixEnd_2199161 := by exact prefixLift 2199161
  have htrace : WordTrace (prefixWord ++ tailWord_2199161) baseStart_2199161 baseEnd_2199161 := by
    simpa [prefixWord, tailWord_2199161, baseEnd_2199161] using wordTrace_append hprefix tailTrace_2199161
  have hstable : (prefixWord ++ tailWord_2199161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199161).length < 2 ^ (prefixWord ++ tailWord_2199161).sum := by decide
  have hdescent : baseEnd_2199161 < baseStart_2199161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199178 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_2199178 : Nat := 118140960795 + 2199178 * 2 ^ 59
def prefixEnd_2199178 : Nat := 4983230072969 + 3 ^ 40 * 2199178 * 2
def baseEnd_2199178 : Nat := 752823572529001293107447

theorem tailTrace_2199178 : CollatzResearch.WordTrace tailWord_2199178 prefixEnd_2199178 752823572529001293107447 := by
  unfold tailWord_2199178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20052652806690292636321547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53473740817840780363524125 20052652806690292636321547)
  ·
    refine ⟨30078979210035438954482321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20052652806690292636321547 30078979210035438954482321)
    ·
      refine ⟨22559234407526579215861741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30078979210035438954482321 22559234407526579215861741)
      ·
        refine ⟨8459712902822467205948153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22559234407526579215861741 8459712902822467205948153)
        ·
          refine ⟨6344784677116850404461115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8459712902822467205948153 6344784677116850404461115)
          ·
            refine ⟨9517177015675275606691673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6344784677116850404461115 9517177015675275606691673)
            ·
              refine ⟨7137882761756456705018755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9517177015675275606691673 7137882761756456705018755)
              ·
                refine ⟨10706824142634685057528133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7137882761756456705018755 10706824142634685057528133)
                ·
                  refine ⟨2007529526744003448286525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10706824142634685057528133 2007529526744003448286525)
                  ·
                    refine ⟨752823572529001293107447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007529526744003448286525 752823572529001293107447)
                    ·
                      rfl

theorem cell22_2199178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_2199178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199178 prefixEnd_2199178 := by exact prefixLift 2199178
  have htrace : WordTrace (prefixWord ++ tailWord_2199178) baseStart_2199178 baseEnd_2199178 := by
    simpa [prefixWord, tailWord_2199178, baseEnd_2199178] using wordTrace_append hprefix tailTrace_2199178
  have hstable : (prefixWord ++ tailWord_2199178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199178).length < 2 ^ (prefixWord ++ tailWord_2199178).sum := by decide
  have hdescent : baseEnd_2199178 < baseStart_2199178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199191 : List Nat := [1, 1, 3, 3, 2, 3, 2, 7]
def baseStart_2199191 : Nat := 118140960795 + 2199191 * 2 ^ 59
def prefixEnd_2199191 : Nat := 4983230072969 + 3 ^ 40 * 2199191 * 2
def baseEnd_2199191 : Nat := 83647558077185954725823

theorem tailTrace_2199191 : CollatzResearch.WordTrace tailWord_2199191 prefixEnd_2199191 83647558077185954725823 := by
  unfold tailWord_2199191
  simp only [CollatzResearch.WordTrace]
  refine ⟨80211085375714073765509427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53474056917142715843672951 80211085375714073765509427)
  ·
    refine ⟨120316628063571110648264141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80211085375714073765509427 120316628063571110648264141)
    ·
      refine ⟨45118735523839166493099053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120316628063571110648264141 45118735523839166493099053)
      ·
        refine ⟨16919525821439687434912145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45118735523839166493099053 16919525821439687434912145)
        ·
          refine ⟨12689644366079765576184109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16919525821439687434912145 12689644366079765576184109)
          ·
            refine ⟨4758616637279912091069041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12689644366079765576184109 4758616637279912091069041)
            ·
              refine ⟨3568962477959934068301781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4758616637279912091069041 3568962477959934068301781)
              ·
                refine ⟨83647558077185954725823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3568962477959934068301781 83647558077185954725823)
                ·
                  rfl

theorem cell22_2199191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 7].length) (baseStart_2199191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199191 prefixEnd_2199191 := by exact prefixLift 2199191
  have htrace : WordTrace (prefixWord ++ tailWord_2199191) baseStart_2199191 baseEnd_2199191 := by
    simpa [prefixWord, tailWord_2199191, baseEnd_2199191] using wordTrace_append hprefix tailTrace_2199191
  have hstable : (prefixWord ++ tailWord_2199191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199191).length < 2 ^ (prefixWord ++ tailWord_2199191).sum := by decide
  have hdescent : baseEnd_2199191 < baseStart_2199191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199240 : List Nat := [2, 1, 3, 1, 2, 2, 3, 4, 1, 3]
def baseStart_2199240 : Nat := 118140960795 + 2199240 * 2 ^ 59
def prefixEnd_2199240 : Nat := 4983230072969 + 3 ^ 40 * 2199240 * 2
def baseEnd_2199240 : Nat := 752844796396053798057257

theorem tailTrace_2199240 : CollatzResearch.WordTrace tailWord_2199240 prefixEnd_2199240 752844796396053798057257 := by
  unfold tailWord_2199240
  simp only [CollatzResearch.WordTrace]
  refine ⟨40106436276268277567021587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53475248368357703422695449 40106436276268277567021587)
  ·
    refine ⟨60159654414402416350532381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40106436276268277567021587 60159654414402416350532381)
    ·
      refine ⟨22559870405400906131449643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60159654414402416350532381 22559870405400906131449643)
      ·
        refine ⟨33839805608101359197174465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22559870405400906131449643 33839805608101359197174465)
        ·
          refine ⟨25379854206076019397880849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33839805608101359197174465 25379854206076019397880849)
          ·
            refine ⟨19034890654557014548410637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25379854206076019397880849 19034890654557014548410637)
            ·
              refine ⟨7138083995458880455653989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19034890654557014548410637 7138083995458880455653989)
              ·
                refine ⟨1338390749148540085435123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7138083995458880455653989 1338390749148540085435123)
                ·
                  refine ⟨2007586123722810128152685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338390749148540085435123 2007586123722810128152685)
                  ·
                    refine ⟨752844796396053798057257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007586123722810128152685 752844796396053798057257)
                    ·
                      rfl

theorem cell22_2199240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_2199240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199240 prefixEnd_2199240 := by exact prefixLift 2199240
  have htrace : WordTrace (prefixWord ++ tailWord_2199240) baseStart_2199240 baseEnd_2199240 := by
    simpa [prefixWord, tailWord_2199240, baseEnd_2199240] using wordTrace_append hprefix tailTrace_2199240
  have hstable : (prefixWord ++ tailWord_2199240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199240).length < 2 ^ (prefixWord ++ tailWord_2199240).sum := by decide
  have hdescent : baseEnd_2199240 < baseStart_2199240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199311 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 6, 4]
def baseStart_2199311 : Nat := 118140960795 + 2199311 * 2 ^ 59
def prefixEnd_2199311 : Nat := 4983230072969 + 3 ^ 40 * 2199311 * 2
def baseEnd_2199311 : Nat := 752869101147033279532039

theorem tailTrace_2199311 : CollatzResearch.WordTrace tailWord_2199311 prefixEnd_2199311 752869101147033279532039 := by
  unfold tailWord_2199311
  simp only [CollatzResearch.WordTrace]
  refine ⟨80215462135279334259877787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53476974756852889506585191 80215462135279334259877787)
  ·
    refine ⟨120323193202919001389816681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80215462135279334259877787 120323193202919001389816681)
    ·
      refine ⟨90242394902189251042362511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120323193202919001389816681 90242394902189251042362511)
      ·
        refine ⟨135363592353283876563543767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90242394902189251042362511 135363592353283876563543767)
        ·
          refine ⟨203045388529925814845315651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135363592353283876563543767 203045388529925814845315651)
          ·
            refine ⟨304568082794888722267973477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203045388529925814845315651 304568082794888722267973477)
            ·
              refine ⟨57106515524041635425245027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304568082794888722267973477 57106515524041635425245027)
              ·
                refine ⟨85659773286062453137867541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57106515524041635425245027 85659773286062453137867541)
                ·
                  refine ⟨4015301872784177490837541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85659773286062453137867541 4015301872784177490837541)
                  ·
                    refine ⟨752869101147033279532039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4015301872784177490837541 752869101147033279532039)
                    ·
                      rfl

theorem cell22_2199311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_2199311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199311 prefixEnd_2199311 := by exact prefixLift 2199311
  have htrace : WordTrace (prefixWord ++ tailWord_2199311) baseStart_2199311 baseEnd_2199311 := by
    simpa [prefixWord, tailWord_2199311, baseEnd_2199311] using wordTrace_append hprefix tailTrace_2199311
  have hstable : (prefixWord ++ tailWord_2199311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199311).length < 2 ^ (prefixWord ++ tailWord_2199311).sum := by decide
  have hdescent : baseEnd_2199311 < baseStart_2199311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199328 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_2199328 : Nat := 118140960795 + 2199328 * 2 ^ 59
def prefixEnd_2199328 : Nat := 4983230072969 + 3 ^ 40 * 2199328 * 2
def baseEnd_2199328 : Nat := 752874920594450901856987

theorem tailTrace_2199328 : CollatzResearch.WordTrace tailWord_2199328 prefixEnd_2199328 752874920594450901856987 := by
  unfold tailWord_2199328
  simp only [CollatzResearch.WordTrace]
  refine ⟨40108041088108873081623319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53477388117478497442164425 40108041088108873081623319)
  ·
    refine ⟨60162061632163309622434979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40108041088108873081623319 60162061632163309622434979)
    ·
      refine ⟨90243092448244964433652469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60162061632163309622434979 90243092448244964433652469)
      ·
        refine ⟨8460289917022965415654919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90243092448244964433652469 8460289917022965415654919)
        ·
          refine ⟨12690434875534448123482379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8460289917022965415654919 12690434875534448123482379)
          ·
            refine ⟨19035652313301672185223569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12690434875534448123482379 19035652313301672185223569)
            ·
              refine ⟨14276739234976254138917677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19035652313301672185223569 14276739234976254138917677)
              ·
                refine ⟨5353777213116095302094129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14276739234976254138917677 5353777213116095302094129)
                ·
                  refine ⟨4015332909837071476570597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5353777213116095302094129 4015332909837071476570597)
                  ·
                    refine ⟨752874920594450901856987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4015332909837071476570597 752874920594450901856987)
                    ·
                      rfl

theorem cell22_2199328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_2199328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199328 prefixEnd_2199328 := by exact prefixLift 2199328
  have htrace : WordTrace (prefixWord ++ tailWord_2199328) baseStart_2199328 baseEnd_2199328 := by
    simpa [prefixWord, tailWord_2199328, baseEnd_2199328] using wordTrace_append hprefix tailTrace_2199328
  have hstable : (prefixWord ++ tailWord_2199328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199328).length < 2 ^ (prefixWord ++ tailWord_2199328).sum := by decide
  have hdescent : baseEnd_2199328 < baseStart_2199328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199332 : List Nat := [2, 3, 1, 3, 2, 3, 1, 3, 4]
def baseStart_2199332 : Nat := 118140960795 + 2199332 * 2 ^ 59
def prefixEnd_2199332 : Nat := 4983230072969 + 3 ^ 40 * 2199332 * 2
def baseEnd_2199332 : Nat := 250958763292065408252325

theorem tailTrace_2199332 : CollatzResearch.WordTrace tailWord_2199332 prefixEnd_2199332 250958763292065408252325 := by
  unfold tailWord_2199332
  simp only [CollatzResearch.WordTrace]
  refine ⟨40108114034101627423196125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53477485378802169897594833 40108114034101627423196125)
  ·
    refine ⟨15040542762788110283698547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40108114034101627423196125 15040542762788110283698547)
    ·
      refine ⟨22560814144182165425547821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15040542762788110283698547 22560814144182165425547821)
      ·
        refine ⟨8460305304068312034580433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22560814144182165425547821 8460305304068312034580433)
        ·
          refine ⟨6345228978051234025935325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8460305304068312034580433 6345228978051234025935325)
          ·
            refine ⟨2379460866769212759725747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6345228978051234025935325 2379460866769212759725747)
            ·
              refine ⟨3569191300153819139588621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2379460866769212759725747 3569191300153819139588621)
              ·
                refine ⟨1338446737557682177345733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3569191300153819139588621 1338446737557682177345733)
                ·
                  refine ⟨250958763292065408252325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338446737557682177345733 250958763292065408252325)
                  ·
                    rfl

theorem cell22_2199332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_2199332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199332 prefixEnd_2199332 := by exact prefixLift 2199332
  have htrace : WordTrace (prefixWord ++ tailWord_2199332) baseStart_2199332 baseEnd_2199332 := by
    simpa [prefixWord, tailWord_2199332, baseEnd_2199332] using wordTrace_append hprefix tailTrace_2199332
  have hstable : (prefixWord ++ tailWord_2199332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199332).length < 2 ^ (prefixWord ++ tailWord_2199332).sum := by decide
  have hdescent : baseEnd_2199332 < baseStart_2199332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199418 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_2199418 : Nat := 118140960795 + 2199418 * 2 ^ 59
def prefixEnd_2199418 : Nat := 4983230072969 + 3 ^ 40 * 2199418 * 2
def baseEnd_2199418 : Nat := 752905729433720667106711

theorem tailTrace_2199418 : CollatzResearch.WordTrace tailWord_2199418 prefixEnd_2199418 752905729433720667106711 := by
  unfold tailWord_2199418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20054841186472922883505727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53479576497261127689348605 20054841186472922883505727)
  ·
    refine ⟨30082261779709384325258591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20054841186472922883505727 30082261779709384325258591)
    ·
      refine ⟨45123392669564076487887887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30082261779709384325258591 45123392669564076487887887)
      ·
        refine ⟨67685089004346114731831831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45123392669564076487887887 67685089004346114731831831)
        ·
          refine ⟨101527633506519172097747747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67685089004346114731831831 101527633506519172097747747)
          ·
            refine ⟨152291450259778758146621621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101527633506519172097747747 152291450259778758146621621)
            ·
              refine ⟨14277323461854258576245777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152291450259778758146621621 14277323461854258576245777)
              ·
                refine ⟨10707992596390693932184333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14277323461854258576245777 10707992596390693932184333)
                ·
                  refine ⟨4015497223646510224569125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10707992596390693932184333 4015497223646510224569125)
                  ·
                    refine ⟨752905729433720667106711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4015497223646510224569125 752905729433720667106711)
                    ·
                      rfl

theorem cell22_2199418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_2199418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199418 prefixEnd_2199418 := by exact prefixLift 2199418
  have htrace : WordTrace (prefixWord ++ tailWord_2199418) baseStart_2199418 baseEnd_2199418 := by
    simpa [prefixWord, tailWord_2199418, baseEnd_2199418] using wordTrace_append hprefix tailTrace_2199418
  have hstable : (prefixWord ++ tailWord_2199418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199418).length < 2 ^ (prefixWord ++ tailWord_2199418).sum := by decide
  have hdescent : baseEnd_2199418 < baseStart_2199418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199422 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2199422 : Nat := 118140960795 + 2199422 * 2 ^ 59
def prefixEnd_2199422 : Nat := 4983230072969 + 3 ^ 40 * 2199422 * 2
def baseEnd_2199422 : Nat := 250969032905155330002233

theorem tailTrace_2199422 : CollatzResearch.WordTrace tailWord_2199422 prefixEnd_2199422 250969032905155330002233 := by
  unfold tailWord_2199422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027438829734650027146065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53479673758584800144779013 10027438829734650027146065)
  ·
    refine ⟨7520579122300987520359549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10027438829734650027146065 7520579122300987520359549)
    ·
      refine ⟨2820217170862870320134831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7520579122300987520359549 2820217170862870320134831)
      ·
        refine ⟨4230325756294305480202247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820217170862870320134831 4230325756294305480202247)
        ·
          refine ⟨6345488634441458220303371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230325756294305480202247 6345488634441458220303371)
          ·
            refine ⟨9518232951662187330455057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6345488634441458220303371 9518232951662187330455057)
            ·
              refine ⟨7138674713746640497841293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9518232951662187330455057 7138674713746640497841293)
              ·
                refine ⟨2677003017654990186690485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7138674713746640497841293 2677003017654990186690485)
                ·
                  refine ⟨250969032905155330002233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677003017654990186690485 250969032905155330002233)
                  ·
                    rfl

theorem cell22_2199422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2199422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199422 prefixEnd_2199422 := by exact prefixLift 2199422
  have htrace : WordTrace (prefixWord ++ tailWord_2199422) baseStart_2199422 baseEnd_2199422 := by
    simpa [prefixWord, tailWord_2199422, baseEnd_2199422] using wordTrace_append hprefix tailTrace_2199422
  have hstable : (prefixWord ++ tailWord_2199422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199422).length < 2 ^ (prefixWord ++ tailWord_2199422).sum := by decide
  have hdescent : baseEnd_2199422 < baseStart_2199422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199433 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 6]
def baseStart_2199433 : Nat := 118140960795 + 2199433 * 2 ^ 59
def prefixEnd_2199433 : Nat := 4983230072969 + 3 ^ 40 * 2199433 * 2
def baseEnd_2199433 : Nat := 250970288080088542660555

theorem tailTrace_2199433 : CollatzResearch.WordTrace tailWord_2199433 prefixEnd_2199433 250970288080088542660555 := by
  unfold tailWord_2199433
  simp only [CollatzResearch.WordTrace]
  refine ⟨80219911840837349095818953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53479941227224899397212635 80219911840837349095818953)
  ·
    refine ⟨60164933880628011821864215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80219911840837349095818953 60164933880628011821864215)
    ·
      refine ⟨90247400820942017732796323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60164933880628011821864215 90247400820942017732796323)
      ·
        refine ⟨135371101231413026599194485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90247400820942017732796323 135371101231413026599194485)
        ·
          refine ⟨12691040740444971243674483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135371101231413026599194485 12691040740444971243674483)
          ·
            refine ⟨19036561110667456865511725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12691040740444971243674483 19036561110667456865511725)
            ·
              refine ⟨7138710416500296324566897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19036561110667456865511725 7138710416500296324566897)
              ·
                refine ⟨5354032812375222243425173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7138710416500296324566897 5354032812375222243425173)
                ·
                  refine ⟨250970288080088542660555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5354032812375222243425173 250970288080088542660555)
                  ·
                    rfl

theorem cell22_2199433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_2199433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199433 prefixEnd_2199433 := by exact prefixLift 2199433
  have htrace : WordTrace (prefixWord ++ tailWord_2199433) baseStart_2199433 baseEnd_2199433 := by
    simpa [prefixWord, tailWord_2199433, baseEnd_2199433] using wordTrace_append hprefix tailTrace_2199433
  have hstable : (prefixWord ++ tailWord_2199433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199433).length < 2 ^ (prefixWord ++ tailWord_2199433).sum := by decide
  have hdescent : baseEnd_2199433 < baseStart_2199433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199452 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2199452 : Nat := 118140960795 + 2199452 * 2 ^ 59
def prefixEnd_2199452 : Nat := 4983230072969 + 3 ^ 40 * 2199452 * 2
def baseEnd_2199452 : Nat := 752917368328555911756607

theorem tailTrace_2199452 : CollatzResearch.WordTrace tailWord_2199452 prefixEnd_2199452 752917368328555911756607 := by
  unfold tailWord_2199452
  simp only [CollatzResearch.WordTrace]
  refine ⟨40110302413884257670380305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53480403218512343560507073 40110302413884257670380305)
  ·
    refine ⟨30082726810413193252785229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40110302413884257670380305 30082726810413193252785229)
    ·
      refine ⟨11281022553904947469794461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30082726810413193252785229 11281022553904947469794461)
      ·
        refine ⟨4230383457714355301172923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11281022553904947469794461 4230383457714355301172923)
        ·
          refine ⟨6345575186571532951759385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230383457714355301172923 6345575186571532951759385)
          ·
            refine ⟨4759181389928649713819539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6345575186571532951759385 4759181389928649713819539)
            ·
              refine ⟨7138772084892974570729309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759181389928649713819539 7138772084892974570729309)
              ·
                refine ⟨2677039531834865464023491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7138772084892974570729309 2677039531834865464023491)
                ·
                  refine ⟨4015559297752298196035237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677039531834865464023491 4015559297752298196035237)
                  ·
                    refine ⟨752917368328555911756607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4015559297752298196035237 752917368328555911756607)
                    ·
                      rfl

theorem cell22_2199452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2199452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199452 prefixEnd_2199452 := by exact prefixLift 2199452
  have htrace : WordTrace (prefixWord ++ tailWord_2199452) baseStart_2199452 baseEnd_2199452 := by
    simpa [prefixWord, tailWord_2199452, baseEnd_2199452] using wordTrace_append hprefix tailTrace_2199452
  have hstable : (prefixWord ++ tailWord_2199452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199452).length < 2 ^ (prefixWord ++ tailWord_2199452).sum := by decide
  have hdescent : baseEnd_2199452 < baseStart_2199452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199465 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 2, 3]
def baseStart_2199465 : Nat := 118140960795 + 2199465 * 2 ^ 59
def prefixEnd_2199465 : Nat := 4983230072969 + 3 ^ 40 * 2199465 * 2
def baseEnd_2199465 : Nat := 752921818494228211181567

theorem tailTrace_2199465 : CollatzResearch.WordTrace tailWord_2199465 prefixEnd_2199465 752921818494228211181567 := by
  unfold tailWord_2199465
  simp only [CollatzResearch.WordTrace]
  refine ⟨80221078976721418560983849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53480719317814279040655899 80221078976721418560983849)
  ·
    refine ⟨60165809232541063920737887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80221078976721418560983849 60165809232541063920737887)
    ·
      refine ⟨90248713848811595881106831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60165809232541063920737887 90248713848811595881106831)
      ·
        refine ⟨135373070773217393821660247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90248713848811595881106831 135373070773217393821660247)
        ·
          refine ⟨203059606159826090732490371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135373070773217393821660247 203059606159826090732490371)
          ·
            refine ⟨304589409239739136098735557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203059606159826090732490371 304589409239739136098735557)
            ·
              refine ⟨57110514232451088018512917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304589409239739136098735557 57110514232451088018512917)
              ·
                refine ⟨2677055354646144750867793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57110514232451088018512917 2677055354646144750867793)
                ·
                  refine ⟨2007791515984608563150845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677055354646144750867793 2007791515984608563150845)
                  ·
                    refine ⟨752921818494228211181567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007791515984608563150845 752921818494228211181567)
                    ·
                      rfl

theorem cell22_2199465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_2199465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199465 prefixEnd_2199465 := by exact prefixLift 2199465
  have htrace : WordTrace (prefixWord ++ tailWord_2199465) baseStart_2199465 baseEnd_2199465 := by
    simpa [prefixWord, tailWord_2199465, baseEnd_2199465] using wordTrace_append hprefix tailTrace_2199465
  have hstable : (prefixWord ++ tailWord_2199465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199465).length < 2 ^ (prefixWord ++ tailWord_2199465).sum := by decide
  have hdescent : baseEnd_2199465 < baseStart_2199465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199533 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_2199533 : Nat := 118140960795 + 2199533 * 2 ^ 59
def prefixEnd_2199533 : Nat := 4983230072969 + 3 ^ 40 * 2199533 * 2
def baseEnd_2199533 : Nat := 752945096283898700481359

theorem tailTrace_2199533 : CollatzResearch.WordTrace tailWord_2199533 prefixEnd_2199533 752945096283898700481359 := by
  unfold tailWord_2199533
  simp only [CollatzResearch.WordTrace]
  refine ⟨80223559140475066174459253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53482372760316710782972835 80223559140475066174459253)
  ·
    refine ⟨7520958669419537453855555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80223559140475066174459253 7520958669419537453855555)
    ·
      refine ⟨11281438004129306180783333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7520958669419537453855555 11281438004129306180783333)
      ·
        refine ⟨2115269625774244908896875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11281438004129306180783333 2115269625774244908896875)
        ·
          refine ⟨3172904438661367363345313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2115269625774244908896875 3172904438661367363345313)
          ·
            refine ⟨2379678328996025522508985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3172904438661367363345313 2379678328996025522508985)
            ·
              refine ⟨1784758746747019141881739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379678328996025522508985 1784758746747019141881739)
              ·
                refine ⟨2677138120120528712822609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784758746747019141881739 2677138120120528712822609)
                ·
                  refine ⟨2007853590090396534616957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677138120120528712822609 2007853590090396534616957)
                  ·
                    refine ⟨752945096283898700481359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007853590090396534616957 752945096283898700481359)
                    ·
                      rfl

theorem cell22_2199533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_2199533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199533 prefixEnd_2199533 := by exact prefixLift 2199533
  have htrace : WordTrace (prefixWord ++ tailWord_2199533) baseStart_2199533 baseEnd_2199533 := by
    simpa [prefixWord, tailWord_2199533, baseEnd_2199533] using wordTrace_append hprefix tailTrace_2199533
  have hstable : (prefixWord ++ tailWord_2199533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199533).length < 2 ^ (prefixWord ++ tailWord_2199533).sum := by decide
  have hdescent : baseEnd_2199533 < baseStart_2199533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199568 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 8]
def baseStart_2199568 : Nat := 118140960795 + 2199568 * 2 ^ 59
def prefixEnd_2199568 : Nat := 4983230072969 + 3 ^ 40 * 2199568 * 2
def baseEnd_2199568 : Nat := 250985692499723425285417

theorem tailTrace_2199568 : CollatzResearch.WordTrace tailWord_2199568 prefixEnd_2199568 250985692499723425285417 := by
  unfold tailWord_2199568
  simp only [CollatzResearch.WordTrace]
  refine ⟨40112417847674133575991679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53483223796898844767988905 40112417847674133575991679)
  ·
    refine ⟨60168626771511200363987519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40112417847674133575991679 60168626771511200363987519)
    ·
      refine ⟨90252940157266800545981279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60168626771511200363987519 90252940157266800545981279)
      ·
        refine ⟨135379410235900200818971919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90252940157266800545981279 135379410235900200818971919)
        ·
          refine ⟨203069115353850301228457879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135379410235900200818971919 203069115353850301228457879)
          ·
            refine ⟨304603673030775451842686819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203069115353850301228457879 304603673030775451842686819)
            ·
              refine ⟨456905509546163177764030229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304603673030775451842686819 456905509546163177764030229)
              ·
                refine ⟨21417445759976398957688917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 456905509546163177764030229 21417445759976398957688917)
                ·
                  refine ⟨250985692499723425285417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21417445759976398957688917 250985692499723425285417)
                  ·
                    rfl

theorem cell22_2199568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_2199568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199568 prefixEnd_2199568 := by exact prefixLift 2199568
  have htrace : WordTrace (prefixWord ++ tailWord_2199568) baseStart_2199568 baseEnd_2199568 := by
    simpa [prefixWord, tailWord_2199568, baseEnd_2199568] using wordTrace_append hprefix tailTrace_2199568
  have hstable : (prefixWord ++ tailWord_2199568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199568).length < 2 ^ (prefixWord ++ tailWord_2199568).sum := by decide
  have hdescent : baseEnd_2199568 < baseStart_2199568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199600 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_2199600 : Nat := 118140960795 + 2199600 * 2 ^ 59
def prefixEnd_2199600 : Nat := 4983230072969 + 3 ^ 40 * 2199600 * 2
def baseEnd_2199600 : Nat := 752968031753132859056153

theorem tailTrace_2199600 : CollatzResearch.WordTrace tailWord_2199600 prefixEnd_2199600 752968031753132859056153 := by
  unfold tailWord_2199600
  simp only [CollatzResearch.WordTrace]
  refine ⟨40113001415616168308574127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53484001887488224411432169 40113001415616168308574127)
  ·
    refine ⟨60169502123424252462861191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40113001415616168308574127 60169502123424252462861191)
    ·
      refine ⟨90254253185136378694291787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60169502123424252462861191 90254253185136378694291787)
      ·
        refine ⟨135381379777704568041437681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90254253185136378694291787 135381379777704568041437681)
        ·
          refine ⟨101536034833278426031078261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135381379777704568041437681 101536034833278426031078261)
          ·
            refine ⟨9519003265619852440413587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101536034833278426031078261 9519003265619852440413587)
            ·
              refine ⟨14278504898429778660620381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9519003265619852440413587 14278504898429778660620381)
              ·
                refine ⟨5354439336911166997732643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14278504898429778660620381 5354439336911166997732643)
                ·
                  refine ⟨8031659005366750496598965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5354439336911166997732643 8031659005366750496598965)
                  ·
                    refine ⟨752968031753132859056153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8031659005366750496598965 752968031753132859056153)
                    ·
                      rfl

theorem cell22_2199600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_2199600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199600 prefixEnd_2199600 := by exact prefixLift 2199600
  have htrace : WordTrace (prefixWord ++ tailWord_2199600) baseStart_2199600 baseEnd_2199600 := by
    simpa [prefixWord, tailWord_2199600, baseEnd_2199600] using wordTrace_append hprefix tailTrace_2199600
  have hstable : (prefixWord ++ tailWord_2199600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199600).length < 2 ^ (prefixWord ++ tailWord_2199600).sum := by decide
  have hdescent : baseEnd_2199600 < baseStart_2199600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199617 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2199617 : Nat := 118140960795 + 2199617 * 2 ^ 59
def prefixEnd_2199617 : Nat := 4983230072969 + 3 ^ 40 * 2199617 * 2
def baseEnd_2199617 : Nat := 752973851200550481381101

theorem tailTrace_2199617 : CollatzResearch.WordTrace tailWord_2199617 prefixEnd_2199617 752973851200550481381101 := by
  unfold tailWord_2199617
  simp only [CollatzResearch.WordTrace]
  refine ⟨80226622872170748520517105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53484415248113832347011403 80226622872170748520517105)
  ·
    refine ⟨60169967154128061390387829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80226622872170748520517105 60169967154128061390387829)
    ·
      refine ⟨5640934420699505755348859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60169967154128061390387829 5640934420699505755348859)
      ·
        refine ⟨8461401631049258633023289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5640934420699505755348859 8461401631049258633023289)
        ·
          refine ⟨6346051223286943974767467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8461401631049258633023289 6346051223286943974767467)
          ·
            refine ⟨9519076834930415962151201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6346051223286943974767467 9519076834930415962151201)
            ·
              refine ⟨7139307626197811971613401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9519076834930415962151201 7139307626197811971613401)
              ·
                refine ⟨5354480719648358978710051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7139307626197811971613401 5354480719648358978710051)
                ·
                  refine ⟨8031721079472538468065077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5354480719648358978710051 8031721079472538468065077)
                  ·
                    refine ⟨752973851200550481381101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8031721079472538468065077 752973851200550481381101)
                    ·
                      rfl

theorem cell22_2199617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2199617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199617 prefixEnd_2199617 := by exact prefixLift 2199617
  have htrace : WordTrace (prefixWord ++ tailWord_2199617) baseStart_2199617 baseEnd_2199617 := by
    simpa [prefixWord, tailWord_2199617, baseEnd_2199617] using wordTrace_append hprefix tailTrace_2199617
  have hstable : (prefixWord ++ tailWord_2199617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199617).length < 2 ^ (prefixWord ++ tailWord_2199617).sum := by decide
  have hdescent : baseEnd_2199617 < baseStart_2199617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199630 : List Nat := [4, 1, 1, 1, 1, 5, 9]
def baseStart_2199630 : Nat := 118140960795 + 2199630 * 2 ^ 59
def prefixEnd_2199630 : Nat := 4983230072969 + 3 ^ 40 * 2199630 * 2
def baseEnd_2199630 : Nat := 27888085235786028918743

theorem tailTrace_2199630 : CollatzResearch.WordTrace tailWord_2199630 prefixEnd_2199630 27888085235786028918743 := by
  unfold tailWord_2199630
  simp only [CollatzResearch.WordTrace]
  refine ⟨10028387127640456467592543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53484731347415767827160229 10028387127640456467592543)
  ·
    refine ⟨15042580691460684701388815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10028387127640456467592543 15042580691460684701388815)
    ·
      refine ⟨22563871037191027052083223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15042580691460684701388815 22563871037191027052083223)
      ·
        refine ⟨33845806555786540578124835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22563871037191027052083223 33845806555786540578124835)
        ·
          refine ⟨50768709833679810867187253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33845806555786540578124835 50768709833679810867187253)
          ·
            refine ⟨4759566546907482268798805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50768709833679810867187253 4759566546907482268798805)
            ·
              refine ⟨27888085235786028918743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4759566546907482268798805 27888085235786028918743)
              ·
                rfl

theorem cell22_2199630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 9].length) (baseStart_2199630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199630 prefixEnd_2199630 := by exact prefixLift 2199630
  have htrace : WordTrace (prefixWord ++ tailWord_2199630) baseStart_2199630 baseEnd_2199630 := by
    simpa [prefixWord, tailWord_2199630, baseEnd_2199630] using wordTrace_append hprefix tailTrace_2199630
  have hstable : (prefixWord ++ tailWord_2199630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199630).length < 2 ^ (prefixWord ++ tailWord_2199630).sum := by decide
  have hdescent : baseEnd_2199630 < baseStart_2199630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199634 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_2199634 : Nat := 118140960795 + 2199634 * 2 ^ 59
def prefixEnd_2199634 : Nat := 4983230072969 + 3 ^ 40 * 2199634 * 2
def baseEnd_2199634 : Nat := 752979670647968103706049

theorem tailTrace_2199634 : CollatzResearch.WordTrace tailWord_2199634 prefixEnd_2199634 752979670647968103706049 := by
  unfold tailWord_2199634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20056810728277290105971489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53484828608739440282590637 20056810728277290105971489)
  ·
    refine ⟨15042608046207967579478617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20056810728277290105971489 15042608046207967579478617)
    ·
      refine ⟨11281956034655975684608963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15042608046207967579478617 11281956034655975684608963)
      ·
        refine ⟨16922934051983963526913445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11281956034655975684608963 16922934051983963526913445)
        ·
          refine ⟨3173050134746993161296271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16922934051983963526913445 3173050134746993161296271)
          ·
            refine ⟨4759575202120489741944407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173050134746993161296271 4759575202120489741944407)
            ·
              refine ⟨7139362803180734612916611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759575202120489741944407 7139362803180734612916611)
              ·
                refine ⟨10709044204771101919374917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139362803180734612916611 10709044204771101919374917)
                ·
                  refine ⟨2007945788394581609882797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10709044204771101919374917 2007945788394581609882797)
                  ·
                    refine ⟨752979670647968103706049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007945788394581609882797 752979670647968103706049)
                    ·
                      rfl

theorem cell22_2199634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_2199634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199634 prefixEnd_2199634 := by exact prefixLift 2199634
  have htrace : WordTrace (prefixWord ++ tailWord_2199634) baseStart_2199634 baseEnd_2199634 := by
    simpa [prefixWord, tailWord_2199634, baseEnd_2199634] using wordTrace_append hprefix tailTrace_2199634
  have hstable : (prefixWord ++ tailWord_2199634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199634).length < 2 ^ (prefixWord ++ tailWord_2199634).sum := by decide
  have hdescent : baseEnd_2199634 < baseStart_2199634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199696 : List Nat := [2, 1, 1, 1, 1, 1, 9, 2, 1, 3]
def baseStart_2199696 : Nat := 118140960795 + 2199696 * 2 ^ 59
def prefixEnd_2199696 : Nat := 4983230072969 + 3 ^ 40 * 2199696 * 2
def baseEnd_2199696 : Nat := 753000894515020608655859

theorem tailTrace_2199696 : CollatzResearch.WordTrace tailWord_2199696 prefixEnd_2199696 753000894515020608655859 := by
  unfold tailWord_2199696
  simp only [CollatzResearch.WordTrace]
  refine ⟨40114752119442272506321471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53486336159256363341761961 40114752119442272506321471)
  ·
    refine ⟨60172128179163408759482207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40114752119442272506321471 60172128179163408759482207)
    ·
      refine ⟨90258192268745113139223311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60172128179163408759482207 90258192268745113139223311)
      ·
        refine ⟨135387288403117669708834967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90258192268745113139223311 135387288403117669708834967)
        ·
          refine ⟨203080932604676504563252451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135387288403117669708834967 203080932604676504563252451)
          ·
            refine ⟨304621398907014756844878677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203080932604676504563252451 304621398907014756844878677)
            ·
              refine ⟨1784891009220789590887961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 304621398907014756844878677 1784891009220789590887961)
              ·
                refine ⟨1338668256915592193165971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784891009220789590887961 1338668256915592193165971)
                ·
                  refine ⟨2008002385373388289748957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338668256915592193165971 2008002385373388289748957)
                  ·
                    refine ⟨753000894515020608655859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008002385373388289748957 753000894515020608655859)
                    ·
                      rfl

theorem cell22_2199696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 3].length) (baseStart_2199696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199696 prefixEnd_2199696 := by exact prefixLift 2199696
  have htrace : WordTrace (prefixWord ++ tailWord_2199696) baseStart_2199696 baseEnd_2199696 := by
    simpa [prefixWord, tailWord_2199696, baseEnd_2199696] using wordTrace_append hprefix tailTrace_2199696
  have hstable : (prefixWord ++ tailWord_2199696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199696).length < 2 ^ (prefixWord ++ tailWord_2199696).sum := by decide
  have hdescent : baseEnd_2199696 < baseStart_2199696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199702 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2199702 : Nat := 118140960795 + 2199702 * 2 ^ 59
def prefixEnd_2199702 : Nat := 4983230072969 + 3 ^ 40 * 2199702 * 2
def baseEnd_2199702 : Nat := 753002948437638593005841

theorem tailTrace_2199702 : CollatzResearch.WordTrace tailWord_2199702 prefixEnd_2199702 753002948437638593005841 := by
  unfold tailWord_2199702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014357692303925502335085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53486482051241872024907573 5014357692303925502335085)
  ·
    refine ⟨1880384134613972063375657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5014357692303925502335085 1880384134613972063375657)
    ·
      refine ⟨1410288100960479047531743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1880384134613972063375657 1410288100960479047531743)
      ·
        refine ⟨2115432151440718571297615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410288100960479047531743 2115432151440718571297615)
        ·
          refine ⟨3173148227161077856946423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2115432151440718571297615 3173148227161077856946423)
          ·
            refine ⟨4759722340741616785419635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173148227161077856946423 4759722340741616785419635)
            ·
              refine ⟨7139583511112425178129453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759722340741616785419635 7139583511112425178129453)
              ·
                refine ⟨2677343816667159441798545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7139583511112425178129453 2677343816667159441798545)
                ·
                  refine ⟨2008007862500369581348909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677343816667159441798545 2008007862500369581348909)
                  ·
                    refine ⟨753002948437638593005841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008007862500369581348909 753002948437638593005841)
                    ·
                      rfl

theorem cell22_2199702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2199702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199702 prefixEnd_2199702 := by exact prefixLift 2199702
  have htrace : WordTrace (prefixWord ++ tailWord_2199702) baseStart_2199702 baseEnd_2199702 := by
    simpa [prefixWord, tailWord_2199702, baseEnd_2199702] using wordTrace_append hprefix tailTrace_2199702
  have hstable : (prefixWord ++ tailWord_2199702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199702).length < 2 ^ (prefixWord ++ tailWord_2199702).sum := by decide
  have hdescent : baseEnd_2199702 < baseStart_2199702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199709 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 5]
def baseStart_2199709 : Nat := 118140960795 + 2199709 * 2 ^ 59
def prefixEnd_2199709 : Nat := 4983230072969 + 3 ^ 40 * 2199709 * 2
def baseEnd_2199709 : Nat := 251001781560230969360273

theorem tailTrace_2199709 : CollatzResearch.WordTrace tailWord_2199709 prefixEnd_2199709 251001781560230969360273 := by
  unfold tailWord_2199709
  simp only [CollatzResearch.WordTrace]
  refine ⟨80229978387837448232866181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53486652258558298821910787 80229978387837448232866181)
  ·
    refine ⟨15043120947719521543662409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80229978387837448232866181 15043120947719521543662409)
    ·
      refine ⟨11282340710789641157746807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15043120947719521543662409 11282340710789641157746807)
      ·
        refine ⟨16923511066184461736620211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11282340710789641157746807 16923511066184461736620211)
        ·
          refine ⟨25385266599276692604930317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16923511066184461736620211 25385266599276692604930317)
          ·
            refine ⟨9519474974728759726848869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25385266599276692604930317 9519474974728759726848869)
            ·
              refine ⟨1784901557761642448784163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9519474974728759726848869 1784901557761642448784163)
              ·
                refine ⟨2677352336642463673176245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784901557761642448784163 2677352336642463673176245)
                ·
                  refine ⟨251001781560230969360273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677352336642463673176245 251001781560230969360273)
                  ·
                    rfl

theorem cell22_2199709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_2199709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199709 prefixEnd_2199709 := by exact prefixLift 2199709
  have htrace : WordTrace (prefixWord ++ tailWord_2199709) baseStart_2199709 baseEnd_2199709 := by
    simpa [prefixWord, tailWord_2199709, baseEnd_2199709] using wordTrace_append hprefix tailTrace_2199709
  have hstable : (prefixWord ++ tailWord_2199709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199709).length < 2 ^ (prefixWord ++ tailWord_2199709).sum := by decide
  have hdescent : baseEnd_2199709 < baseStart_2199709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199739 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 1, 4]
def baseStart_2199739 : Nat := 118140960795 + 2199739 * 2 ^ 59
def prefixEnd_2199739 : Nat := 4983230072969 + 3 ^ 40 * 2199739 * 2
def baseEnd_2199739 : Nat := 753015614293782829830727

theorem tailTrace_2199739 : CollatzResearch.WordTrace tailWord_2199739 prefixEnd_2199739 753015614293782829830727 := by
  unfold tailWord_2199739
  simp only [CollatzResearch.WordTrace]
  refine ⟨80231072577728763356458271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53487381718485842237638847 80231072577728763356458271)
  ·
    refine ⟨120346608866593145034687407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80231072577728763356458271 120346608866593145034687407)
    ·
      refine ⟨180519913299889717552031111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120346608866593145034687407 180519913299889717552031111)
      ·
        refine ⟨270779869949834576328046667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180519913299889717552031111 270779869949834576328046667)
        ·
          refine ⟨406169804924751864492070001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270779869949834576328046667 406169804924751864492070001)
          ·
            refine ⟨304627353693563898369052501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406169804924751864492070001 304627353693563898369052501)
            ·
              refine ⟨1784925900548225967006167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 304627353693563898369052501 1784925900548225967006167)
              ·
                refine ⟨2677388850822338950509251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784925900548225967006167 2677388850822338950509251)
                ·
                  refine ⟨4016083276233508425763877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677388850822338950509251 4016083276233508425763877)
                  ·
                    refine ⟨753015614293782829830727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4016083276233508425763877 753015614293782829830727)
                    ·
                      rfl

theorem cell22_2199739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 4].length) (baseStart_2199739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199739 prefixEnd_2199739 := by exact prefixLift 2199739
  have htrace : WordTrace (prefixWord ++ tailWord_2199739) baseStart_2199739 baseEnd_2199739 := by
    simpa [prefixWord, tailWord_2199739, baseEnd_2199739] using wordTrace_append hprefix tailTrace_2199739
  have hstable : (prefixWord ++ tailWord_2199739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199739).length < 2 ^ (prefixWord ++ tailWord_2199739).sum := by decide
  have hdescent : baseEnd_2199739 < baseStart_2199739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199754 : List Nat := [3, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_2199754 : Nat := 118140960795 + 2199754 * 2 ^ 59
def prefixEnd_2199754 : Nat := 4983230072969 + 3 ^ 40 * 2199754 * 2
def baseEnd_2199754 : Nat := 251006916366775930235227

theorem tailTrace_2199754 : CollatzResearch.WordTrace tailWord_2199754 prefixEnd_2199754 251006916366775930235227 := by
  unfold tailWord_2199754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20057904918168605229563579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53487746448449613945502877 20057904918168605229563579)
  ·
    refine ⟨30086857377252907844345369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20057904918168605229563579 30086857377252907844345369)
    ·
      refine ⟨22565143032939680883259027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30086857377252907844345369 22565143032939680883259027)
      ·
        refine ⟨33847714549409521324888541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22565143032939680883259027 33847714549409521324888541)
        ·
          refine ⟨12692892956028570496833203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33847714549409521324888541 12692892956028570496833203)
          ·
            refine ⟨19039339434042855745249805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12692892956028570496833203 19039339434042855745249805)
            ·
              refine ⟨7139752287766070904468677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19039339434042855745249805 7139752287766070904468677)
              ·
                refine ⟨1338703553956138294587877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7139752287766070904468677 1338703553956138294587877)
                ·
                  refine ⟨251006916366775930235227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338703553956138294587877 251006916366775930235227)
                  ·
                    rfl

theorem cell22_2199754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_2199754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199754 prefixEnd_2199754 := by exact prefixLift 2199754
  have htrace : WordTrace (prefixWord ++ tailWord_2199754) baseStart_2199754 baseEnd_2199754 := by
    simpa [prefixWord, tailWord_2199754, baseEnd_2199754] using wordTrace_append hprefix tailTrace_2199754
  have hstable : (prefixWord ++ tailWord_2199754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199754).length < 2 ^ (prefixWord ++ tailWord_2199754).sum := by decide
  have hdescent : baseEnd_2199754 < baseStart_2199754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199769 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 2, 3]
def baseStart_2199769 : Nat := 118140960795 + 2199769 * 2 ^ 59
def prefixEnd_2199769 : Nat := 4983230072969 + 3 ^ 40 * 2199769 * 2
def baseEnd_2199769 : Nat := 753025883906872751580635

theorem tailTrace_2199769 : CollatzResearch.WordTrace tailWord_2199769 prefixEnd_2199769 753025883906872751580635 := by
  unfold tailWord_2199769
  simp only [CollatzResearch.WordTrace]
  refine ⟨80232166767620078480050361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53488111178413385653366907 80232166767620078480050361)
  ·
    refine ⟨60174125075715058860037771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80232166767620078480050361 60174125075715058860037771)
    ·
      refine ⟨90261187613572588290056657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60174125075715058860037771 90261187613572588290056657)
      ·
        refine ⟨67695890710179441217542493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90261187613572588290056657 67695890710179441217542493)
        ·
          refine ⟨25385959016317290456578435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67695890710179441217542493 25385959016317290456578435)
          ·
            refine ⟨38078938524475935684867653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25385959016317290456578435 38078938524475935684867653)
            ·
              refine ⟨7139800973339237940912685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38078938524475935684867653 7139800973339237940912685)
              ·
                refine ⟨2677425365002214227842257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7139800973339237940912685 2677425365002214227842257)
                ·
                  refine ⟨2008069023751660670881693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677425365002214227842257 2008069023751660670881693)
                  ·
                    refine ⟨753025883906872751580635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008069023751660670881693 753025883906872751580635)
                    ·
                      rfl

theorem cell22_2199769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_2199769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199769 prefixEnd_2199769 := by exact prefixLift 2199769
  have htrace : WordTrace (prefixWord ++ tailWord_2199769) baseStart_2199769 baseEnd_2199769 := by
    simpa [prefixWord, tailWord_2199769, baseEnd_2199769] using wordTrace_append hprefix tailTrace_2199769
  have hstable : (prefixWord ++ tailWord_2199769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199769).length < 2 ^ (prefixWord ++ tailWord_2199769).sum := by decide
  have hdescent : baseEnd_2199769 < baseStart_2199769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199784 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2199784 : Nat := 118140960795 + 2199784 * 2 ^ 59
def prefixEnd_2199784 : Nat := 4983230072969 + 3 ^ 40 * 2199784 * 2
def baseEnd_2199784 : Nat := 753031018713417712455589

theorem tailTrace_2199784 : CollatzResearch.WordTrace tailWord_2199784 prefixEnd_2199784 753031018713417712455589 := by
  unfold tailWord_2199784
  simp only [CollatzResearch.WordTrace]
  refine ⟨40116356931282868020923203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53488475908377157361230937 40116356931282868020923203)
  ·
    refine ⟨60174535396924302031384805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40116356931282868020923203 60174535396924302031384805)
    ·
      refine ⟨11282725386923306630884651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60174535396924302031384805 11282725386923306630884651)
      ·
        refine ⟨16924088080384959946326977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11282725386923306630884651 16924088080384959946326977)
        ·
          refine ⟨12693066060288719959745233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16924088080384959946326977 12693066060288719959745233)
          ·
            refine ⟨9519799545216539969808925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12693066060288719959745233 9519799545216539969808925)
            ·
              refine ⟨3569924829456202488678347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9519799545216539969808925 3569924829456202488678347)
              ·
                refine ⟨5354887244184303733017521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3569924829456202488678347 5354887244184303733017521)
                ·
                  refine ⟨4016165433138227799763141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354887244184303733017521 4016165433138227799763141)
                  ·
                    refine ⟨753031018713417712455589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4016165433138227799763141 753031018713417712455589)
                    ·
                      rfl

theorem cell22_2199784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2199784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199784 prefixEnd_2199784 := by exact prefixLift 2199784
  have htrace : WordTrace (prefixWord ++ tailWord_2199784) baseStart_2199784 baseEnd_2199784 := by
    simpa [prefixWord, tailWord_2199784, baseEnd_2199784] using wordTrace_append hprefix tailTrace_2199784
  have hstable : (prefixWord ++ tailWord_2199784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199784).length < 2 ^ (prefixWord ++ tailWord_2199784).sum := by decide
  have hdescent : baseEnd_2199784 < baseStart_2199784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199827 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 5]
def baseStart_2199827 : Nat := 118140960795 + 2199827 * 2 ^ 59
def prefixEnd_2199827 : Nat := 4983230072969 + 3 ^ 40 * 2199827 * 2
def baseEnd_2199827 : Nat := 251015246164059977876819

theorem tailTrace_2199827 : CollatzResearch.WordTrace tailWord_2199827 prefixEnd_2199827 251015246164059977876819 := by
  unfold tailWord_2199827
  simp only [CollatzResearch.WordTrace]
  refine ⟨80234282201409954385661735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53489521467606636257107823 80234282201409954385661735)
  ·
    refine ⟨120351423302114931578492603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80234282201409954385661735 120351423302114931578492603)
    ·
      refine ⟨180527134953172397367738905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120351423302114931578492603 180527134953172397367738905)
      ·
        refine ⟨135395351214879298025804179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180527134953172397367738905 135395351214879298025804179)
        ·
          refine ⟨203093026822318947038706269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135395351214879298025804179 203093026822318947038706269)
          ·
            refine ⟨76159885058369605139514851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203093026822318947038706269 76159885058369605139514851)
            ·
              refine ⟨114239827587554407709272277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76159885058369605139514851 114239827587554407709272277)
              ·
                refine ⟨2677495959083306430686069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114239827587554407709272277 2677495959083306430686069)
                ·
                  refine ⟨251015246164059977876819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677495959083306430686069 251015246164059977876819)
                  ·
                    rfl

theorem cell22_2199827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 5].length) (baseStart_2199827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199827 prefixEnd_2199827 := by exact prefixLift 2199827
  have htrace : WordTrace (prefixWord ++ tailWord_2199827) baseStart_2199827 baseEnd_2199827 := by
    simpa [prefixWord, tailWord_2199827, baseEnd_2199827] using wordTrace_append hprefix tailTrace_2199827
  have hstable : (prefixWord ++ tailWord_2199827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199827).length < 2 ^ (prefixWord ++ tailWord_2199827).sum := by decide
  have hdescent : baseEnd_2199827 < baseStart_2199827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199865 : List Nat := [1, 2, 1, 6, 1, 2, 3, 2, 1, 3]
def baseStart_2199865 : Nat := 118140960795 + 2199865 * 2 ^ 59
def prefixEnd_2199865 : Nat := 4983230072969 + 3 ^ 40 * 2199865 * 2
def baseEnd_2199865 : Nat := 753058746668760501180341

theorem tailTrace_2199865 : CollatzResearch.WordTrace tailWord_2199865 prefixEnd_2199865 753058746668760501180341 := by
  unfold tailWord_2199865
  simp only [CollatzResearch.WordTrace]
  refine ⟨80235668175272286875545049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53490445450181524583696699 80235668175272286875545049)
  ·
    refine ⟨60176751131454215156658787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80235668175272286875545049 60176751131454215156658787)
    ·
      refine ⟨90265126697181322734988181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60176751131454215156658787 90265126697181322734988181)
      ·
        refine ⟨4231177813930374503202571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90265126697181322734988181 4231177813930374503202571)
        ·
          refine ⟨6346766720895561754803857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231177813930374503202571 6346766720895561754803857)
          ·
            refine ⟨4760075040671671316102893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6346766720895561754803857 4760075040671671316102893)
            ·
              refine ⟨1785028140251876743538585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4760075040671671316102893 1785028140251876743538585)
              ·
                refine ⟨1338771105188907557653939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785028140251876743538585 1338771105188907557653939)
                ·
                  refine ⟨2008156657783361336480909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338771105188907557653939 2008156657783361336480909)
                  ·
                    refine ⟨753058746668760501180341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008156657783361336480909 753058746668760501180341)
                    ·
                      rfl

theorem cell22_2199865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 3].length) (baseStart_2199865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199865 prefixEnd_2199865 := by exact prefixLift 2199865
  have htrace : WordTrace (prefixWord ++ tailWord_2199865) baseStart_2199865 baseEnd_2199865 := by
    simpa [prefixWord, tailWord_2199865, baseEnd_2199865] using wordTrace_append hprefix tailTrace_2199865
  have hstable : (prefixWord ++ tailWord_2199865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199865).length < 2 ^ (prefixWord ++ tailWord_2199865).sum := by decide
  have hdescent : baseEnd_2199865 < baseStart_2199865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199872 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 6]
def baseStart_2199872 : Nat := 118140960795 + 2199872 * 2 ^ 59
def prefixEnd_2199872 : Nat := 4983230072969 + 3 ^ 40 * 2199872 * 2
def baseEnd_2199872 : Nat := 251020380970604938751773

theorem tailTrace_2199872 : CollatzResearch.WordTrace tailWord_2199872 prefixEnd_2199872 251020380970604938751773 := by
  unfold tailWord_2199872
  simp only [CollatzResearch.WordTrace]
  refine ⟨40117961743123463535524935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53490615657497951380699913 40117961743123463535524935)
  ·
    refine ⟨60176942614685195303287403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40117961743123463535524935 60176942614685195303287403)
    ·
      refine ⟨90265413922027792954931105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60176942614685195303287403 90265413922027792954931105)
      ·
        refine ⟨67699060441520844716198329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90265413922027792954931105 67699060441520844716198329)
        ·
          refine ⟨50774295331140633537148747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67699060441520844716198329 50774295331140633537148747)
          ·
            refine ⟨76161442996710950305723121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50774295331140633537148747 76161442996710950305723121)
            ·
              refine ⟨57121082247533212729292341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76161442996710950305723121 57121082247533212729292341)
              ·
                refine ⟨5355101460706238693371157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57121082247533212729292341 5355101460706238693371157)
                ·
                  refine ⟨251020380970604938751773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5355101460706238693371157 251020380970604938751773)
                  ·
                    rfl

theorem cell22_2199872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_2199872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2199872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2199872 prefixEnd_2199872 := by exact prefixLift 2199872
  have htrace : WordTrace (prefixWord ++ tailWord_2199872) baseStart_2199872 baseEnd_2199872 := by
    simpa [prefixWord, tailWord_2199872, baseEnd_2199872] using wordTrace_append hprefix tailTrace_2199872
  have hstable : (prefixWord ++ tailWord_2199872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199872).length < 2 ^ (prefixWord ++ tailWord_2199872).sum := by decide
  have hdescent : baseEnd_2199872 < baseStart_2199872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200009 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_2200009 : Nat := 118140960795 + 2200009 * 2 ^ 59
def prefixEnd_2200009 : Nat := 4983230072969 + 3 ^ 40 * 2200009 * 2
def baseEnd_2200009 : Nat := 753108040811592125579899

theorem tailTrace_2200009 : CollatzResearch.WordTrace tailWord_2200009 prefixEnd_2200009 753108040811592125579899 := by
  unfold tailWord_2200009
  simp only [CollatzResearch.WordTrace]
  refine ⟨80240920286750599468787081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53493946857833732979191387 80240920286750599468787081)
  ·
    refine ⟨60180690215062949601590311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80240920286750599468787081 60180690215062949601590311)
    ·
      refine ⟨90271035322594424402385467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60180690215062949601590311 90271035322594424402385467)
      ·
        refine ⟨135406552983891636603578201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90271035322594424402385467 135406552983891636603578201)
        ·
          refine ⟨101554914737918727452683651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135406552983891636603578201 101554914737918727452683651)
          ·
            refine ⟨152332372106878091179025477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101554914737918727452683651 152332372106878091179025477)
            ·
              refine ⟨28562319770039642096067277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152332372106878091179025477 28562319770039642096067277)
              ·
                refine ⟨10710869913764865786025229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28562319770039642096067277 10710869913764865786025229)
                ·
                  refine ⟨4016576217661824669759461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10710869913764865786025229 4016576217661824669759461)
                  ·
                    refine ⟨753108040811592125579899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4016576217661824669759461 753108040811592125579899)
                    ·
                      rfl

theorem cell22_2200009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_2200009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200009 prefixEnd_2200009 := by exact prefixLift 2200009
  have htrace : WordTrace (prefixWord ++ tailWord_2200009) baseStart_2200009 baseEnd_2200009 := by
    simpa [prefixWord, tailWord_2200009, baseEnd_2200009] using wordTrace_append hprefix tailTrace_2200009
  have hstable : (prefixWord ++ tailWord_2200009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200009).length < 2 ^ (prefixWord ++ tailWord_2200009).sum := by decide
  have hdescent : baseEnd_2200009 < baseStart_2200009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200026 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_2200026 : Nat := 118140960795 + 2200026 * 2 ^ 59
def prefixEnd_2200026 : Nat := 4983230072969 + 3 ^ 40 * 2200026 * 2
def baseEnd_2200026 : Nat := 753113860259009747904847

theorem tailTrace_2200026 : CollatzResearch.WordTrace tailWord_2200026 prefixEnd_2200026 753113860259009747904847 := by
  unfold tailWord_2200026
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060385081922252843038983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53494360218459340914770621 20060385081922252843038983)
  ·
    refine ⟨30090577622883379264558475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20060385081922252843038983 30090577622883379264558475)
    ·
      refine ⟨45135866434325068896837713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30090577622883379264558475 45135866434325068896837713)
      ·
        refine ⟨33851899825743801672628285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45135866434325068896837713 33851899825743801672628285)
        ·
          refine ⟨12694462434653925627235607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33851899825743801672628285 12694462434653925627235607)
          ·
            refine ⟨19041693651980888440853411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12694462434653925627235607 19041693651980888440853411)
            ·
              refine ⟨28562540477971332661280117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19041693651980888440853411 28562540477971332661280117)
              ·
                refine ⟨2677738169809812436995011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28562540477971332661280117 2677738169809812436995011)
                ·
                  refine ⟨4016607254714718655492517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677738169809812436995011 4016607254714718655492517)
                  ·
                    refine ⟨753113860259009747904847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4016607254714718655492517 753113860259009747904847)
                    ·
                      rfl

theorem cell22_2200026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_2200026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200026 prefixEnd_2200026 := by exact prefixLift 2200026
  have htrace : WordTrace (prefixWord ++ tailWord_2200026) baseStart_2200026 baseEnd_2200026 := by
    simpa [prefixWord, tailWord_2200026, baseEnd_2200026] using wordTrace_append hprefix tailTrace_2200026
  have hstable : (prefixWord ++ tailWord_2200026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200026).length < 2 ^ (prefixWord ++ tailWord_2200026).sum := by decide
  have hdescent : baseEnd_2200026 < baseStart_2200026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200034 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2200034 : Nat := 118140960795 + 2200034 * 2 ^ 59
def prefixEnd_2200034 : Nat := 4983230072969 + 3 ^ 40 * 2200034 * 2
def baseEnd_2200034 : Nat := 753116598822500393704823

theorem tailTrace_2200034 : CollatzResearch.WordTrace tailWord_2200034 prefixEnd_2200034 753116598822500393704823 := by
  unfold tailWord_2200034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060458027915007184611789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53494554741106685825631437 20060458027915007184611789)
  ·
    refine ⟨7522671760468127694229421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20060458027915007184611789 7522671760468127694229421)
    ·
      refine ⟨2821001910175547885336033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7522671760468127694229421 2821001910175547885336033)
      ·
        refine ⟨2115751432631660914002025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2821001910175547885336033 2115751432631660914002025)
        ·
          refine ⟨1586813574473745685501519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2115751432631660914002025 1586813574473745685501519)
          ·
            refine ⟨2380220361710618528252279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586813574473745685501519 2380220361710618528252279)
            ·
              refine ⟨3570330542565927792378419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380220361710618528252279 3570330542565927792378419)
              ·
                refine ⟨5355495813848891688567629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3570330542565927792378419 5355495813848891688567629)
                ·
                  refine ⟨2008310930193334383212861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5355495813848891688567629 2008310930193334383212861)
                  ·
                    refine ⟨753116598822500393704823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008310930193334383212861 753116598822500393704823)
                    ·
                      rfl

theorem cell22_2200034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2200034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200034 prefixEnd_2200034 := by exact prefixLift 2200034
  have htrace : WordTrace (prefixWord ++ tailWord_2200034) baseStart_2200034 baseEnd_2200034 := by
    simpa [prefixWord, tailWord_2200034, baseEnd_2200034] using wordTrace_append hprefix tailTrace_2200034
  have hstable : (prefixWord ++ tailWord_2200034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200034).length < 2 ^ (prefixWord ++ tailWord_2200034).sum := by decide
  have hdescent : baseEnd_2200034 < baseStart_2200034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200069 : List Nat := [1, 3, 1, 1, 2, 2, 4, 8]
def baseStart_2200069 : Nat := 118140960795 + 2200069 * 2 ^ 59
def prefixEnd_2200069 : Nat := 4983230072969 + 3 ^ 40 * 2200069 * 2
def baseEnd_2200069 : Nat := 83680953337530218786635

theorem tailTrace_2200069 : CollatzResearch.WordTrace tailWord_2200069 prefixEnd_2200069 83680953337530218786635 := by
  unfold tailWord_2200069
  simp only [CollatzResearch.WordTrace]
  refine ⟨80243108666533229715971261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53495405777688819810647507 80243108666533229715971261)
  ·
    refine ⟨30091165749949961143489223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80243108666533229715971261 30091165749949961143489223)
    ·
      refine ⟨45136748624924941715233835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30091165749949961143489223 45136748624924941715233835)
      ·
        refine ⟨67705122937387412572850753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45136748624924941715233835 67705122937387412572850753)
        ·
          refine ⟨50778842203040559429638065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67705122937387412572850753 50778842203040559429638065)
          ·
            refine ⟨38084131652280419572228549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50778842203040559429638065 38084131652280419572228549)
            ·
              refine ⟨7140774684802578669792853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38084131652280419572228549 7140774684802578669792853)
              ·
                refine ⟨83680953337530218786635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7140774684802578669792853 83680953337530218786635)
                ·
                  rfl

theorem cell22_2200069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 8].length) (baseStart_2200069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200069 prefixEnd_2200069 := by exact prefixLift 2200069
  have htrace : WordTrace (prefixWord ++ tailWord_2200069) baseStart_2200069 baseEnd_2200069 := by
    simpa [prefixWord, tailWord_2200069, baseEnd_2200069] using wordTrace_append hprefix tailTrace_2200069
  have hstable : (prefixWord ++ tailWord_2200069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200069).length < 2 ^ (prefixWord ++ tailWord_2200069).sum := by decide
  have hdescent : baseEnd_2200069 < baseStart_2200069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200135 : List Nat := [1, 1, 4, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2200135 : Nat := 118140960795 + 2200135 * 2 ^ 59
def prefixEnd_2200135 : Nat := 4983230072969 + 3 ^ 40 * 2200135 * 2
def baseEnd_2200135 : Nat := 753151173186569796929513

theorem tailTrace_2200135 : CollatzResearch.WordTrace tailWord_2200135 prefixEnd_2200135 753151173186569796929513 := by
  unfold tailWord_2200135
  simp only [CollatzResearch.WordTrace]
  refine ⟨80245515884294122987873859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53497010589529415325249239 80245515884294122987873859)
  ·
    refine ⟨120368273826441184481810789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80245515884294122987873859 120368273826441184481810789)
    ·
      refine ⟨22569051342457722090339523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120368273826441184481810789 22569051342457722090339523)
      ·
        refine ⟨33853577013686583135509285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22569051342457722090339523 33853577013686583135509285)
        ·
          refine ⟨6347545690066234337907991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33853577013686583135509285 6347545690066234337907991)
          ·
            refine ⟨9521318535099351506861987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347545690066234337907991 9521318535099351506861987)
            ·
              refine ⟨14281977802649027260292981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9521318535099351506861987 14281977802649027260292981)
              ·
                refine ⟨1338935418998346305652467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14281977802649027260292981 1338935418998346305652467)
                ·
                  refine ⟨2008403128497519458478701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338935418998346305652467 2008403128497519458478701)
                  ·
                    refine ⟨753151173186569796929513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008403128497519458478701 753151173186569796929513)
                    ·
                      rfl

theorem cell22_2200135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2200135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200135 prefixEnd_2200135 := by exact prefixLift 2200135
  have htrace : WordTrace (prefixWord ++ tailWord_2200135) baseStart_2200135 baseEnd_2200135 := by
    simpa [prefixWord, tailWord_2200135, baseEnd_2200135] using wordTrace_append hprefix tailTrace_2200135
  have hstable : (prefixWord ++ tailWord_2200135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200135).length < 2 ^ (prefixWord ++ tailWord_2200135).sum := by decide
  have hdescent : baseEnd_2200135 < baseStart_2200135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200146 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2200146 : Nat := 118140960795 + 2200146 * 2 ^ 59
def prefixEnd_2200146 : Nat := 4983230072969 + 3 ^ 40 * 2200146 * 2
def baseEnd_2200146 : Nat := 753154938711369434904479

theorem tailTrace_2200146 : CollatzResearch.WordTrace tailWord_2200146 prefixEnd_2200146 753154938711369434904479 := by
  unfold tailWord_2200146
  simp only [CollatzResearch.WordTrace]
  refine ⟨20061479271813567966631073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53497278058169514577682861 20061479271813567966631073)
  ·
    refine ⟨15046109453860175974973305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20061479271813567966631073 15046109453860175974973305)
    ·
      refine ⟨11284582090395131981229979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15046109453860175974973305 11284582090395131981229979)
      ·
        refine ⟨16926873135592697971844969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11284582090395131981229979 16926873135592697971844969)
        ·
          refine ⟨12695154851694523478883727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16926873135592697971844969 12695154851694523478883727)
          ·
            refine ⟨19042732277541785218325591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12695154851694523478883727 19042732277541785218325591)
            ·
              refine ⟨28564098416312677827488387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19042732277541785218325591 28564098416312677827488387)
              ·
                refine ⟨42846147624469016741232581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28564098416312677827488387 42846147624469016741232581)
                ·
                  refine ⟨8033652679587940638981109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42846147624469016741232581 8033652679587940638981109)
                  ·
                    refine ⟨753154938711369434904479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8033652679587940638981109 753154938711369434904479)
                    ·
                      rfl

theorem cell22_2200146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2200146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200146 prefixEnd_2200146 := by exact prefixLift 2200146
  have htrace : WordTrace (prefixWord ++ tailWord_2200146) baseStart_2200146 baseEnd_2200146 := by
    simpa [prefixWord, tailWord_2200146, baseEnd_2200146] using wordTrace_append hprefix tailTrace_2200146
  have hstable : (prefixWord ++ tailWord_2200146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200146).length < 2 ^ (prefixWord ++ tailWord_2200146).sum := by decide
  have hdescent : baseEnd_2200146 < baseStart_2200146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200148 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 5]
def baseStart_2200148 : Nat := 118140960795 + 2200148 * 2 ^ 59
def prefixEnd_2200148 : Nat := 4983230072969 + 3 ^ 40 * 2200148 * 2
def baseEnd_2200148 : Nat := 251051874450747365451491

theorem tailTrace_2200148 : CollatzResearch.WordTrace tailWord_2200148 prefixEnd_2200148 251051874450747365451491 := by
  unfold tailWord_2200148
  simp only [CollatzResearch.WordTrace]
  refine ⟨40122995016623513104048549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53497326688831350805398065 40122995016623513104048549)
  ·
    refine ⟨7523061565616908707009103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40122995016623513104048549 7523061565616908707009103)
    ·
      refine ⟨11284592348425363060513655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7523061565616908707009103 11284592348425363060513655)
      ·
        refine ⟨16926888522638044590770483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11284592348425363060513655 16926888522638044590770483)
        ·
          refine ⟨25390332783957066886155725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16926888522638044590770483 25390332783957066886155725)
          ·
            refine ⟨9521374793983900082308397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25390332783957066886155725 9521374793983900082308397)
            ·
              refine ⟨3570515547743962530865649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9521374793983900082308397 3570515547743962530865649)
              ·
                refine ⟨2677886660807971898149237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3570515547743962530865649 2677886660807971898149237)
                ·
                  refine ⟨251051874450747365451491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677886660807971898149237 251051874450747365451491)
                  ·
                    rfl

theorem cell22_2200148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_2200148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200148 prefixEnd_2200148 := by exact prefixLift 2200148
  have htrace : WordTrace (prefixWord ++ tailWord_2200148) baseStart_2200148 baseEnd_2200148 := by
    simpa [prefixWord, tailWord_2200148, baseEnd_2200148] using wordTrace_append hprefix tailTrace_2200148
  have hstable : (prefixWord ++ tailWord_2200148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200148).length < 2 ^ (prefixWord ++ tailWord_2200148).sum := by decide
  have hdescent : baseEnd_2200148 < baseStart_2200148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200165 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 5]
def baseStart_2200165 : Nat := 118140960795 + 2200165 * 2 ^ 59
def prefixEnd_2200165 : Nat := 4983230072969 + 3 ^ 40 * 2200165 * 2
def baseEnd_2200165 : Nat := 251053814266553239559807

theorem tailTrace_2200165 : CollatzResearch.WordTrace tailWord_2200165 prefixEnd_2200165 251053814266553239559807 := by
  unfold tailWord_2200165
  simp only [CollatzResearch.WordTrace]
  refine ⟨80246610074185438111465949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53497740049456958740977299 80246610074185438111465949)
  ·
    refine ⟨30092478777819539291799731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80246610074185438111465949 30092478777819539291799731)
    ·
      refine ⟨45138718166729308937699597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30092478777819539291799731 45138718166729308937699597)
      ·
        refine ⟨16927019312523490851637349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45138718166729308937699597 16927019312523490851637349)
        ·
          refine ⟨3173816121098154534682003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16927019312523490851637349 3173816121098154534682003)
          ·
            refine ⟨4760724181647231802023005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173816121098154534682003 4760724181647231802023005)
            ·
              refine ⟨1785271568117711925758627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4760724181647231802023005 1785271568117711925758627)
              ·
                refine ⟨2677907352176567888637941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785271568117711925758627 2677907352176567888637941)
                ·
                  refine ⟨251053814266553239559807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677907352176567888637941 251053814266553239559807)
                  ·
                    rfl

theorem cell22_2200165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_2200165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200165 prefixEnd_2200165 := by exact prefixLift 2200165
  have htrace : WordTrace (prefixWord ++ tailWord_2200165) baseStart_2200165 baseEnd_2200165 := by
    simpa [prefixWord, tailWord_2200165, baseEnd_2200165] using wordTrace_append hprefix tailTrace_2200165
  have hstable : (prefixWord ++ tailWord_2200165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200165).length < 2 ^ (prefixWord ++ tailWord_2200165).sum := by decide
  have hdescent : baseEnd_2200165 < baseStart_2200165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200210 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_2200210 : Nat := 118140960795 + 2200210 * 2 ^ 59
def prefixEnd_2200210 : Nat := 4983230072969 + 3 ^ 40 * 2200210 * 2
def baseEnd_2200210 : Nat := 251058949073098200434761

theorem tailTrace_2200210 : CollatzResearch.WordTrace tailWord_2200210 prefixEnd_2200210 251058949073098200434761 := by
  unfold tailWord_2200210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20062062839755602699213521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53498834239348273864569389 20062062839755602699213521)
  ·
    refine ⟨15046547129816702024410141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20062062839755602699213521 15046547129816702024410141)
    ·
      refine ⟨5642455173681263259153803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15046547129816702024410141 5642455173681263259153803)
      ·
        refine ⟨8463682760521894888730705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5642455173681263259153803 8463682760521894888730705)
        ·
          refine ⟨6347762070391421166548029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8463682760521894888730705 6347762070391421166548029)
          ·
            refine ⟨2380410776396782937455511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6347762070391421166548029 2380410776396782937455511)
            ·
              refine ⟨3570616164595174406183267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380410776396782937455511 3570616164595174406183267)
              ·
                refine ⟨5355924246892761609274901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3570616164595174406183267 5355924246892761609274901)
                ·
                  refine ⟨251058949073098200434761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5355924246892761609274901 251058949073098200434761)
                  ·
                    rfl

theorem cell22_2200210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_2200210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200210 prefixEnd_2200210 := by exact prefixLift 2200210
  have htrace : WordTrace (prefixWord ++ tailWord_2200210) baseStart_2200210 baseEnd_2200210 := by
    simpa [prefixWord, tailWord_2200210, baseEnd_2200210] using wordTrace_append hprefix tailTrace_2200210
  have hstable : (prefixWord ++ tailWord_2200210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200210).length < 2 ^ (prefixWord ++ tailWord_2200210).sum := by decide
  have hdescent : baseEnd_2200210 < baseStart_2200210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200221 : List Nat := [1, 4, 2, 1, 1, 1, 3, 9]
def baseStart_2200221 : Nat := 118140960795 + 2200221 * 2 ^ 59
def prefixEnd_2200221 : Nat := 4983230072969 + 3 ^ 40 * 2200221 * 2
def baseEnd_2200221 : Nat := 83686734749343804364361

theorem tailTrace_2200221 : CollatzResearch.WordTrace tailWord_2200221 prefixEnd_2200221 83686734749343804364361 := by
  unfold tailWord_2200221
  simp only [CollatzResearch.WordTrace]
  refine ⟨80248652561982559675504517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53499101707988373117003011 80248652561982559675504517)
  ·
    refine ⟨15046622355371729939157097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80248652561982559675504517 15046622355371729939157097)
    ·
      refine ⟨11284966766528797454367823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15046622355371729939157097 11284966766528797454367823)
      ·
        refine ⟨16927450149793196181551735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11284966766528797454367823 16927450149793196181551735)
        ·
          refine ⟨25391175224689794272327603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16927450149793196181551735 25391175224689794272327603)
          ·
            refine ⟨38086762837034691408491405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25391175224689794272327603 38086762837034691408491405)
            ·
              refine ⟨14282536063888009278184277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38086762837034691408491405 14282536063888009278184277)
              ·
                refine ⟨83686734749343804364361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14282536063888009278184277 83686734749343804364361)
                ·
                  rfl

theorem cell22_2200221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 9].length) (baseStart_2200221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200221 prefixEnd_2200221 := by exact prefixLift 2200221
  have htrace : WordTrace (prefixWord ++ tailWord_2200221) baseStart_2200221 baseEnd_2200221 := by
    simpa [prefixWord, tailWord_2200221, baseEnd_2200221] using wordTrace_append hprefix tailTrace_2200221
  have hstable : (prefixWord ++ tailWord_2200221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200221).length < 2 ^ (prefixWord ++ tailWord_2200221).sum := by decide
  have hdescent : baseEnd_2200221 < baseStart_2200221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200268 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_2200268 : Nat := 118140960795 + 2200268 * 2 ^ 59
def prefixEnd_2200268 : Nat := 4983230072969 + 3 ^ 40 * 2200268 * 2
def baseEnd_2200268 : Nat := 753196701804601783354105

theorem tailTrace_2200268 : CollatzResearch.WordTrace tailWord_2200268 prefixEnd_2200268 753196701804601783354105 := by
  unfold tailWord_2200268
  simp only [CollatzResearch.WordTrace]
  refine ⟨40125183396406143351232729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53500244528541524468310305 40125183396406143351232729)
  ·
    refine ⟨30093887547304607513424547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40125183396406143351232729 30093887547304607513424547)
    ·
      refine ⟨45140831320956911270136821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30093887547304607513424547 45140831320956911270136821)
      ·
        refine ⟨4231952936339710431575327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45140831320956911270136821 4231952936339710431575327)
        ·
          refine ⟨6347929404509565647362991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231952936339710431575327 6347929404509565647362991)
          ·
            refine ⟨9521894106764348471044487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347929404509565647362991 9521894106764348471044487)
            ·
              refine ⟨14282841160146522706566731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9521894106764348471044487 14282841160146522706566731)
              ·
                refine ⟨21424261740219784059850097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14282841160146522706566731 21424261740219784059850097)
                ·
                  refine ⟨16068196305164838044887573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21424261740219784059850097 16068196305164838044887573)
                  ·
                    refine ⟨753196701804601783354105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16068196305164838044887573 753196701804601783354105)
                    ·
                      rfl

theorem cell22_2200268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_2200268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200268 prefixEnd_2200268 := by exact prefixLift 2200268
  have htrace : WordTrace (prefixWord ++ tailWord_2200268) baseStart_2200268 baseEnd_2200268 := by
    simpa [prefixWord, tailWord_2200268, baseEnd_2200268] using wordTrace_append hprefix tailTrace_2200268
  have hstable : (prefixWord ++ tailWord_2200268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200268).length < 2 ^ (prefixWord ++ tailWord_2200268).sum := by decide
  have hdescent : baseEnd_2200268 < baseStart_2200268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200311 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 10]
def baseStart_2200311 : Nat := 118140960795 + 2200311 * 2 ^ 59
def prefixEnd_2200311 : Nat := 4983230072969 + 3 ^ 40 * 2200311 * 2
def baseEnd_2200311 : Nat := 251070473861121334842991

theorem tailTrace_2200311 : CollatzResearch.WordTrace tailWord_2200311 prefixEnd_2200311 251070473861121334842991 := by
  unfold tailWord_2200311
  simp only [CollatzResearch.WordTrace]
  refine ⟨80251935131656505046280787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53501290087771003364187191 80251935131656505046280787)
  ·
    refine ⟨120377902697484757569421181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80251935131656505046280787 120377902697484757569421181)
    ·
      refine ⟨45141713511556784088532943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120377902697484757569421181 45141713511556784088532943)
      ·
        refine ⟨67712570267335176132799415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45141713511556784088532943 67712570267335176132799415)
        ·
          refine ⟨101568855401002764199199123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67712570267335176132799415 101568855401002764199199123)
          ·
            refine ⟨152353283101504146298798685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101568855401002764199199123 152353283101504146298798685)
            ·
              refine ⟨57132481163064054862049507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152353283101504146298798685 57132481163064054862049507)
              ·
                refine ⟨85698721744596082293074261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57132481163064054862049507 85698721744596082293074261)
                ·
                  refine ⟨251070473861121334842991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 85698721744596082293074261 251070473861121334842991)
                  ·
                    rfl

theorem cell22_2200311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 10].length) (baseStart_2200311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200311 prefixEnd_2200311 := by exact prefixLift 2200311
  have htrace : WordTrace (prefixWord ++ tailWord_2200311) baseStart_2200311 baseEnd_2200311 := by
    simpa [prefixWord, tailWord_2200311, baseEnd_2200311] using wordTrace_append hprefix tailTrace_2200311
  have hstable : (prefixWord ++ tailWord_2200311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200311).length < 2 ^ (prefixWord ++ tailWord_2200311).sum := by decide
  have hdescent : baseEnd_2200311 < baseStart_2200311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200328 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 6]
def baseStart_2200328 : Nat := 118140960795 + 2200328 * 2 ^ 59
def prefixEnd_2200328 : Nat := 4983230072969 + 3 ^ 40 * 2200328 * 2
def baseEnd_2200328 : Nat := 251072413676927208951307

theorem tailTrace_2200328 : CollatzResearch.WordTrace tailWord_2200328 prefixEnd_2200328 251072413676927208951307 := by
  unfold tailWord_2200328
  simp only [CollatzResearch.WordTrace]
  refine ⟨40126277586297458474824819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53501703448396611299766425 40126277586297458474824819)
  ·
    refine ⟨60189416379446187712237229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40126277586297458474824819 60189416379446187712237229)
    ·
      refine ⟨22571031142292320392088961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60189416379446187712237229 22571031142292320392088961)
      ·
        refine ⟨16928273356719240294066721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22571031142292320392088961 16928273356719240294066721)
        ·
          refine ⟨12696205017539430220550041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16928273356719240294066721 12696205017539430220550041)
          ·
            refine ⟨9522153763154572665412531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12696205017539430220550041 9522153763154572665412531)
            ·
              refine ⟨14283230644731858998118797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9522153763154572665412531 14283230644731858998118797)
              ·
                refine ⟨5356211491774447124294549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14283230644731858998118797 5356211491774447124294549)
                ·
                  refine ⟨251072413676927208951307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5356211491774447124294549 251072413676927208951307)
                  ·
                    rfl

theorem cell22_2200328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_2200328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200328 prefixEnd_2200328 := by exact prefixLift 2200328
  have htrace : WordTrace (prefixWord ++ tailWord_2200328) baseStart_2200328 baseEnd_2200328 := by
    simpa [prefixWord, tailWord_2200328, baseEnd_2200328] using wordTrace_append hprefix tailTrace_2200328
  have hstable : (prefixWord ++ tailWord_2200328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200328).length < 2 ^ (prefixWord ++ tailWord_2200328).sum := by decide
  have hdescent : baseEnd_2200328 < baseStart_2200328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200360 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2200360 : Nat := 118140960795 + 2200360 * 2 ^ 59
def prefixEnd_2200360 : Nat := 4983230072969 + 3 ^ 40 * 2200360 * 2
def baseEnd_2200360 : Nat := 753228195284744210053823

theorem tailTrace_2200360 : CollatzResearch.WordTrace tailWord_2200360 prefixEnd_2200360 753228195284744210053823 := by
  unfold tailWord_2200360
  simp only [CollatzResearch.WordTrace]
  refine ⟨40126861154239493207407267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53502481538985990943209689 40126861154239493207407267)
  ·
    refine ⟨60190291731359239811110901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40126861154239493207407267 60190291731359239811110901)
    ·
      refine ⟨5642839849814928732291647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60190291731359239811110901 5642839849814928732291647)
      ·
        refine ⟨8464259774722393098437471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5642839849814928732291647 8464259774722393098437471)
        ·
          refine ⟨12696389662083589647656207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8464259774722393098437471 12696389662083589647656207)
          ·
            refine ⟨19044584493125384471484311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12696389662083589647656207 19044584493125384471484311)
            ·
              refine ⟨28566876739688076707226467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19044584493125384471484311 28566876739688076707226467)
              ·
                refine ⟨42850315109532115060839701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28566876739688076707226467 42850315109532115060839701)
                ·
                  refine ⟨2008608520759317893476861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42850315109532115060839701 2008608520759317893476861)
                  ·
                    refine ⟨753228195284744210053823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008608520759317893476861 753228195284744210053823)
                    ·
                      rfl

theorem cell22_2200360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2200360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200360 prefixEnd_2200360 := by exact prefixLift 2200360
  have htrace : WordTrace (prefixWord ++ tailWord_2200360) baseStart_2200360 baseEnd_2200360 := by
    simpa [prefixWord, tailWord_2200360, baseEnd_2200360] using wordTrace_append hprefix tailTrace_2200360
  have hstable : (prefixWord ++ tailWord_2200360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200360).length < 2 ^ (prefixWord ++ tailWord_2200360).sum := by decide
  have hdescent : baseEnd_2200360 < baseStart_2200360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200373 : List Nat := [1, 3, 3, 1, 3, 1, 10]
def baseStart_2200373 : Nat := 118140960795 + 2200373 * 2 ^ 59
def prefixEnd_2200373 : Nat := 4983230072969 + 3 ^ 40 * 2200373 * 2
def baseEnd_2200373 : Nat := 27897505387052463314029

theorem tailTrace_2200373 : CollatzResearch.WordTrace tailWord_2200373 prefixEnd_2200373 27897505387052463314029 := by
  unfold tailWord_2200373
  simp only [CollatzResearch.WordTrace]
  refine ⟨80254196457431889635037773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53502797638287926423358515 80254196457431889635037773)
  ·
    refine ⟨30095323671536958613139165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80254196457431889635037773 30095323671536958613139165)
    ·
      refine ⟨11285746376826359479927187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30095323671536958613139165 11285746376826359479927187)
      ·
        refine ⟨16928619565239539219890781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11285746376826359479927187 16928619565239539219890781)
        ·
          refine ⟨6348232336964827207459043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16928619565239539219890781 6348232336964827207459043)
          ·
            refine ⟨9522348505447240811188565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348232336964827207459043 9522348505447240811188565)
            ·
              refine ⟨27897505387052463314029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9522348505447240811188565 27897505387052463314029)
              ·
                rfl

theorem cell22_2200373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 10].length) (baseStart_2200373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200373 prefixEnd_2200373 := by exact prefixLift 2200373
  have htrace : WordTrace (prefixWord ++ tailWord_2200373) baseStart_2200373 baseEnd_2200373 := by
    simpa [prefixWord, tailWord_2200373, baseEnd_2200373] using wordTrace_append hprefix tailTrace_2200373
  have hstable : (prefixWord ++ tailWord_2200373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200373).length < 2 ^ (prefixWord ++ tailWord_2200373).sum := by decide
  have hdescent : baseEnd_2200373 < baseStart_2200373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200405 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_2200405 : Nat := 118140960795 + 2200405 * 2 ^ 59
def prefixEnd_2200405 : Nat := 4983230072969 + 3 ^ 40 * 2200405 * 2
def baseEnd_2200405 : Nat := 753243599704379092678685

theorem tailTrace_2200405 : CollatzResearch.WordTrace tailWord_2200405 prefixEnd_2200405 753243599704379092678685 := by
  unfold tailWord_2200405
  simp only [CollatzResearch.WordTrace]
  refine ⟨80255363593315959100202669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53503575728877306066801779 80255363593315959100202669)
  ·
    refine ⟨30095761347493484662576001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80255363593315959100202669 30095761347493484662576001)
    ·
      refine ⟨22571821010620113496932001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30095761347493484662576001 22571821010620113496932001)
      ·
        refine ⟨16928865757965085122699001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22571821010620113496932001 16928865757965085122699001)
        ·
          refine ⟨12696649318473813842024251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16928865757965085122699001 12696649318473813842024251)
          ·
            refine ⟨19044973977710720763036377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12696649318473813842024251 19044973977710720763036377)
            ·
              refine ⟨14283730483283040572277283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19044973977710720763036377 14283730483283040572277283)
              ·
                refine ⟨21425595724924560858415925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14283730483283040572277283 21425595724924560858415925)
                ·
                  refine ⟨2008649599211677580476493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21425595724924560858415925 2008649599211677580476493)
                  ·
                    refine ⟨753243599704379092678685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008649599211677580476493 753243599704379092678685)
                    ·
                      rfl

theorem cell22_2200405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_2200405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200405 prefixEnd_2200405 := by exact prefixLift 2200405
  have htrace : WordTrace (prefixWord ++ tailWord_2200405) baseStart_2200405 baseEnd_2200405 := by
    simpa [prefixWord, tailWord_2200405, baseEnd_2200405] using wordTrace_append hprefix tailTrace_2200405
  have hstable : (prefixWord ++ tailWord_2200405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200405).length < 2 ^ (prefixWord ++ tailWord_2200405).sum := by decide
  have hdescent : baseEnd_2200405 < baseStart_2200405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200465 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_2200465 : Nat := 118140960795 + 2200465 * 2 ^ 59
def prefixEnd_2200465 : Nat := 4983230072969 + 3 ^ 40 * 2200465 * 2
def baseEnd_2200465 : Nat := 753264138930558936178501

theorem tailTrace_2200465 : CollatzResearch.WordTrace tailWord_2200465 prefixEnd_2200465 753264138930558936178501 := by
  unfold tailWord_2200465
  simp only [CollatzResearch.WordTrace]
  refine ⟨80257551973098589347386849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53505034648732392898257899 80257551973098589347386849)
  ·
    refine ⟨60193163979823942010540137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80257551973098589347386849 60193163979823942010540137)
    ·
      refine ⟨45144872984867956507905103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60193163979823942010540137 45144872984867956507905103)
      ·
        refine ⟨67717309477301934761857655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45144872984867956507905103 67717309477301934761857655)
        ·
          refine ⟨101575964215952902142786483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67717309477301934761857655 101575964215952902142786483)
          ·
            refine ⟨152363946323929353214179725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101575964215952902142786483 152363946323929353214179725)
            ·
              refine ⟨57136479871473507455317397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152363946323929353214179725 57136479871473507455317397)
              ·
                refine ⟨2678272493975320661968003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57136479871473507455317397 2678272493975320661968003)
                ·
                  refine ⟨4017408740962980992952005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678272493975320661968003 4017408740962980992952005)
                  ·
                    refine ⟨753264138930558936178501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4017408740962980992952005 753264138930558936178501)
                    ·
                      rfl

theorem cell22_2200465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_2200465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200465 prefixEnd_2200465 := by exact prefixLift 2200465
  have htrace : WordTrace (prefixWord ++ tailWord_2200465) baseStart_2200465 baseEnd_2200465 := by
    simpa [prefixWord, tailWord_2200465, baseEnd_2200465] using wordTrace_append hprefix tailTrace_2200465
  have hstable : (prefixWord ++ tailWord_2200465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200465).length < 2 ^ (prefixWord ++ tailWord_2200465).sum := by decide
  have hdescent : baseEnd_2200465 < baseStart_2200465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200497 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 6]
def baseStart_2200497 : Nat := 118140960795 + 2200497 * 2 ^ 59
def prefixEnd_2200497 : Nat := 4983230072969 + 3 ^ 40 * 2200497 * 2
def baseEnd_2200497 : Nat := 251091697728173839792801

theorem tailTrace_2200497 : CollatzResearch.WordTrace tailWord_2200497 prefixEnd_2200497 251091697728173839792801 := by
  unfold tailWord_2200497
  simp only [CollatzResearch.WordTrace]
  refine ⟨80258719108982658812551745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53505812739321772541701163 80258719108982658812551745)
  ·
    refine ⟨60194039331736994109413809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80258719108982658812551745 60194039331736994109413809)
    ·
      refine ⟨45145529498802745582060357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60194039331736994109413809 45145529498802745582060357)
      ·
        refine ⟨8464786781025514796636317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45145529498802745582060357 8464786781025514796636317)
        ·
          refine ⟨3174295042884568048738619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8464786781025514796636317 3174295042884568048738619)
          ·
            refine ⟨4761442564326852073107929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174295042884568048738619 4761442564326852073107929)
            ·
              refine ⟨3571081923245139054830947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4761442564326852073107929 3571081923245139054830947)
              ·
                refine ⟨5356622884867708582246421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571081923245139054830947 5356622884867708582246421)
                ·
                  refine ⟨251091697728173839792801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5356622884867708582246421 251091697728173839792801)
                  ·
                    rfl

theorem cell22_2200497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_2200497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200497 prefixEnd_2200497 := by exact prefixLift 2200497
  have htrace : WordTrace (prefixWord ++ tailWord_2200497) baseStart_2200497 baseEnd_2200497 := by
    simpa [prefixWord, tailWord_2200497, baseEnd_2200497] using wordTrace_append hprefix tailTrace_2200497
  have hstable : (prefixWord ++ tailWord_2200497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200497).length < 2 ^ (prefixWord ++ tailWord_2200497).sum := by decide
  have hdescent : baseEnd_2200497 < baseStart_2200497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200510 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2200510 : Nat := 118140960795 + 2200510 * 2 ^ 59
def prefixEnd_2200510 : Nat := 4983230072969 + 3 ^ 40 * 2200510 * 2
def baseEnd_2200510 : Nat := 753279543350193818803363

theorem tailTrace_2200510 : CollatzResearch.WordTrace tailWord_2200510 prefixEnd_2200510 753279543350193818803363 := by
  unfold tailWord_2200510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10032399157241945254096873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53506128838623708021849989 10032399157241945254096873)
  ·
    refine ⟨7524299367931458940572655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10032399157241945254096873 7524299367931458940572655)
    ·
      refine ⟨11286449051897188410858983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7524299367931458940572655 11286449051897188410858983)
      ·
        refine ⟨16929673577845782616288475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11286449051897188410858983 16929673577845782616288475)
        ·
          refine ⟨25394510366768673924432713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16929673577845782616288475 25394510366768673924432713)
          ·
            refine ⟨19045882775076505443324535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25394510366768673924432713 19045882775076505443324535)
            ·
              refine ⟨28568824162614758164986803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19045882775076505443324535 28568824162614758164986803)
              ·
                refine ⟨42853236243922137247480205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28568824162614758164986803 42853236243922137247480205)
                ·
                  refine ⟨16069963591470801467805077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42853236243922137247480205 16069963591470801467805077)
                  ·
                    refine ⟨753279543350193818803363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16069963591470801467805077 753279543350193818803363)
                    ·
                      rfl

theorem cell22_2200510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2200510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200510 prefixEnd_2200510 := by exact prefixLift 2200510
  have htrace : WordTrace (prefixWord ++ tailWord_2200510) baseStart_2200510 baseEnd_2200510 := by
    simpa [prefixWord, tailWord_2200510, baseEnd_2200510] using wordTrace_append hprefix tailTrace_2200510
  have hstable : (prefixWord ++ tailWord_2200510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200510).length < 2 ^ (prefixWord ++ tailWord_2200510).sum := by decide
  have hdescent : baseEnd_2200510 < baseStart_2200510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200512 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 1, 5]
def baseStart_2200512 : Nat := 118140960795 + 2200512 * 2 ^ 59
def prefixEnd_2200512 : Nat := 4983230072969 + 3 ^ 40 * 2200512 * 2
def baseEnd_2200512 : Nat := 753280227991066480253357

theorem tailTrace_2200512 : CollatzResearch.WordTrace tailWord_2200512 prefixEnd_2200512 753280227991066480253357 := by
  unfold tailWord_2200512
  simp only [CollatzResearch.WordTrace]
  refine ⟨40129633101964158187173895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53506177469285544249565193 40129633101964158187173895)
  ·
    refine ⟨60194449652946237280760843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40129633101964158187173895 60194449652946237280760843)
    ·
      refine ⟨90291674479419355921141265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60194449652946237280760843 90291674479419355921141265)
      ·
        refine ⟨67718755859564516940855949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90291674479419355921141265 67718755859564516940855949)
        ·
          refine ⟨25394533447336693852820981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67718755859564516940855949 25394533447336693852820981)
          ·
            refine ⟨2380737510687815048701967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25394533447336693852820981 2380737510687815048701967)
            ·
              refine ⟨3571106266031722573052951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380737510687815048701967 3571106266031722573052951)
              ·
                refine ⟨5356659399047583859579427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571106266031722573052951 5356659399047583859579427)
                ·
                  refine ⟨8034989098571375789369141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356659399047583859579427 8034989098571375789369141)
                  ·
                    refine ⟨753280227991066480253357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8034989098571375789369141 753280227991066480253357)
                    ·
                      rfl

theorem cell22_2200512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_2200512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200512 prefixEnd_2200512 := by exact prefixLift 2200512
  have htrace : WordTrace (prefixWord ++ tailWord_2200512) baseStart_2200512 baseEnd_2200512 := by
    simpa [prefixWord, tailWord_2200512, baseEnd_2200512] using wordTrace_append hprefix tailTrace_2200512
  have hstable : (prefixWord ++ tailWord_2200512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200512).length < 2 ^ (prefixWord ++ tailWord_2200512).sum := by decide
  have hdescent : baseEnd_2200512 < baseStart_2200512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200516 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2200516 : Nat := 118140960795 + 2200516 * 2 ^ 59
def prefixEnd_2200516 : Nat := 4983230072969 + 3 ^ 40 * 2200516 * 2
def baseEnd_2200516 : Nat := 753281597272811803153345

theorem tailTrace_2200516 : CollatzResearch.WordTrace tailWord_2200516 prefixEnd_2200516 753281597272811803153345 := by
  unfold tailWord_2200516
  simp only [CollatzResearch.WordTrace]
  refine ⟨40129706047956912528746701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53506274730609216704995601 40129706047956912528746701)
  ·
    refine ⟨15048639767983842198280013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40129706047956912528746701 15048639767983842198280013)
    ·
      refine ⟨5643239912993940824355005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15048639767983842198280013 5643239912993940824355005)
      ·
        refine ⟨2116214967372727809133127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5643239912993940824355005 2116214967372727809133127)
        ·
          refine ⟨3174322451059091713699691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116214967372727809133127 3174322451059091713699691)
          ·
            refine ⟨4761483676588637570549537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174322451059091713699691 4761483676588637570549537)
            ·
              refine ⟨3571112757441478177912153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4761483676588637570549537 3571112757441478177912153)
              ·
                refine ⟨2678334568081108633434115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571112757441478177912153 2678334568081108633434115)
                ·
                  refine ⟨4017501852121662950151173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678334568081108633434115 4017501852121662950151173)
                  ·
                    refine ⟨753281597272811803153345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4017501852121662950151173 753281597272811803153345)
                    ·
                      rfl

theorem cell22_2200516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2200516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200516 prefixEnd_2200516 := by exact prefixLift 2200516
  have htrace : WordTrace (prefixWord ++ tailWord_2200516) baseStart_2200516 baseEnd_2200516 := by
    simpa [prefixWord, tailWord_2200516, baseEnd_2200516] using wordTrace_append hprefix tailTrace_2200516
  have hstable : (prefixWord ++ tailWord_2200516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200516).length < 2 ^ (prefixWord ++ tailWord_2200516).sum := by decide
  have hdescent : baseEnd_2200516 < baseStart_2200516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200604 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 5]
def baseStart_2200604 : Nat := 118140960795 + 2200604 * 2 ^ 59
def prefixEnd_2200604 : Nat := 4983230072969 + 3 ^ 40 * 2200604 * 2
def baseEnd_2200604 : Nat := 251103907157069635651025

theorem tailTrace_2200604 : CollatzResearch.WordTrace tailWord_2200604 prefixEnd_2200604 251103907157069635651025 := by
  unfold tailWord_2200604
  simp only [CollatzResearch.WordTrace]
  refine ⟨40131310859797508043348433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53508414479730010724464577 40131310859797508043348433)
  ·
    refine ⟨30098483144848131032511325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40131310859797508043348433 30098483144848131032511325)
    ·
      refine ⟨11286931179318049137191747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30098483144848131032511325 11286931179318049137191747)
      ·
        refine ⟨16930396768977073705787621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11286931179318049137191747 16930396768977073705787621)
        ·
          refine ⟨3174449394183201319835179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16930396768977073705787621 3174449394183201319835179)
          ·
            refine ⟨4761674091274801979752769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174449394183201319835179 4761674091274801979752769)
            ·
              refine ⟨3571255568456101484814577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4761674091274801979752769 3571255568456101484814577)
              ·
                refine ⟨2678441676342076113610933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571255568456101484814577 2678441676342076113610933)
                ·
                  refine ⟨251103907157069635651025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2678441676342076113610933 251103907157069635651025)
                  ·
                    rfl

theorem cell22_2200604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_2200604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200604 prefixEnd_2200604 := by exact prefixLift 2200604
  have htrace : WordTrace (prefixWord ++ tailWord_2200604) baseStart_2200604 baseEnd_2200604 := by
    simpa [prefixWord, tailWord_2200604, baseEnd_2200604] using wordTrace_append hprefix tailTrace_2200604
  have hstable : (prefixWord ++ tailWord_2200604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200604).length < 2 ^ (prefixWord ++ tailWord_2200604).sum := by decide
  have hdescent : baseEnd_2200604 < baseStart_2200604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200608 : List Nat := [2, 1, 1, 7, 1, 1, 1, 4, 1, 3]
def baseStart_2200608 : Nat := 118140960795 + 2200608 * 2 ^ 59
def prefixEnd_2200608 : Nat := 4983230072969 + 3 ^ 40 * 2200608 * 2
def baseEnd_2200608 : Nat := 753313090752954229853063

theorem tailTrace_2200608 : CollatzResearch.WordTrace tailWord_2200608 prefixEnd_2200608 753313090752954229853063 := by
  unfold tailWord_2200608
  simp only [CollatzResearch.WordTrace]
  refine ⟨40131383805790262384921239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53508511741053683179894985 40131383805790262384921239)
  ·
    refine ⟨60197075708685393577381859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40131383805790262384921239 60197075708685393577381859)
    ·
      refine ⟨90295613563028090366072789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60197075708685393577381859 90295613563028090366072789)
      ·
        refine ⟨2116303442883470867954831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 90295613563028090366072789 2116303442883470867954831)
        ·
          refine ⟨3174455164325206301932247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116303442883470867954831 3174455164325206301932247)
          ·
            refine ⟨4761682746487809452898371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174455164325206301932247 4761682746487809452898371)
            ·
              refine ⟨7142524119731714179347557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4761682746487809452898371 7142524119731714179347557)
              ·
                refine ⟨1339223272449696408627667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7142524119731714179347557 1339223272449696408627667)
                ·
                  refine ⟨2008834908674544612941501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339223272449696408627667 2008834908674544612941501)
                  ·
                    refine ⟨753313090752954229853063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008834908674544612941501 753313090752954229853063)
                    ·
                      rfl

theorem cell22_2200608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 3].length) (baseStart_2200608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200608 prefixEnd_2200608 := by exact prefixLift 2200608
  have htrace : WordTrace (prefixWord ++ tailWord_2200608) baseStart_2200608 baseEnd_2200608 := by
    simpa [prefixWord, tailWord_2200608, baseEnd_2200608] using wordTrace_append hprefix tailTrace_2200608
  have hstable : (prefixWord ++ tailWord_2200608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200608).length < 2 ^ (prefixWord ++ tailWord_2200608).sum := by decide
  have hdescent : baseEnd_2200608 < baseStart_2200608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200632 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 6]
def baseStart_2200632 : Nat := 118140960795 + 2200632 * 2 ^ 59
def prefixEnd_2200632 : Nat := 4983230072969 + 3 ^ 40 * 2200632 * 2
def baseEnd_2200632 : Nat := 251107102147808722417663

theorem tailTrace_2200632 : CollatzResearch.WordTrace tailWord_2200632 prefixEnd_2200632 251107102147808722417663 := by
  unfold tailWord_2200632
  simp only [CollatzResearch.WordTrace]
  refine ⟨40131821481746788434358075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53509095308995717912477433 40131821481746788434358075)
  ·
    refine ⟨60197732222620182651537113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40131821481746788434358075 60197732222620182651537113)
    ·
      refine ⟨45148299166965136988652835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60197732222620182651537113 45148299166965136988652835)
      ·
        refine ⟨67722448750447705482979253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45148299166965136988652835 67722448750447705482979253)
        ·
          refine ⟨6348979570354472389029305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67722448750447705482979253 6348979570354472389029305)
          ·
            refine ⟨4761734677765854291771979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6348979570354472389029305 4761734677765854291771979)
            ·
              refine ⟨7142602016648781437657969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4761734677765854291771979 7142602016648781437657969)
              ·
                refine ⟨5356951512486586078243477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7142602016648781437657969 5356951512486586078243477)
                ·
                  refine ⟨251107102147808722417663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5356951512486586078243477 251107102147808722417663)
                  ·
                    rfl

theorem cell22_2200632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_2200632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200632 prefixEnd_2200632 := by exact prefixLift 2200632
  have htrace : WordTrace (prefixWord ++ tailWord_2200632) baseStart_2200632 baseEnd_2200632 := by
    simpa [prefixWord, tailWord_2200632, baseEnd_2200632] using wordTrace_append hprefix tailTrace_2200632
  have hstable : (prefixWord ++ tailWord_2200632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200632).length < 2 ^ (prefixWord ++ tailWord_2200632).sum := by decide
  have hdescent : baseEnd_2200632 < baseStart_2200632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200647 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 1, 5]
def baseStart_2200647 : Nat := 118140960795 + 2200647 * 2 ^ 59
def prefixEnd_2200647 : Nat := 4983230072969 + 3 ^ 40 * 2200647 * 2
def baseEnd_2200647 : Nat := 753326441249971128127943

theorem tailTrace_2200647 : CollatzResearch.WordTrace tailWord_2200647 prefixEnd_2200647 753326441249971128127943 := by
  unfold tailWord_2200647
  simp only [CollatzResearch.WordTrace]
  refine ⟨80264190058439234430512195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53509460038959489620341463 80264190058439234430512195)
  ·
    refine ⟨120396285087658851645768293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80264190058439234430512195 120396285087658851645768293)
    ·
      refine ⟨22574303453936034683581555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120396285087658851645768293 22574303453936034683581555)
      ·
        refine ⟨33861455180904052025372333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22574303453936034683581555 33861455180904052025372333)
        ·
          refine ⟨12698045692839019509514625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33861455180904052025372333 12698045692839019509514625)
          ·
            refine ⟨9523534269629264632135969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12698045692839019509514625 9523534269629264632135969)
            ·
              refine ⟨7142650702221948474101977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9523534269629264632135969 7142650702221948474101977)
              ·
                refine ⟨5356988026666461355576483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7142650702221948474101977 5356988026666461355576483)
                ·
                  refine ⟨8035482039999692033364725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356988026666461355576483 8035482039999692033364725)
                  ·
                    refine ⟨753326441249971128127943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8035482039999692033364725 753326441249971128127943)
                    ·
                      rfl

theorem cell22_2200647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_2200647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200647 prefixEnd_2200647 := by exact prefixLift 2200647
  have htrace : WordTrace (prefixWord ++ tailWord_2200647) baseStart_2200647 baseEnd_2200647 := by
    simpa [prefixWord, tailWord_2200647, baseEnd_2200647] using wordTrace_append hprefix tailTrace_2200647
  have hstable : (prefixWord ++ tailWord_2200647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200647).length < 2 ^ (prefixWord ++ tailWord_2200647).sum := by decide
  have hdescent : baseEnd_2200647 < baseStart_2200647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200681 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 2, 3]
def baseStart_2200681 : Nat := 118140960795 + 2200681 * 2 ^ 59
def prefixEnd_2200681 : Nat := 4983230072969 + 3 ^ 40 * 2200681 * 2
def baseEnd_2200681 : Nat := 753338080144806372777839

theorem tailTrace_2200681 : CollatzResearch.WordTrace tailWord_2200681 prefixEnd_2200681 753338080144806372777839 := by
  unfold tailWord_2200681
  simp only [CollatzResearch.WordTrace]
  refine ⟨80265430140316058237249897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53510286760210705491499931 80265430140316058237249897)
  ·
    refine ⟨60199072605237043677937423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80265430140316058237249897 60199072605237043677937423)
    ·
      refine ⟨90298608907855565516906135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60199072605237043677937423 90298608907855565516906135)
      ·
        refine ⟨135447913361783348275359203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90298608907855565516906135 135447913361783348275359203)
        ·
          refine ⟨203171870042675022413038805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135447913361783348275359203 203171870042675022413038805)
          ·
            refine ⟨4761840704125195837805597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 203171870042675022413038805 4761840704125195837805597)
            ·
              refine ⟨1785690264046948439177099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4761840704125195837805597 1785690264046948439177099)
              ·
                refine ⟨2678535396070422658765649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785690264046948439177099 2678535396070422658765649)
                ·
                  refine ⟨2008901547052816994074237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2678535396070422658765649 2008901547052816994074237)
                  ·
                    refine ⟨753338080144806372777839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008901547052816994074237 753338080144806372777839)
                    ·
                      rfl

theorem cell22_2200681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 3].length) (baseStart_2200681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200681 prefixEnd_2200681 := by exact prefixLift 2200681
  have htrace : WordTrace (prefixWord ++ tailWord_2200681) baseStart_2200681 baseEnd_2200681 := by
    simpa [prefixWord, tailWord_2200681, baseEnd_2200681] using wordTrace_append hprefix tailTrace_2200681
  have hstable : (prefixWord ++ tailWord_2200681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200681).length < 2 ^ (prefixWord ++ tailWord_2200681).sum := by decide
  have hdescent : baseEnd_2200681 < baseStart_2200681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200737 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2200737 : Nat := 118140960795 + 2200737 * 2 ^ 59
def prefixEnd_2200737 : Nat := 4983230072969 + 3 ^ 40 * 2200737 * 2
def baseEnd_2200737 : Nat := 753357250089240893377667

theorem tailTrace_2200737 : CollatzResearch.WordTrace tailWord_2200737 prefixEnd_2200737 753357250089240893377667 := by
  unfold tailWord_2200737
  simp only [CollatzResearch.WordTrace]
  refine ⟨80267472628113179801288465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53511648418742119867525643 80267472628113179801288465)
  ·
    refine ⟨60200604471084884850966349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80267472628113179801288465 60200604471084884850966349)
    ·
      refine ⟨22575226676656831819112381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60200604471084884850966349 22575226676656831819112381)
      ·
        refine ⟨8465710003746311932167143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22575226676656831819112381 8465710003746311932167143)
        ·
          refine ⟨12698565005619467898250715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8465710003746311932167143 12698565005619467898250715)
          ·
            refine ⟨19047847508429201847376073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12698565005619467898250715 19047847508429201847376073)
            ·
              refine ⟨14285885631321901385532055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19047847508429201847376073 14285885631321901385532055)
              ·
                refine ⟨21428828446982852078298083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14285885631321901385532055 21428828446982852078298083)
                ·
                  refine ⟨32143242670474278117447125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21428828446982852078298083 32143242670474278117447125)
                  ·
                    refine ⟨753357250089240893377667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32143242670474278117447125 753357250089240893377667)
                    ·
                      rfl

theorem cell22_2200737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2200737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200737 prefixEnd_2200737 := by exact prefixLift 2200737
  have htrace : WordTrace (prefixWord ++ tailWord_2200737) baseStart_2200737 baseEnd_2200737 := by
    simpa [prefixWord, tailWord_2200737, baseEnd_2200737] using wordTrace_append hprefix tailTrace_2200737
  have hstable : (prefixWord ++ tailWord_2200737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200737).length < 2 ^ (prefixWord ++ tailWord_2200737).sum := by decide
  have hdescent : baseEnd_2200737 < baseStart_2200737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200752 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_2200752 : Nat := 118140960795 + 2200752 * 2 ^ 59
def prefixEnd_2200752 : Nat := 4983230072969 + 3 ^ 40 * 2200752 * 2
def baseEnd_2200752 : Nat := 753362384895785854252621

theorem tailTrace_2200752 : CollatzResearch.WordTrace tailWord_2200752 prefixEnd_2200752 753362384895785854252621 := by
  unfold tailWord_2200752
  simp only [CollatzResearch.WordTrace]
  refine ⟨40134009861529418681542255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53512013148705891575389673 40134009861529418681542255)
  ·
    refine ⟨60201014792294128022313383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40134009861529418681542255 60201014792294128022313383)
    ·
      refine ⟨90301522188441192033470075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60201014792294128022313383 90301522188441192033470075)
      ·
        refine ⟨135452283282661788050205113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90301522188441192033470075 135452283282661788050205113)
        ·
          refine ⟨101589212461996341037653835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135452283282661788050205113 101589212461996341037653835)
          ·
            refine ⟨152383818692994511556480753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101589212461996341037653835 152383818692994511556480753)
            ·
              refine ⟨114287864019745883667360565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152383818692994511556480753 114287864019745883667360565)
              ·
                refine ⟨10714487251851176593815053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114287864019745883667360565 10714487251851176593815053)
                ·
                  refine ⟨4017932719444191222680645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10714487251851176593815053 4017932719444191222680645)
                  ·
                    refine ⟨753362384895785854252621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4017932719444191222680645 753362384895785854252621)
                    ·
                      rfl

theorem cell22_2200752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_2200752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200752 prefixEnd_2200752 := by exact prefixLift 2200752
  have htrace : WordTrace (prefixWord ++ tailWord_2200752) baseStart_2200752 baseEnd_2200752 := by
    simpa [prefixWord, tailWord_2200752, baseEnd_2200752] using wordTrace_append hprefix tailTrace_2200752
  have hstable : (prefixWord ++ tailWord_2200752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200752).length < 2 ^ (prefixWord ++ tailWord_2200752).sum := by decide
  have hdescent : baseEnd_2200752 < baseStart_2200752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200818 : List Nat := [3, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_2200818 : Nat := 118140960795 + 2200818 * 2 ^ 59
def prefixEnd_2200818 : Nat := 4983230072969 + 3 ^ 40 * 2200818 * 2
def baseEnd_2200818 : Nat := 251128326014861227367473

theorem tailTrace_2200818 : CollatzResearch.WordTrace tailWord_2200818 prefixEnd_2200818 251128326014861227367473 := by
  unfold tailWord_2200818
  simp only [CollatzResearch.WordTrace]
  refine ⟨20067606735204932658746777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53513617960546487089991405 20067606735204932658746777)
  ·
    refine ⟨15050705051403699494060083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20067606735204932658746777 15050705051403699494060083)
    ·
      refine ⟨22576057577105549241090125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15050705051403699494060083 22576057577105549241090125)
      ·
        refine ⟨8466021591414580965408797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22576057577105549241090125 8466021591414580965408797)
        ·
          refine ⟨3174758096780467862028299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8466021591414580965408797 3174758096780467862028299)
          ·
            refine ⟨4762137145170701793042449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174758096780467862028299 4762137145170701793042449)
            ·
              refine ⟨3571602858878026344781837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762137145170701793042449 3571602858878026344781837)
              ·
                refine ⟨1339351072079259879293189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3571602858878026344781837 1339351072079259879293189)
                ·
                  refine ⟨251128326014861227367473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1339351072079259879293189 251128326014861227367473)
                  ·
                    rfl

theorem cell22_2200818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_2200818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200818 prefixEnd_2200818 := by exact prefixLift 2200818
  have htrace : WordTrace (prefixWord ++ tailWord_2200818) baseStart_2200818 baseEnd_2200818 := by
    simpa [prefixWord, tailWord_2200818, baseEnd_2200818] using wordTrace_append hprefix tailTrace_2200818
  have hstable : (prefixWord ++ tailWord_2200818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200818).length < 2 ^ (prefixWord ++ tailWord_2200818).sum := by decide
  have hdescent : baseEnd_2200818 < baseStart_2200818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200833 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2200833 : Nat := 118140960795 + 2200833 * 2 ^ 59
def prefixEnd_2200833 : Nat := 4983230072969 + 3 ^ 40 * 2200833 * 2
def baseEnd_2200833 : Nat := 753390112851128642977373

theorem tailTrace_2200833 : CollatzResearch.WordTrace tailWord_2200833 prefixEnd_2200833 753390112851128642977373 := by
  unfold tailWord_2200833
  simp only [CollatzResearch.WordTrace]
  refine ⟨80270974035765388196783153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53513982690510258797855435 80270974035765388196783153)
  ·
    refine ⟨60203230526824041147587365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80270974035765388196783153 60203230526824041147587365)
    ·
      refine ⟨11288105723779507715172631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60203230526824041147587365 11288105723779507715172631)
      ·
        refine ⟨16932158585669261572758947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11288105723779507715172631 16932158585669261572758947)
        ·
          refine ⟨25398237878503892359138421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16932158585669261572758947 25398237878503892359138421)
          ·
            refine ⟨2381084801109739908669227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25398237878503892359138421 2381084801109739908669227)
            ·
              refine ⟨3571627201664609863003841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381084801109739908669227 3571627201664609863003841)
              ·
                refine ⟨2678720401248457397252881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571627201664609863003841 2678720401248457397252881)
                ·
                  refine ⟨2009040300936343047939661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2678720401248457397252881 2009040300936343047939661)
                  ·
                    refine ⟨753390112851128642977373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009040300936343047939661 753390112851128642977373)
                    ·
                      rfl

theorem cell22_2200833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2200833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200833 prefixEnd_2200833 := by exact prefixLift 2200833
  have htrace : WordTrace (prefixWord ++ tailWord_2200833) baseStart_2200833 baseEnd_2200833 := by
    simpa [prefixWord, tailWord_2200833, baseEnd_2200833] using wordTrace_append hprefix tailTrace_2200833
  have hstable : (prefixWord ++ tailWord_2200833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200833).length < 2 ^ (prefixWord ++ tailWord_2200833).sum := by decide
  have hdescent : baseEnd_2200833 < baseStart_2200833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200850 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2200850 : Nat := 118140960795 + 2200850 * 2 ^ 59
def prefixEnd_2200850 : Nat := 4983230072969 + 3 ^ 40 * 2200850 * 2
def baseEnd_2200850 : Nat := 753395932298546265302321

theorem tailTrace_2200850 : CollatzResearch.WordTrace tailWord_2200850 prefixEnd_2200850 753395932298546265302321 := by
  unfold tailWord_2200850
  simp only [CollatzResearch.WordTrace]
  refine ⟨20067898519175950025038001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53514396051135866733434669 20067898519175950025038001)
  ·
    refine ⟨15050923889381962518778501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20067898519175950025038001 15050923889381962518778501)
    ·
      refine ⟨2822048229259117972270969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15050923889381962518778501 2822048229259117972270969)
      ·
        refine ⟨2116536171944338479203227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2822048229259117972270969 2116536171944338479203227)
        ·
          refine ⟨3174804257916507718804841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116536171944338479203227 3174804257916507718804841)
          ·
            refine ⟨2381103193437380789103631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3174804257916507718804841 2381103193437380789103631)
            ·
              refine ⟨3571654790156071183655447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381103193437380789103631 3571654790156071183655447)
              ·
                refine ⟨5357482185234106775483171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571654790156071183655447 5357482185234106775483171)
                ·
                  refine ⟨8036223277851160163224757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357482185234106775483171 8036223277851160163224757)
                  ·
                    refine ⟨753395932298546265302321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8036223277851160163224757 753395932298546265302321)
                    ·
                      rfl

theorem cell22_2200850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2200850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200850 prefixEnd_2200850 := by exact prefixLift 2200850
  have htrace : WordTrace (prefixWord ++ tailWord_2200850) baseStart_2200850 baseEnd_2200850 := by
    simpa [prefixWord, tailWord_2200850, baseEnd_2200850] using wordTrace_append hprefix tailTrace_2200850
  have hstable : (prefixWord ++ tailWord_2200850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200850).length < 2 ^ (prefixWord ++ tailWord_2200850).sum := by decide
  have hdescent : baseEnd_2200850 < baseStart_2200850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200863 : List Nat := [1, 1, 2, 4, 5, 1, 2, 6]
def baseStart_2200863 : Nat := 118140960795 + 2200863 * 2 ^ 59
def prefixEnd_2200863 : Nat := 4983230072969 + 3 ^ 40 * 2200863 * 2
def baseEnd_2200863 : Nat := 83711153607135396080809

theorem tailTrace_2200863 : CollatzResearch.WordTrace tailWord_2200863 prefixEnd_2200863 83711153607135396080809 := by
  unfold tailWord_2200863
  simp only [CollatzResearch.WordTrace]
  refine ⟨80272068225656703320375243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53514712150437802213583495 80272068225656703320375243)
  ·
    refine ⟨120408102338485054980562865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80272068225656703320375243 120408102338485054980562865)
    ·
      refine ⟨90306076753863791235422149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120408102338485054980562865 90306076753863791235422149)
      ·
        refine ⟨16932389391349460856641653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90306076753863791235422149 16932389391349460856641653)
        ·
          refine ⟨1587411505439011955310155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16932389391349460856641653 1587411505439011955310155)
          ·
            refine ⟨2381117258158517932965233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587411505439011955310155 2381117258158517932965233)
            ·
              refine ⟨1785837943618888449723925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2381117258158517932965233 1785837943618888449723925)
              ·
                refine ⟨83711153607135396080809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1785837943618888449723925 83711153607135396080809)
                ·
                  rfl

theorem cell22_2200863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 6].length) (baseStart_2200863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200863 prefixEnd_2200863 := by exact prefixLift 2200863
  have htrace : WordTrace (prefixWord ++ tailWord_2200863) baseStart_2200863 baseEnd_2200863 := by
    simpa [prefixWord, tailWord_2200863, baseEnd_2200863] using wordTrace_append hprefix tailTrace_2200863
  have hstable : (prefixWord ++ tailWord_2200863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200863).length < 2 ^ (prefixWord ++ tailWord_2200863).sum := by decide
  have hdescent : baseEnd_2200863 < baseStart_2200863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200895 : List Nat := [1, 1, 2, 2, 4, 3, 3, 2, 1, 3]
def baseStart_2200895 : Nat := 118140960795 + 2200895 * 2 ^ 59
def prefixEnd_2200895 : Nat := 4983230072969 + 3 ^ 40 * 2200895 * 2
def baseEnd_2200895 : Nat := 753411336718181147927183

theorem tailTrace_2200895 : CollatzResearch.WordTrace tailWord_2200895 prefixEnd_2200895 753411336718181147927183 := by
  unfold tailWord_2200895
  simp only [CollatzResearch.WordTrace]
  refine ⟨80273235361540772785540139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53515490241027181857026759 80273235361540772785540139)
  ·
    refine ⟨120409853042311159178310209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80273235361540772785540139 120409853042311159178310209)
    ·
      refine ⟨90307389781733369383732657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120409853042311159178310209 90307389781733369383732657)
      ·
        refine ⟨67730542336300027037799493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90307389781733369383732657 67730542336300027037799493)
        ·
          refine ⟨12699476688056255069587405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67730542336300027037799493 12699476688056255069587405)
          ·
            refine ⟨4762303758021095651095277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12699476688056255069587405 4762303758021095651095277)
            ·
              refine ⟨1785863909257910869160729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4762303758021095651095277 1785863909257910869160729)
              ·
                refine ⟨1339397931943433151870547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785863909257910869160729 1339397931943433151870547)
                ·
                  refine ⟨2009096897915149727805821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339397931943433151870547 2009096897915149727805821)
                  ·
                    refine ⟨753411336718181147927183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009096897915149727805821 753411336718181147927183)
                    ·
                      rfl

theorem cell22_2200895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 3].length) (baseStart_2200895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200895 prefixEnd_2200895 := by exact prefixLift 2200895
  have htrace : WordTrace (prefixWord ++ tailWord_2200895) baseStart_2200895 baseEnd_2200895 := by
    simpa [prefixWord, tailWord_2200895, baseEnd_2200895] using wordTrace_append hprefix tailTrace_2200895
  have hstable : (prefixWord ++ tailWord_2200895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200895).length < 2 ^ (prefixWord ++ tailWord_2200895).sum := by decide
  have hdescent : baseEnd_2200895 < baseStart_2200895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200904 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_2200904 : Nat := 118140960795 + 2200904 * 2 ^ 59
def prefixEnd_2200904 : Nat := 4983230072969 + 3 ^ 40 * 2200904 * 2
def baseEnd_2200904 : Nat := 753414417602108124452155

theorem tailTrace_2200904 : CollatzResearch.WordTrace tailWord_2200904 prefixEnd_2200904 753414417602108124452155 := by
  unfold tailWord_2200904
  simp only [CollatzResearch.WordTrace]
  refine ⟨40136781809254083661308883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53515709079005444881745177 40136781809254083661308883)
  ·
    refine ⟨60205172713881125491963325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40136781809254083661308883 60205172713881125491963325)
    ·
      refine ⟨22576939767705422059486247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60205172713881125491963325 22576939767705422059486247)
      ·
        refine ⟨33865409651558133089229371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22576939767705422059486247 33865409651558133089229371)
        ·
          refine ⟨50798114477337199633844057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33865409651558133089229371 50798114477337199633844057)
          ·
            refine ⟨38098585858002899725383043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50798114477337199633844057 38098585858002899725383043)
            ·
              refine ⟨57147878787004349588074565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38098585858002899725383043 57147878787004349588074565)
              ·
                refine ⟨10715227272563315547763981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57147878787004349588074565 10715227272563315547763981)
                ·
                  refine ⟨4018210227211243330411493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10715227272563315547763981 4018210227211243330411493)
                  ·
                    refine ⟨753414417602108124452155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4018210227211243330411493 753414417602108124452155)
                    ·
                      rfl

theorem cell22_2200904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_2200904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200904 prefixEnd_2200904 := by exact prefixLift 2200904
  have htrace : WordTrace (prefixWord ++ tailWord_2200904) baseStart_2200904 baseEnd_2200904 := by
    simpa [prefixWord, tailWord_2200904, baseEnd_2200904] using wordTrace_append hprefix tailTrace_2200904
  have hstable : (prefixWord ++ tailWord_2200904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200904).length < 2 ^ (prefixWord ++ tailWord_2200904).sum := by decide
  have hdescent : baseEnd_2200904 < baseStart_2200904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200908 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 5]
def baseStart_2200908 : Nat := 118140960795 + 2200908 * 2 ^ 59
def prefixEnd_2200908 : Nat := 4983230072969 + 3 ^ 40 * 2200908 * 2
def baseEnd_2200908 : Nat := 251138595627951149117381

theorem tailTrace_2200908 : CollatzResearch.WordTrace tailWord_2200908 prefixEnd_2200908 251138595627951149117381 := by
  unfold tailWord_2200908
  simp only [CollatzResearch.WordTrace]
  refine ⟨40136854755246838002881689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53515806340329117337175585 40136854755246838002881689)
  ·
    refine ⟨30102641066435128502161267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40136854755246838002881689 30102641066435128502161267)
    ·
      refine ⟨45153961599652692753241901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30102641066435128502161267 45153961599652692753241901)
      ·
        refine ⟨16932735599869759782465713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45153961599652692753241901 16932735599869759782465713)
        ·
          refine ⟨12699551699902319836849285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16932735599869759782465713 12699551699902319836849285)
          ·
            refine ⟨2381165943731684969409241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12699551699902319836849285 2381165943731684969409241)
            ·
              refine ⟨1785874457798763727056931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2381165943731684969409241 1785874457798763727056931)
              ·
                refine ⟨2678811686698145590585397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785874457798763727056931 2678811686698145590585397)
                ·
                  refine ⟨251138595627951149117381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2678811686698145590585397 251138595627951149117381)
                  ·
                    rfl

theorem cell22_2200908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_2200908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200908 prefixEnd_2200908 := by exact prefixLift 2200908
  have htrace : WordTrace (prefixWord ++ tailWord_2200908) baseStart_2200908 baseEnd_2200908 := by
    simpa [prefixWord, tailWord_2200908, baseEnd_2200908] using wordTrace_append hprefix tailTrace_2200908
  have hstable : (prefixWord ++ tailWord_2200908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200908).length < 2 ^ (prefixWord ++ tailWord_2200908).sum := by decide
  have hdescent : baseEnd_2200908 < baseStart_2200908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200921 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_2200921 : Nat := 118140960795 + 2200921 * 2 ^ 59
def prefixEnd_2200921 : Nat := 4983230072969 + 3 ^ 40 * 2200921 * 2
def baseEnd_2200921 : Nat := 753420237049525746777103

theorem tailTrace_2200921 : CollatzResearch.WordTrace tailWord_2200921 prefixEnd_2200921 753420237049525746777103 := by
  unfold tailWord_2200921
  simp only [CollatzResearch.WordTrace]
  refine ⟨80274183659446579225986617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53516122439631052817324411 80274183659446579225986617)
  ·
    refine ⟨60205637744584934419489963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80274183659446579225986617 60205637744584934419489963)
    ·
      refine ⟨90308456616877401629234945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60205637744584934419489963 90308456616877401629234945)
      ·
        refine ⟨67731342462658051221926209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90308456616877401629234945 67731342462658051221926209)
        ·
          refine ⟨50798506846993538416444657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67731342462658051221926209 50798506846993538416444657)
          ·
            refine ⟨38098880135245153812333493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50798506846993538416444657 38098880135245153812333493)
            ·
              refine ⟨3571770012679233169906265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38098880135245153812333493 3571770012679233169906265)
              ·
                refine ⟨2678827509509424877429699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571770012679233169906265 2678827509509424877429699)
                ·
                  refine ⟨4018241264264137316144549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678827509509424877429699 4018241264264137316144549)
                  ·
                    refine ⟨753420237049525746777103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4018241264264137316144549 753420237049525746777103)
                    ·
                      rfl

theorem cell22_2200921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_2200921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200921 prefixEnd_2200921 := by exact prefixLift 2200921
  have htrace : WordTrace (prefixWord ++ tailWord_2200921) baseStart_2200921 baseEnd_2200921 := by
    simpa [prefixWord, tailWord_2200921, baseEnd_2200921] using wordTrace_append hprefix tailTrace_2200921
  have hstable : (prefixWord ++ tailWord_2200921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200921).length < 2 ^ (prefixWord ++ tailWord_2200921).sum := by decide
  have hdescent : baseEnd_2200921 < baseStart_2200921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200953 : List Nat := [1, 2, 1, 3, 2, 1, 6, 2, 4]
def baseStart_2200953 : Nat := 118140960795 + 2200953 * 2 ^ 59
def prefixEnd_2200953 : Nat := 4983230072969 + 3 ^ 40 * 2200953 * 2
def baseEnd_2200953 : Nat := 251143730434496109992335

theorem tailTrace_2200953 : CollatzResearch.WordTrace tailWord_2200953 prefixEnd_2200953 251143730434496109992335 := by
  unfold tailWord_2200953
  simp only [CollatzResearch.WordTrace]
  refine ⟨80275350795330648691151513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53516900530220432460767675 80275350795330648691151513)
  ·
    refine ⟨60206513096497986518363635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80275350795330648691151513 60206513096497986518363635)
    ·
      refine ⟨90309769644746979777545453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60206513096497986518363635 90309769644746979777545453)
      ·
        refine ⟨33866163616780117416579545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90309769644746979777545453 33866163616780117416579545)
        ·
          refine ⟨25399622712585088062434659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33866163616780117416579545 25399622712585088062434659)
          ·
            refine ⟨38099434068877632093651989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25399622712585088062434659 38099434068877632093651989)
            ·
              refine ⟨1785910971978639004389937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38099434068877632093651989 1785910971978639004389937)
              ·
                refine ⟨1339433228983979253292453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785910971978639004389937 1339433228983979253292453)
                ·
                  refine ⟨251143730434496109992335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1339433228983979253292453 251143730434496109992335)
                  ·
                    rfl

theorem cell22_2200953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 4].length) (baseStart_2200953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200953 prefixEnd_2200953 := by exact prefixLift 2200953
  have htrace : WordTrace (prefixWord ++ tailWord_2200953) baseStart_2200953 baseEnd_2200953 := by
    simpa [prefixWord, tailWord_2200953, baseEnd_2200953] using wordTrace_append hprefix tailTrace_2200953
  have hstable : (prefixWord ++ tailWord_2200953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200953).length < 2 ^ (prefixWord ++ tailWord_2200953).sum := by decide
  have hdescent : baseEnd_2200953 < baseStart_2200953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200968 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 2, 3]
def baseStart_2200968 : Nat := 118140960795 + 2200968 * 2 ^ 59
def prefixEnd_2200968 : Nat := 4983230072969 + 3 ^ 40 * 2200968 * 2
def baseEnd_2200968 : Nat := 753436326110033290851959

theorem tailTrace_2200968 : CollatzResearch.WordTrace tailWord_2200968 prefixEnd_2200968 753436326110033290851959 := by
  unfold tailWord_2200968
  simp only [CollatzResearch.WordTrace]
  refine ⟨40137948945138153126473779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53517265260184204168631705 40137948945138153126473779)
  ·
    refine ⟨60206923417707229689710669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40137948945138153126473779 60206923417707229689710669)
    ·
      refine ⟨22577596281640211133641501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60206923417707229689710669 22577596281640211133641501)
      ·
        refine ⟨8466598605615079175115563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22577596281640211133641501 8466598605615079175115563)
        ·
          refine ⟨12699897908422618762673345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8466598605615079175115563 12699897908422618762673345)
          ·
            refine ⟨9524923431316964072005009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12699897908422618762673345 9524923431316964072005009)
            ·
              refine ⟨7143692573487723054003757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9524923431316964072005009 7143692573487723054003757)
              ·
                refine ⟨2678884715057896145251409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7143692573487723054003757 2678884715057896145251409)
                ·
                  refine ⟨2009163536293422108938557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2678884715057896145251409 2009163536293422108938557)
                  ·
                    refine ⟨753436326110033290851959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009163536293422108938557 753436326110033290851959)
                    ·
                      rfl

theorem cell22_2200968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_2200968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200968 prefixEnd_2200968 := by exact prefixLift 2200968
  have htrace : WordTrace (prefixWord ++ tailWord_2200968) baseStart_2200968 baseEnd_2200968 := by
    simpa [prefixWord, tailWord_2200968, baseEnd_2200968] using wordTrace_append hprefix tailTrace_2200968
  have hstable : (prefixWord ++ tailWord_2200968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200968).length < 2 ^ (prefixWord ++ tailWord_2200968).sum := by decide
  have hdescent : baseEnd_2200968 < baseStart_2200968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200996 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_2200996 : Nat := 118140960795 + 2200996 * 2 ^ 59
def prefixEnd_2200996 : Nat := 4983230072969 + 3 ^ 40 * 2200996 * 2
def baseEnd_2200996 : Nat := 753445911082250551151873

theorem tailTrace_2200996 : CollatzResearch.WordTrace tailWord_2200996 prefixEnd_2200996 753445911082250551151873 := by
  unfold tailWord_2200996
  simp only [CollatzResearch.WordTrace]
  refine ⟨40138459567087433517483421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53517946089449911356644561 40138459567087433517483421)
  ·
    refine ⟨15051922337657787569056283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40138459567087433517483421 15051922337657787569056283)
    ·
      refine ⟨22577883506486681353584425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15051922337657787569056283 22577883506486681353584425)
      ·
        refine ⟨16933412629865011015188319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22577883506486681353584425 16933412629865011015188319)
        ·
          refine ⟨25400118944797516522782479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16933412629865011015188319 25400118944797516522782479)
          ·
            refine ⟨38100178417196274784173719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25400118944797516522782479 38100178417196274784173719)
            ·
              refine ⟨57150267625794412176260579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38100178417196274784173719 57150267625794412176260579)
              ·
                refine ⟨85725401438691618264390869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57150267625794412176260579 85725401438691618264390869)
                ·
                  refine ⟨2009189096219334803071661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 85725401438691618264390869 2009189096219334803071661)
                  ·
                    refine ⟨753445911082250551151873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009189096219334803071661 753445911082250551151873)
                    ·
                      rfl

theorem cell22_2200996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_2200996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2200996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2200996 prefixEnd_2200996 := by exact prefixLift 2200996
  have htrace : WordTrace (prefixWord ++ tailWord_2200996) baseStart_2200996 baseEnd_2200996 := by
    simpa [prefixWord, tailWord_2200996, baseEnd_2200996] using wordTrace_append hprefix tailTrace_2200996
  have hstable : (prefixWord ++ tailWord_2200996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200996).length < 2 ^ (prefixWord ++ tailWord_2200996).sum := by decide
  have hdescent : baseEnd_2200996 < baseStart_2200996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201013 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_2201013 : Nat := 118140960795 + 2201013 * 2 ^ 59
def prefixEnd_2201013 : Nat := 4983230072969 + 3 ^ 40 * 2201013 * 2
def baseEnd_2201013 : Nat := 753451730529668173476821

theorem tailTrace_2201013 : CollatzResearch.WordTrace tailWord_2201013 prefixEnd_2201013 753451730529668173476821 := by
  unfold tailWord_2201013
  simp only [CollatzResearch.WordTrace]
  refine ⟨80277539175113278938335693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53518359450075519292223795 80277539175113278938335693)
  ·
    refine ⟨30104077190667479601875885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80277539175113278938335693 30104077190667479601875885)
    ·
      refine ⟨11289028946500304850703457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30104077190667479601875885 11289028946500304850703457)
      ·
        refine ⟨8466771709875228638027593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11289028946500304850703457 8466771709875228638027593)
        ·
          refine ⟨6350078782406421478520695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8466771709875228638027593 6350078782406421478520695)
          ·
            refine ⟨9525118173609632217781043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6350078782406421478520695 9525118173609632217781043)
            ·
              refine ⟨14287677260414448326671565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9525118173609632217781043 14287677260414448326671565)
              ·
                refine ⟨5357878972655418122501837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14287677260414448326671565 5357878972655418122501837)
                ·
                  refine ⟨2009204614745781795938189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5357878972655418122501837 2009204614745781795938189)
                  ·
                    refine ⟨753451730529668173476821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009204614745781795938189 753451730529668173476821)
                    ·
                      rfl

theorem cell22_2201013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_2201013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201013 prefixEnd_2201013 := by exact prefixLift 2201013
  have htrace : WordTrace (prefixWord ++ tailWord_2201013) baseStart_2201013 baseEnd_2201013 := by
    simpa [prefixWord, tailWord_2201013, baseEnd_2201013] using wordTrace_append hprefix tailTrace_2201013
  have hstable : (prefixWord ++ tailWord_2201013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201013).length < 2 ^ (prefixWord ++ tailWord_2201013).sum := by decide
  have hdescent : baseEnd_2201013 < baseStart_2201013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201071 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 6]
def baseStart_2201071 : Nat := 118140960795 + 2201071 * 2 ^ 59
def prefixEnd_2201071 : Nat := 4983230072969 + 3 ^ 40 * 2201071 * 2
def baseEnd_2201071 : Nat := 251157195038325118508881

theorem tailTrace_2201071 : CollatzResearch.WordTrace tailWord_2201071 prefixEnd_2201071 251157195038325118508881 := by
  unfold tailWord_2201071
  simp only [CollatzResearch.WordTrace]
  refine ⟨80279654608903154843947067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53519769739268769895964711 80279654608903154843947067)
  ·
    refine ⟨120419481913354732265920601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80279654608903154843947067 120419481913354732265920601)
    ·
      refine ⟨90314611435016049199440451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120419481913354732265920601 90314611435016049199440451)
      ·
        refine ⟨135471917152524073799160677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90314611435016049199440451 135471917152524073799160677)
        ·
          refine ⟨25400984466098263837342627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135471917152524073799160677 25400984466098263837342627)
          ·
            refine ⟨38101476699147395756013941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25400984466098263837342627 38101476699147395756013941)
            ·
              refine ⟨3572013440545068352126307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38101476699147395756013941 3572013440545068352126307)
              ·
                refine ⟨5358020160817602528189461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572013440545068352126307 5358020160817602528189461)
                ·
                  refine ⟨251157195038325118508881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5358020160817602528189461 251157195038325118508881)
                  ·
                    rfl

theorem cell22_2201071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 6].length) (baseStart_2201071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201071 prefixEnd_2201071 := by exact prefixLift 2201071
  have htrace : WordTrace (prefixWord ++ tailWord_2201071) baseStart_2201071 baseEnd_2201071 := by
    simpa [prefixWord, tailWord_2201071, baseEnd_2201071] using wordTrace_append hprefix tailTrace_2201071
  have hstable : (prefixWord ++ tailWord_2201071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201071).length < 2 ^ (prefixWord ++ tailWord_2201071).sum := by decide
  have hdescent : baseEnd_2201071 < baseStart_2201071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201077 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 5]
def baseStart_2201077 : Nat := 118140960795 + 2201077 * 2 ^ 59
def prefixEnd_2201077 : Nat := 4983230072969 + 3 ^ 40 * 2201077 * 2
def baseEnd_2201077 : Nat := 251157879679197779958875

theorem tailTrace_2201077 : CollatzResearch.WordTrace tailWord_2201077 prefixEnd_2201077 251157879679197779958875 := by
  unfold tailWord_2201077
  simp only [CollatzResearch.WordTrace]
  refine ⟨80279873446881417868665485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53519915631254278579110323 80279873446881417868665485)
  ·
    refine ⟨30104952542580531700749557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80279873446881417868665485 30104952542580531700749557)
    ·
      refine ⟨2822339300866924846945271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30104952542580531700749557 2822339300866924846945271)
      ·
        refine ⟨4233508951300387270417907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2822339300866924846945271 4233508951300387270417907)
        ·
          refine ⟨6350263426950580905626861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4233508951300387270417907 6350263426950580905626861)
          ·
            refine ⟨2381348785106467839610073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6350263426950580905626861 2381348785106467839610073)
            ·
              refine ⟨1786011588829850879707555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2381348785106467839610073 1786011588829850879707555)
              ·
                refine ⟨2679017383244776319561333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786011588829850879707555 2679017383244776319561333)
                ·
                  refine ⟨251157879679197779958875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2679017383244776319561333 251157879679197779958875)
                  ·
                    rfl

theorem cell22_2201077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_2201077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201077 prefixEnd_2201077 := by exact prefixLift 2201077
  have htrace : WordTrace (prefixWord ++ tailWord_2201077) baseStart_2201077 baseEnd_2201077 := by
    simpa [prefixWord, tailWord_2201077, baseEnd_2201077] using wordTrace_append hprefix tailTrace_2201077
  have hstable : (prefixWord ++ tailWord_2201077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201077).length < 2 ^ (prefixWord ++ tailWord_2201077).sum := by decide
  have hdescent : baseEnd_2201077 < baseStart_2201077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201090 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2201090 : Nat := 118140960795 + 2201090 * 2 ^ 59
def prefixEnd_2201090 : Nat := 4983230072969 + 3 ^ 40 * 2201090 * 2
def baseEnd_2201090 : Nat := 753478089203265639301585

theorem tailTrace_2201090 : CollatzResearch.WordTrace tailWord_2201090 prefixEnd_2201090 753478089203265639301585 := by
  unfold tailWord_2201090
  simp only [CollatzResearch.WordTrace]
  refine ⟨20070086898958580272222181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53520231730556214059259149 20070086898958580272222181)
  ·
    refine ⟨3763141293554733801041659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20070086898958580272222181 3763141293554733801041659)
    ·
      refine ⟨5644711940332100701562489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3763141293554733801041659 5644711940332100701562489)
      ·
        refine ⟨4233533955249075526171867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5644711940332100701562489 4233533955249075526171867)
        ·
          refine ⟨6350300932873613289257801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4233533955249075526171867 6350300932873613289257801)
          ·
            refine ⟨4762725699655209966943351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6350300932873613289257801 4762725699655209966943351)
            ·
              refine ⟨7144088549482814950415027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4762725699655209966943351 7144088549482814950415027)
              ·
                refine ⟨10716132824224222425622541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7144088549482814950415027 10716132824224222425622541)
                ·
                  refine ⟨4018549809084083409608453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10716132824224222425622541 4018549809084083409608453)
                  ·
                    refine ⟨753478089203265639301585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4018549809084083409608453 753478089203265639301585)
                    ·
                      rfl

theorem cell22_2201090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2201090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201090 prefixEnd_2201090 := by exact prefixLift 2201090
  have htrace : WordTrace (prefixWord ++ tailWord_2201090) baseStart_2201090 baseEnd_2201090 := by
    simpa [prefixWord, tailWord_2201090, baseEnd_2201090] using wordTrace_append hprefix tailTrace_2201090
  have hstable : (prefixWord ++ tailWord_2201090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201090).length < 2 ^ (prefixWord ++ tailWord_2201090).sum := by decide
  have hdescent : baseEnd_2201090 < baseStart_2201090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201120 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 2, 3]
def baseStart_2201120 : Nat := 118140960795 + 2201120 * 2 ^ 59
def prefixEnd_2201120 : Nat := 4983230072969 + 3 ^ 40 * 2201120 * 2
def baseEnd_2201120 : Nat := 753488358816355561051493

theorem tailTrace_2201120 : CollatzResearch.WordTrace tailWord_2201120 prefixEnd_2201120 753488358816355561051493 := by
  unfold tailWord_2201120
  simp only [CollatzResearch.WordTrace]
  refine ⟨40140720892862818106240407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53520961190483757474987209 40140720892862818106240407)
  ·
    refine ⟨60211081339294227159360611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40140720892862818106240407 60211081339294227159360611)
    ·
      refine ⟨90316622008941340739040917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60211081339294227159360611 90316622008941340739040917)
      ·
        refine ⟨4233591656669125347142543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90316622008941340739040917 4233591656669125347142543)
        ·
          refine ⟨6350387485003688020713815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4233591656669125347142543 6350387485003688020713815)
          ·
            refine ⟨9525581227505532031070723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6350387485003688020713815 9525581227505532031070723)
            ·
              refine ⟨14288371841258298046606085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9525581227505532031070723 14288371841258298046606085)
              ·
                refine ⟨2679069720235930883738641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14288371841258298046606085 2679069720235930883738641)
                ·
                  refine ⟨2009302290176948162803981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679069720235930883738641 2009302290176948162803981)
                  ·
                    refine ⟨753488358816355561051493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009302290176948162803981 753488358816355561051493)
                    ·
                      rfl

theorem cell22_2201120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_2201120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201120 prefixEnd_2201120 := by exact prefixLift 2201120
  have htrace : WordTrace (prefixWord ++ tailWord_2201120) baseStart_2201120 baseEnd_2201120 := by
    simpa [prefixWord, tailWord_2201120, baseEnd_2201120] using wordTrace_append hprefix tailTrace_2201120
  have hstable : (prefixWord ++ tailWord_2201120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201120).length < 2 ^ (prefixWord ++ tailWord_2201120).sum := by decide
  have hdescent : baseEnd_2201120 < baseStart_2201120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201146 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_2201146 : Nat := 118140960795 + 2201146 * 2 ^ 59
def prefixEnd_2201146 : Nat := 4983230072969 + 3 ^ 40 * 2201146 * 2
def baseEnd_2201146 : Nat := 753497259147700159901413

theorem tailTrace_2201146 : CollatzResearch.WordTrace tailWord_2201146 prefixEnd_2201146 753497259147700159901413 := by
  unfold tailWord_2201146
  simp only [CollatzResearch.WordTrace]
  refine ⟨20070597520907860663231823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53521593389087628435284861 20070597520907860663231823)
  ·
    refine ⟨30105896281361790994847735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20070597520907860663231823 30105896281361790994847735)
    ·
      refine ⟨45158844422042686492271603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30105896281361790994847735 45158844422042686492271603)
      ·
        refine ⟨67738266633064029738407405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45158844422042686492271603 67738266633064029738407405)
        ·
          refine ⟨25401849987399011151902777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67738266633064029738407405 25401849987399011151902777)
          ·
            refine ⟨19051387490549258363927083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25401849987399011151902777 19051387490549258363927083)
            ·
              refine ⟨28577081235823887545890625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19051387490549258363927083 28577081235823887545890625)
              ·
                refine ⟨21432810926867915659417969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28577081235823887545890625 21432810926867915659417969)
                ·
                  refine ⟨16074608195150936744563477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21432810926867915659417969 16074608195150936744563477)
                  ·
                    refine ⟨753497259147700159901413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16074608195150936744563477 753497259147700159901413)
                    ·
                      rfl

theorem cell22_2201146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_2201146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201146 prefixEnd_2201146 := by exact prefixLift 2201146
  have htrace : WordTrace (prefixWord ++ tailWord_2201146) baseStart_2201146 baseEnd_2201146 := by
    simpa [prefixWord, tailWord_2201146, baseEnd_2201146] using wordTrace_append hprefix tailTrace_2201146
  have hstable : (prefixWord ++ tailWord_2201146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201146).length < 2 ^ (prefixWord ++ tailWord_2201146).sum := by decide
  have hdescent : baseEnd_2201146 < baseStart_2201146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201240 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 6]
def baseStart_2201240 : Nat := 118140960795 + 2201240 * 2 ^ 59
def prefixEnd_2201240 : Nat := 4983230072969 + 3 ^ 40 * 2201240 * 2
def baseEnd_2201240 : Nat := 251176479089571749350375

theorem tailTrace_2201240 : CollatzResearch.WordTrace tailWord_2201240 prefixEnd_2201240 251176479089571749350375 := by
  unfold tailWord_2201240
  simp only [CollatzResearch.WordTrace]
  refine ⟨40142909272645448353424587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53523879030193931137899449 40142909272645448353424587)
  ·
    refine ⟨60214363908968172530136881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40142909272645448353424587 60214363908968172530136881)
    ·
      refine ⟨45160772931726129397602661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60214363908968172530136881 45160772931726129397602661)
      ·
        refine ⟨8467644924698649262050499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45160772931726129397602661 8467644924698649262050499)
        ·
          refine ⟨12701467387047973893075749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8467644924698649262050499 12701467387047973893075749)
          ·
            refine ⟨2381525135071495104951703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12701467387047973893075749 2381525135071495104951703)
            ·
              refine ⟨3572287702607242657427555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381525135071495104951703 3572287702607242657427555)
              ·
                refine ⟨5358431553910863986141333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572287702607242657427555 5358431553910863986141333)
                ·
                  refine ⟨251176479089571749350375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5358431553910863986141333 251176479089571749350375)
                  ·
                    rfl

theorem cell22_2201240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_2201240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201240 prefixEnd_2201240 := by exact prefixLift 2201240
  have htrace : WordTrace (prefixWord ++ tailWord_2201240) baseStart_2201240 baseEnd_2201240 := by
    simpa [prefixWord, tailWord_2201240, baseEnd_2201240] using wordTrace_append hprefix tailTrace_2201240
  have hstable : (prefixWord ++ tailWord_2201240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201240).length < 2 ^ (prefixWord ++ tailWord_2201240).sum := by decide
  have hdescent : baseEnd_2201240 < baseStart_2201240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201334 : List Nat := [5, 1, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_2201334 : Nat := 118140960795 + 2201334 * 2 ^ 59
def prefixEnd_2201334 : Nat := 4983230072969 + 3 ^ 40 * 2201334 * 2
def baseEnd_2201334 : Nat := 753561615389730336200837

theorem tailTrace_2201334 : CollatzResearch.WordTrace tailWord_2201334 prefixEnd_2201334 753561615389730336200837 := by
  unfold tailWord_2201334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018077937934396922548191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53526164671300233840514037 5018077937934396922548191)
  ·
    refine ⟨7527116906901595383822287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5018077937934396922548191 7527116906901595383822287)
    ·
      refine ⟨11290675360352393075733431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7527116906901595383822287 11290675360352393075733431)
      ·
        refine ⟨16936013040528589613600147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11290675360352393075733431 16936013040528589613600147)
        ·
          refine ⟨25404019560792884420400221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16936013040528589613600147 25404019560792884420400221)
          ·
            refine ⟨9526507335297331657650083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25404019560792884420400221 9526507335297331657650083)
            ·
              refine ⟨14289761002945997486475125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9526507335297331657650083 14289761002945997486475125)
              ·
                refine ⟨1339665094026187264357043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14289761002945997486475125 1339665094026187264357043)
                ·
                  refine ⟨2009497641039280896535565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339665094026187264357043 2009497641039280896535565)
                  ·
                    refine ⟨753561615389730336200837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009497641039280896535565 753561615389730336200837)
                    ·
                      rfl

theorem cell22_2201334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_2201334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201334 prefixEnd_2201334 := by exact prefixLift 2201334
  have htrace : WordTrace (prefixWord ++ tailWord_2201334) baseStart_2201334 baseEnd_2201334 := by
    simpa [prefixWord, tailWord_2201334, baseEnd_2201334] using wordTrace_append hprefix tailTrace_2201334
  have hstable : (prefixWord ++ tailWord_2201334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201334).length < 2 ^ (prefixWord ++ tailWord_2201334).sum := by decide
  have hdescent : baseEnd_2201334 < baseStart_2201334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201362 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2201362 : Nat := 118140960795 + 2201362 * 2 ^ 59
def prefixEnd_2201362 : Nat := 4983230072969 + 3 ^ 40 * 2201362 * 2
def baseEnd_2201362 : Nat := 753571200361947596500751

theorem tailTrace_2201362 : CollatzResearch.WordTrace tailWord_2201362 prefixEnd_2201362 753571200361947596500751 := by
  unfold tailWord_2201362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20072567062712227885697585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53526845500565941028526893 20072567062712227885697585)
  ·
    refine ⟨15054425297034170914273189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20072567062712227885697585 15054425297034170914273189)
    ·
      refine ⟨2822704743193907046426223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15054425297034170914273189 2822704743193907046426223)
      ·
        refine ⟨4234057114790860569639335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2822704743193907046426223 4234057114790860569639335)
        ·
          refine ⟨6351085672186290854459003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234057114790860569639335 6351085672186290854459003)
          ·
            refine ⟨9526628508279436281688505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351085672186290854459003 9526628508279436281688505)
            ·
              refine ⟨7144971381209577211266379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9526628508279436281688505 7144971381209577211266379)
              ·
                refine ⟨10717457071814365816899569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7144971381209577211266379 10717457071814365816899569)
                ·
                  refine ⟨8038092803860774362674677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10717457071814365816899569 8038092803860774362674677)
                  ·
                    refine ⟨753571200361947596500751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8038092803860774362674677 753571200361947596500751)
                    ·
                      rfl

theorem cell22_2201362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2201362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201362 prefixEnd_2201362 := by exact prefixLift 2201362
  have htrace : WordTrace (prefixWord ++ tailWord_2201362) baseStart_2201362 baseEnd_2201362 := by
    simpa [prefixWord, tailWord_2201362, baseEnd_2201362] using wordTrace_append hprefix tailTrace_2201362
  have hstable : (prefixWord ++ tailWord_2201362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201362).length < 2 ^ (prefixWord ++ tailWord_2201362).sum := by decide
  have hdescent : baseEnd_2201362 < baseStart_2201362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201377 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_2201377 : Nat := 118140960795 + 2201377 * 2 ^ 59
def prefixEnd_2201377 : Nat := 4983230072969 + 3 ^ 40 * 2201377 * 2
def baseEnd_2201377 : Nat := 753576335168492557375705

theorem tailTrace_2201377 : CollatzResearch.WordTrace tailWord_2201377 prefixEnd_2201377 753576335168492557375705 := by
  unfold tailWord_2201377
  simp only [CollatzResearch.WordTrace]
  refine ⟨80290815345794569104586385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53527210230529712736390923 80290815345794569104586385)
  ·
    refine ⟨60218111509345926828439789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80290815345794569104586385 60218111509345926828439789)
    ·
      refine ⟨22581791816004722560664921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60218111509345926828439789 22581791816004722560664921)
      ·
        refine ⟨16936343862003541920498691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22581791816004722560664921 16936343862003541920498691)
        ·
          refine ⟨25404515793005312880748037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16936343862003541920498691 25404515793005312880748037)
          ·
            refine ⟨4763346711188496165140257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25404515793005312880748037 4763346711188496165140257)
            ·
              refine ⟨3572510033391372123855193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4763346711188496165140257 3572510033391372123855193)
              ·
                refine ⟨2679382525043529092891395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3572510033391372123855193 2679382525043529092891395)
                ·
                  refine ⟨4019073787565293639337093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2679382525043529092891395 4019073787565293639337093)
                  ·
                    refine ⟨753576335168492557375705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4019073787565293639337093 753576335168492557375705)
                    ·
                      rfl

theorem cell22_2201377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_2201377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201377 prefixEnd_2201377 := by exact prefixLift 2201377
  have htrace : WordTrace (prefixWord ++ tailWord_2201377) baseStart_2201377 baseEnd_2201377 := by
    simpa [prefixWord, tailWord_2201377, baseEnd_2201377] using wordTrace_append hprefix tailTrace_2201377
  have hstable : (prefixWord ++ tailWord_2201377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201377).length < 2 ^ (prefixWord ++ tailWord_2201377).sum := by decide
  have hdescent : baseEnd_2201377 < baseStart_2201377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201486 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_2201486 : Nat := 118140960795 + 2201486 * 2 ^ 59
def prefixEnd_2201486 : Nat := 4983230072969 + 3 ^ 40 * 2201486 * 2
def baseEnd_2201486 : Nat := 753613648096052606400371

theorem tailTrace_2201486 : CollatzResearch.WordTrace tailWord_2201486 prefixEnd_2201486 753613648096052606400371 := by
  unfold tailWord_2201486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10036848862799960090038039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53529860601599787146869541 10036848862799960090038039)
  ·
    refine ⟨15055273294199940135057059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10036848862799960090038039 15055273294199940135057059)
    ·
      refine ⟨22582909941299910202585589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15055273294199940135057059 22582909941299910202585589)
      ·
        refine ⟨2117147806996866581492399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22582909941299910202585589 2117147806996866581492399)
        ·
          refine ⟨3175721710495299872238599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117147806996866581492399 3175721710495299872238599)
          ·
            refine ⟨4763582565742949808357899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175721710495299872238599 4763582565742949808357899)
            ·
              refine ⟨7145373848614424712536849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763582565742949808357899 7145373848614424712536849)
              ·
                refine ⟨5359030386460818534402637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7145373848614424712536849 5359030386460818534402637)
                ·
                  refine ⟨2009636394922806950400989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5359030386460818534402637 2009636394922806950400989)
                  ·
                    refine ⟨753613648096052606400371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009636394922806950400989 753613648096052606400371)
                    ·
                      rfl

theorem cell22_2201486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_2201486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201486 prefixEnd_2201486 := by exact prefixLift 2201486
  have htrace : WordTrace (prefixWord ++ tailWord_2201486) baseStart_2201486 baseEnd_2201486 := by
    simpa [prefixWord, tailWord_2201486, baseEnd_2201486] using wordTrace_append hprefix tailTrace_2201486
  have hstable : (prefixWord ++ tailWord_2201486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201486).length < 2 ^ (prefixWord ++ tailWord_2201486).sum := by decide
  have hdescent : baseEnd_2201486 < baseStart_2201486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201557 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2201557 : Nat := 118140960795 + 2201557 * 2 ^ 59
def prefixEnd_2201557 : Nat := 4983230072969 + 3 ^ 40 * 2201557 * 2
def baseEnd_2201557 : Nat := 753637952847032087875153

theorem tailTrace_2201557 : CollatzResearch.WordTrace tailWord_2201557 prefixEnd_2201557 753637952847032087875153 := by
  unfold tailWord_2201557
  simp only [CollatzResearch.WordTrace]
  refine ⟨80297380485142459846138925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53531586990094973230759283 80297380485142459846138925)
  ·
    refine ⟨30111517681928422442302097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80297380485142459846138925 30111517681928422442302097)
    ·
      refine ⟨22583638261446316831726573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30111517681928422442302097 22583638261446316831726573)
      ·
        refine ⟨8468864348042368811897465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22583638261446316831726573 8468864348042368811897465)
        ·
          refine ⟨6351648261031776608923099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8468864348042368811897465 6351648261031776608923099)
          ·
            refine ⟨9527472391547664913384649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351648261031776608923099 9527472391547664913384649)
            ·
              refine ⟨7145604293660748685038487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9527472391547664913384649 7145604293660748685038487)
              ·
                refine ⟨10718406440491123027557731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7145604293660748685038487 10718406440491123027557731)
                ·
                  refine ⟨16077609660736684541336597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10718406440491123027557731 16077609660736684541336597)
                  ·
                    refine ⟨753637952847032087875153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16077609660736684541336597 753637952847032087875153)
                    ·
                      rfl

theorem cell22_2201557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2201557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201557 prefixEnd_2201557 := by exact prefixLift 2201557
  have htrace : WordTrace (prefixWord ++ tailWord_2201557) baseStart_2201557 baseEnd_2201557 := by
    simpa [prefixWord, tailWord_2201557, baseEnd_2201557] using wordTrace_append hprefix tailTrace_2201557
  have hstable : (prefixWord ++ tailWord_2201557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201557).length < 2 ^ (prefixWord ++ tailWord_2201557).sum := by decide
  have hdescent : baseEnd_2201557 < baseStart_2201557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201561 : List Nat := [1, 2, 1, 2, 6, 2, 1, 3, 4]
def baseStart_2201561 : Nat := 118140960795 + 2201561 * 2 ^ 59
def prefixEnd_2201561 : Nat := 4983230072969 + 3 ^ 40 * 2201561 * 2
def baseEnd_2201561 : Nat := 251213107376259136925047

theorem tailTrace_2201561 : CollatzResearch.WordTrace tailWord_2201561 prefixEnd_2201561 251213107376259136925047 := by
  unfold tailWord_2201561
  simp only [CollatzResearch.WordTrace]
  refine ⟨80297526377127968529284537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53531684251418645686189691 80297526377127968529284537)
  ·
    refine ⟨60223144782845976396963403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80297526377127968529284537 60223144782845976396963403)
    ·
      refine ⟨90334717174268964595445105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60223144782845976396963403 90334717174268964595445105)
      ·
        refine ⟨67751037880701723446583829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90334717174268964595445105 67751037880701723446583829)
        ·
          refine ⟨3175829900657893286558617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67751037880701723446583829 3175829900657893286558617)
          ·
            refine ⟨2381872425493419964918963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3175829900657893286558617 2381872425493419964918963)
            ·
              refine ⟨3572808638240129947378445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381872425493419964918963 3572808638240129947378445)
              ·
                refine ⟨1339803239340048730266917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3572808638240129947378445 1339803239340048730266917)
                ·
                  refine ⟨251213107376259136925047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1339803239340048730266917 251213107376259136925047)
                  ·
                    rfl

theorem cell22_2201561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 4].length) (baseStart_2201561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201561 prefixEnd_2201561 := by exact prefixLift 2201561
  have htrace : WordTrace (prefixWord ++ tailWord_2201561) baseStart_2201561 baseEnd_2201561 := by
    simpa [prefixWord, tailWord_2201561, baseEnd_2201561] using wordTrace_append hprefix tailTrace_2201561
  have hstable : (prefixWord ++ tailWord_2201561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201561).length < 2 ^ (prefixWord ++ tailWord_2201561).sum := by decide
  have hdescent : baseEnd_2201561 < baseStart_2201561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201600 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 9]
def baseStart_2201600 : Nat := 118140960795 + 2201600 * 2 ^ 59
def prefixEnd_2201600 : Nat := 4983230072969 + 3 ^ 40 * 2201600 * 2
def baseEnd_2201600 : Nat := 251217557541931436350007

theorem tailTrace_2201600 : CollatzResearch.WordTrace tailWord_2201600 prefixEnd_2201600 251217557541931436350007 := by
  unfold tailWord_2201600
  simp only [CollatzResearch.WordTrace]
  refine ⟨40149474411993339094977127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53532632549324452126636169 40149474411993339094977127)
  ·
    refine ⟨60224211617990008642465691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40149474411993339094977127 60224211617990008642465691)
    ·
      refine ⟨90336317426985012963698537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60224211617990008642465691 90336317426985012963698537)
      ·
        refine ⟨67752238070238759722773903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90336317426985012963698537 67752238070238759722773903)
        ·
          refine ⟨101628357105358139584160855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67752238070238759722773903 101628357105358139584160855)
          ·
            refine ⟨152442535658037209376241283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101628357105358139584160855 152442535658037209376241283)
            ·
              refine ⟨228663803487055814064361925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152442535658037209376241283 228663803487055814064361925)
              ·
                refine ⟨42874463153822965137067861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228663803487055814064361925 42874463153822965137067861)
                ·
                  refine ⟨251217557541931436350007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42874463153822965137067861 251217557541931436350007)
                  ·
                    rfl

theorem cell22_2201600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_2201600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201600 prefixEnd_2201600 := by exact prefixLift 2201600
  have htrace : WordTrace (prefixWord ++ tailWord_2201600) baseStart_2201600 baseEnd_2201600 := by
    simpa [prefixWord, tailWord_2201600, baseEnd_2201600] using wordTrace_append hprefix tailTrace_2201600
  have hstable : (prefixWord ++ tailWord_2201600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201600).length < 2 ^ (prefixWord ++ tailWord_2201600).sum := by decide
  have hdescent : baseEnd_2201600 < baseStart_2201600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201634 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_2201634 : Nat := 118140960795 + 2201634 * 2 ^ 59
def prefixEnd_2201634 : Nat := 4983230072969 + 3 ^ 40 * 2201634 * 2
def baseEnd_2201634 : Nat := 251221437173543184566639

theorem tailTrace_2201634 : CollatzResearch.WordTrace tailWord_2201634 prefixEnd_2201634 251221437173543184566639 := by
  unfold tailWord_2201634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20075047226465875499172989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53533459270575667997794637 20075047226465875499172989)
  ·
    refine ⟨7528142709924703312189871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20075047226465875499172989 7528142709924703312189871)
    ·
      refine ⟨11292214064887054968284807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7528142709924703312189871 11292214064887054968284807)
      ·
        refine ⟨16938321097330582452427211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11292214064887054968284807 16938321097330582452427211)
        ·
          refine ⟨25407481645995873678640817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16938321097330582452427211 25407481645995873678640817)
          ·
            refine ⟨19055611234496905258980613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25407481645995873678640817 19055611234496905258980613)
            ·
              refine ⟨3572927106468169736058865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19055611234496905258980613 3572927106468169736058865)
              ·
                refine ⟨2679695329851127302044149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3572927106468169736058865 2679695329851127302044149)
                ·
                  refine ⟨251221437173543184566639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2679695329851127302044149 251221437173543184566639)
                  ·
                    rfl

theorem cell22_2201634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_2201634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201634 prefixEnd_2201634 := by exact prefixLift 2201634
  have htrace : WordTrace (prefixWord ++ tailWord_2201634) baseStart_2201634 baseEnd_2201634 := by
    simpa [prefixWord, tailWord_2201634, baseEnd_2201634] using wordTrace_append hprefix tailTrace_2201634
  have hstable : (prefixWord ++ tailWord_2201634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201634).length < 2 ^ (prefixWord ++ tailWord_2201634).sum := by decide
  have hdescent : baseEnd_2201634 < baseStart_2201634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201724 : List Nat := [2, 2, 2, 1, 1, 4, 4, 6]
def baseStart_2201724 : Nat := 118140960795 + 2201724 * 2 ^ 59
def prefixEnd_2201724 : Nat := 4983230072969 + 3 ^ 40 * 2201724 * 2
def baseEnd_2201724 : Nat := 83743902262211035438849

theorem tailTrace_2201724 : CollatzResearch.WordTrace tailWord_2201724 prefixEnd_2201724 83743902262211035438849 := by
  unfold tailWord_2201724
  simp only [CollatzResearch.WordTrace]
  refine ⟨40151735737768723683734113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53535647650358298244978817 40151735737768723683734113)
  ·
    refine ⟨30113801803326542762800585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40151735737768723683734113 30113801803326542762800585)
    ·
      refine ⟨22585351352494907072100439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30113801803326542762800585 22585351352494907072100439)
      ·
        refine ⟨33878027028742360608150659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22585351352494907072100439 33878027028742360608150659)
        ·
          refine ⟨50817040543113540912225989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33878027028742360608150659 50817040543113540912225989)
          ·
            refine ⟨9528195101833788921042373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50817040543113540912225989 9528195101833788921042373)
            ·
              refine ⟨1786536581593835422695445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9528195101833788921042373 1786536581593835422695445)
              ·
                refine ⟨83743902262211035438849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1786536581593835422695445 83743902262211035438849)
                ·
                  rfl

theorem cell22_2201724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 6].length) (baseStart_2201724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201724 prefixEnd_2201724 := by exact prefixLift 2201724
  have htrace : WordTrace (prefixWord ++ tailWord_2201724) baseStart_2201724 baseEnd_2201724 := by
    simpa [prefixWord, tailWord_2201724, baseEnd_2201724] using wordTrace_append hprefix tailTrace_2201724
  have hstable : (prefixWord ++ tailWord_2201724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201724).length < 2 ^ (prefixWord ++ tailWord_2201724).sum := by decide
  have hdescent : baseEnd_2201724 < baseStart_2201724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201831 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 6]
def baseStart_2201831 : Nat := 118140960795 + 2201831 * 2 ^ 59
def prefixEnd_2201831 : Nat := 4983230072969 + 3 ^ 40 * 2201831 * 2
def baseEnd_2201831 : Nat := 251243916215528902174771

theorem tailTrace_2201831 : CollatzResearch.WordTrace tailWord_2201831 prefixEnd_2201831 251243916215528902174771 := by
  unfold tailWord_2201831
  simp only [CollatzResearch.WordTrace]
  refine ⟨80307374086149804641613347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53538249390766536427742231 80307374086149804641613347)
  ·
    refine ⟨120461061129224706962420021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80307374086149804641613347 120461061129224706962420021)
    ·
      refine ⟨11293224480864816277726877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120461061129224706962420021 11293224480864816277726877)
      ·
        refine ⟨4234959180324306104147579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11293224480864816277726877 4234959180324306104147579)
        ·
          refine ⟨6352438770486459156221369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234959180324306104147579 6352438770486459156221369)
          ·
            refine ⟨4764329077864844367166027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6352438770486459156221369 4764329077864844367166027)
            ·
              refine ⟨7146493616797266550749041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764329077864844367166027 7146493616797266550749041)
              ·
                refine ⟨5359870212597949913061781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7146493616797266550749041 5359870212597949913061781)
                ·
                  refine ⟨251243916215528902174771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5359870212597949913061781 251243916215528902174771)
                  ·
                    rfl

theorem cell22_2201831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 6].length) (baseStart_2201831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201831 prefixEnd_2201831 := by exact prefixLift 2201831
  have htrace : WordTrace (prefixWord ++ tailWord_2201831) baseStart_2201831 baseEnd_2201831 := by
    simpa [prefixWord, tailWord_2201831, baseEnd_2201831] using wordTrace_append hprefix tailTrace_2201831
  have hstable : (prefixWord ++ tailWord_2201831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201831).length < 2 ^ (prefixWord ++ tailWord_2201831).sum := by decide
  have hdescent : baseEnd_2201831 < baseStart_2201831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201846 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2201846 : Nat := 118140960795 + 2201846 * 2 ^ 59
def prefixEnd_2201846 : Nat := 4983230072969 + 3 ^ 40 * 2201846 * 2
def baseEnd_2201846 : Nat := 753736883453131667399267

theorem tailTrace_2201846 : CollatzResearch.WordTrace tailWord_2201846 prefixEnd_2201846 753736883453131667399267 := by
  unfold tailWord_2201846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019245073818466387713087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53538614120730308135606261 5019245073818466387713087)
  ·
    refine ⟨7528867610727699581569631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019245073818466387713087 7528867610727699581569631)
    ·
      refine ⟨11293301416091549372354447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7528867610727699581569631 11293301416091549372354447)
      ·
        refine ⟨16939952124137324058531671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11293301416091549372354447 16939952124137324058531671)
        ·
          refine ⟨25409928186205986087797507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16939952124137324058531671 25409928186205986087797507)
          ·
            refine ⟨38114892279308979131696261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25409928186205986087797507 38114892279308979131696261)
            ·
              refine ⟨7146542302370433587193049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38114892279308979131696261 7146542302370433587193049)
              ·
                refine ⟨5359906726777825190394787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7146542302370433587193049 5359906726777825190394787)
                ·
                  refine ⟨8039860090166737785592181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5359906726777825190394787 8039860090166737785592181)
                  ·
                    refine ⟨753736883453131667399267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8039860090166737785592181 753736883453131667399267)
                    ·
                      rfl

theorem cell22_2201846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2201846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201846 prefixEnd_2201846 := by exact prefixLift 2201846
  have htrace : WordTrace (prefixWord ++ tailWord_2201846) baseStart_2201846 baseEnd_2201846 := by
    simpa [prefixWord, tailWord_2201846, baseEnd_2201846] using wordTrace_append hprefix tailTrace_2201846
  have hstable : (prefixWord ++ tailWord_2201846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201846).length < 2 ^ (prefixWord ++ tailWord_2201846).sum := by decide
  have hdescent : baseEnd_2201846 < baseStart_2201846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201889 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2201889 : Nat := 118140960795 + 2201889 * 2 ^ 59
def prefixEnd_2201889 : Nat := 4983230072969 + 3 ^ 40 * 2201889 * 2
def baseEnd_2201889 : Nat := 753751603231893888574135

theorem tailTrace_2201889 : CollatzResearch.WordTrace tailWord_2201889 prefixEnd_2201889 753751603231893888574135 := by
  unfold tailWord_2201889
  simp only [CollatzResearch.WordTrace]
  refine ⟨80309489519939680547224721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53539659679959787031483147 80309489519939680547224721)
  ·
    refine ⟨60232117139954760410418541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80309489519939680547224721 60232117139954760410418541)
    ·
      refine ⟨22587043927483035153906953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60232117139954760410418541 22587043927483035153906953)
      ·
        refine ⟨16940282945612276365430215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22587043927483035153906953 16940282945612276365430215)
        ·
          refine ⟨25410424418418414548145323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16940282945612276365430215 25410424418418414548145323)
          ·
            refine ⟨38115636627627621822217985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25410424418418414548145323 38115636627627621822217985)
            ·
              refine ⟨28586727470720716366663489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38115636627627621822217985 28586727470720716366663489)
              ·
                refine ⟨21440045603040537274997617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28586727470720716366663489 21440045603040537274997617)
                ·
                  refine ⟨16080034202280402956248213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21440045603040537274997617 16080034202280402956248213)
                  ·
                    refine ⟨753751603231893888574135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16080034202280402956248213 753751603231893888574135)
                    ·
                      rfl

theorem cell22_2201889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2201889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201889 prefixEnd_2201889 := by exact prefixLift 2201889
  have htrace : WordTrace (prefixWord ++ tailWord_2201889) baseStart_2201889 baseEnd_2201889 := by
    simpa [prefixWord, tailWord_2201889, baseEnd_2201889] using wordTrace_append hprefix tailTrace_2201889
  have hstable : (prefixWord ++ tailWord_2201889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201889).length < 2 ^ (prefixWord ++ tailWord_2201889).sum := by decide
  have hdescent : baseEnd_2201889 < baseStart_2201889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201891 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 3, 3]
def baseStart_2201891 : Nat := 118140960795 + 2201891 * 2 ^ 59
def prefixEnd_2201891 : Nat := 4983230072969 + 3 ^ 40 * 2201891 * 2
def baseEnd_2201891 : Nat := 753752287872766550024129

theorem tailTrace_2201891 : CollatzResearch.WordTrace tailWord_2201891 prefixEnd_2201891 753752287872766550024129 := by
  unfold tailWord_2201891
  simp only [CollatzResearch.WordTrace]
  refine ⟨80309562465932434888797527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53539708310621623259198351 80309562465932434888797527)
  ·
    refine ⟨120464343698898652333196291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80309562465932434888797527 120464343698898652333196291)
    ·
      refine ⟨180696515548347978499794437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120464343698898652333196291 180696515548347978499794437)
      ·
        refine ⟨33880596665315245968711457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180696515548347978499794437 33880596665315245968711457)
        ·
          refine ⟨25410447498986434476533593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33880596665315245968711457 25410447498986434476533593)
          ·
            refine ⟨19057835624239825857400195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25410447498986434476533593 19057835624239825857400195)
            ·
              refine ⟨28586753436359738786100293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19057835624239825857400195 28586753436359738786100293)
              ·
                refine ⟨5360016269317451022393805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28586753436359738786100293 5360016269317451022393805)
                ·
                  refine ⟨2010006100994044133397677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5360016269317451022393805 2010006100994044133397677)
                  ·
                    refine ⟨753752287872766550024129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2010006100994044133397677 753752287872766550024129)
                    ·
                      rfl

theorem cell22_2201891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 3].length) (baseStart_2201891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201891 prefixEnd_2201891 := by exact prefixLift 2201891
  have htrace : WordTrace (prefixWord ++ tailWord_2201891) baseStart_2201891 baseEnd_2201891 := by
    simpa [prefixWord, tailWord_2201891, baseEnd_2201891] using wordTrace_append hprefix tailTrace_2201891
  have hstable : (prefixWord ++ tailWord_2201891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201891).length < 2 ^ (prefixWord ++ tailWord_2201891).sum := by decide
  have hdescent : baseEnd_2201891 < baseStart_2201891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201893 : List Nat := [1, 3, 1, 2, 5, 2, 2, 6]
def baseStart_2201893 : Nat := 118140960795 + 2201893 * 2 ^ 59
def prefixEnd_2201893 : Nat := 4983230072969 + 3 ^ 40 * 2201893 * 2
def baseEnd_2201893 : Nat := 83750330279293245719347

theorem tailTrace_2201893 : CollatzResearch.WordTrace tailWord_2201893 prefixEnd_2201893 83750330279293245719347 := by
  unfold tailWord_2201893
  simp only [CollatzResearch.WordTrace]
  refine ⟨80309635411925189230370333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53539756941283459486913555 80309635411925189230370333)
  ·
    refine ⟨30116113279471945961388875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80309635411925189230370333 30116113279471945961388875)
    ·
      refine ⟨45174169919207918942083313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30116113279471945961388875 45174169919207918942083313)
      ·
        refine ⟨33880627439405939206562485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45174169919207918942083313 33880627439405939206562485)
        ·
          refine ⟨3176308822444306800615233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33880627439405939206562485 3176308822444306800615233)
          ·
            refine ⟨2382231616833230100461425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3176308822444306800615233 2382231616833230100461425)
            ·
              refine ⟨1786673712624922575346069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2382231616833230100461425 1786673712624922575346069)
              ·
                refine ⟨83750330279293245719347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1786673712624922575346069 83750330279293245719347)
                ·
                  rfl

theorem cell22_2201893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 6].length) (baseStart_2201893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201893 prefixEnd_2201893 := by exact prefixLift 2201893
  have htrace : WordTrace (prefixWord ++ tailWord_2201893) baseStart_2201893 baseEnd_2201893 := by
    simpa [prefixWord, tailWord_2201893, baseEnd_2201893] using wordTrace_append hprefix tailTrace_2201893
  have hstable : (prefixWord ++ tailWord_2201893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201893).length < 2 ^ (prefixWord ++ tailWord_2201893).sum := by decide
  have hdescent : baseEnd_2201893 < baseStart_2201893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201938 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_2201938 : Nat := 118140960795 + 2201938 * 2 ^ 59
def prefixEnd_2201938 : Nat := 4983230072969 + 3 ^ 40 * 2201938 * 2
def baseEnd_2201938 : Nat := 251256125644424698032995

theorem tailTrace_2201938 : CollatzResearch.WordTrace tailWord_2201938 prefixEnd_2201938 251256125644424698032995 := by
  unfold tailWord_2201938
  simp only [CollatzResearch.WordTrace]
  refine ⟨20077819174190540478939617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53540851131174774610505645 20077819174190540478939617)
  ·
    refine ⟨15058364380642905359204713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20077819174190540478939617 15058364380642905359204713)
    ·
      refine ⟨11293773285482179019403535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15058364380642905359204713 11293773285482179019403535)
      ·
        refine ⟨16940659928223268529105303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11293773285482179019403535 16940659928223268529105303)
        ·
          refine ⟨25410989892334902793657955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16940659928223268529105303 25410989892334902793657955)
          ·
            refine ⟨38116484838502354190486933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25410989892334902793657955 38116484838502354190486933)
            ·
              refine ⟨1786710226804797852679075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38116484838502354190486933 1786710226804797852679075)
              ·
                refine ⟨2680065340207196779018613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786710226804797852679075 2680065340207196779018613)
                ·
                  refine ⟨251256125644424698032995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2680065340207196779018613 251256125644424698032995)
                  ·
                    rfl

theorem cell22_2201938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_2201938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201938 prefixEnd_2201938 := by exact prefixLift 2201938
  have htrace : WordTrace (prefixWord ++ tailWord_2201938) baseStart_2201938 baseEnd_2201938 := by
    simpa [prefixWord, tailWord_2201938, baseEnd_2201938] using wordTrace_append hprefix tailTrace_2201938
  have hstable : (prefixWord ++ tailWord_2201938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201938).length < 2 ^ (prefixWord ++ tailWord_2201938).sum := by decide
  have hdescent : baseEnd_2201938 < baseStart_2201938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201998 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2201998 : Nat := 118140960795 + 2201998 * 2 ^ 59
def prefixEnd_2201998 : Nat := 4983230072969 + 3 ^ 40 * 2201998 * 2
def baseEnd_2201998 : Nat := 753788916159453937598801

theorem tailTrace_2201998 : CollatzResearch.WordTrace tailWord_2201998 prefixEnd_2201998 753788916159453937598801 := by
  unfold tailWord_2201998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10039183134568099020367831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53542310051029861441961765 10039183134568099020367831)
  ·
    refine ⟨15058774701852148530551747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10039183134568099020367831 15058774701852148530551747)
    ·
      refine ⟨22588162052778222795827621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15058774701852148530551747 22588162052778222795827621)
      ·
        refine ⟨4235280384895916774217679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22588162052778222795827621 4235280384895916774217679)
        ·
          refine ⟨6352920577343875161326519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235280384895916774217679 6352920577343875161326519)
          ·
            refine ⟨9529380866015812741989779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6352920577343875161326519 9529380866015812741989779)
            ·
              refine ⟨14294071299023719112984669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9529380866015812741989779 14294071299023719112984669)
              ·
                refine ⟨5360276737133894667369251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14294071299023719112984669 5360276737133894667369251)
                ·
                  refine ⟨8040415105700842001053877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360276737133894667369251 8040415105700842001053877)
                  ·
                    refine ⟨753788916159453937598801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8040415105700842001053877 753788916159453937598801)
                    ·
                      rfl

theorem cell22_2201998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2201998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2201998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2201998 prefixEnd_2201998 := by exact prefixLift 2201998
  have htrace : WordTrace (prefixWord ++ tailWord_2201998) baseStart_2201998 baseEnd_2201998 := by
    simpa [prefixWord, tailWord_2201998, baseEnd_2201998] using wordTrace_append hprefix tailTrace_2201998
  have hstable : (prefixWord ++ tailWord_2201998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201998).length < 2 ^ (prefixWord ++ tailWord_2201998).sum := by decide
  have hdescent : baseEnd_2201998 < baseStart_2201998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202013 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_2202013 : Nat := 118140960795 + 2202013 * 2 ^ 59
def prefixEnd_2202013 : Nat := 4983230072969 + 3 ^ 40 * 2202013 * 2
def baseEnd_2202013 : Nat := 753794050965998898473755

theorem tailTrace_2202013 : CollatzResearch.WordTrace tailWord_2202013 prefixEnd_2202013 753794050965998898473755 := by
  unfold tailWord_2202013
  simp only [CollatzResearch.WordTrace]
  refine ⟨80314012171490449724738693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53542674780993633149825795 80314012171490449724738693)
  ·
    refine ⟨15058877282154459323388505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80314012171490449724738693 15058877282154459323388505)
    ·
      refine ⟨11294157961615844492541379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15058877282154459323388505 11294157961615844492541379)
      ·
        refine ⟨16941236942423766738812069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11294157961615844492541379 16941236942423766738812069)
        ·
          refine ⟨3176481926704456263527263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16941236942423766738812069 3176481926704456263527263)
          ·
            refine ⟨4764722890056684395290895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176481926704456263527263 4764722890056684395290895)
            ·
              refine ⟨7147084335085026592936343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764722890056684395290895 7147084335085026592936343)
              ·
                refine ⟨10720626502627539889404515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7147084335085026592936343 10720626502627539889404515)
                ·
                  refine ⟨16080939753941309834106773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10720626502627539889404515 16080939753941309834106773)
                  ·
                    refine ⟨753794050965998898473755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16080939753941309834106773 753794050965998898473755)
                    ·
                      rfl

theorem cell22_2202013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_2202013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202013 prefixEnd_2202013 := by exact prefixLift 2202013
  have htrace : WordTrace (prefixWord ++ tailWord_2202013) baseStart_2202013 baseEnd_2202013 := by
    simpa [prefixWord, tailWord_2202013, baseEnd_2202013] using wordTrace_append hprefix tailTrace_2202013
  have hstable : (prefixWord ++ tailWord_2202013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202013).length < 2 ^ (prefixWord ++ tailWord_2202013).sum := by decide
  have hdescent : baseEnd_2202013 < baseStart_2202013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202017 : List Nat := [1, 2, 3, 5, 1, 1, 2, 3, 4]
def baseStart_2202017 : Nat := 118140960795 + 2202017 * 2 ^ 59
def prefixEnd_2202017 : Nat := 4983230072969 + 3 ^ 40 * 2202017 * 2
def baseEnd_2202017 : Nat := 251265140082581407124581

theorem tailTrace_2202017 : CollatzResearch.WordTrace tailWord_2202017 prefixEnd_2202017 251265140082581407124581 := by
  unfold tailWord_2202017
  simp only [CollatzResearch.WordTrace]
  refine ⟨80314158063475958407884305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53542772042317305605256203 80314158063475958407884305)
  ·
    refine ⟨60235618547606968805913229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80314158063475958407884305 60235618547606968805913229)
    ·
      refine ⟨22588356955352613302217461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60235618547606968805913229 22588356955352613302217461)
      ·
        refine ⟨2117658464564307497082887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22588356955352613302217461 2117658464564307497082887)
        ·
          refine ⟨3176487696846461245624331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117658464564307497082887 3176487696846461245624331)
          ·
            refine ⟨4764731545269691868436497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176487696846461245624331 4764731545269691868436497)
            ·
              refine ⟨3573548658952268901327373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4764731545269691868436497 3573548658952268901327373)
              ·
                refine ⟨1340080747107100837997765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3573548658952268901327373 1340080747107100837997765)
                ·
                  refine ⟨251265140082581407124581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340080747107100837997765 251265140082581407124581)
                  ·
                    rfl

theorem cell22_2202017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 4].length) (baseStart_2202017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202017 prefixEnd_2202017 := by exact prefixLift 2202017
  have htrace : WordTrace (prefixWord ++ tailWord_2202017) baseStart_2202017 baseEnd_2202017 := by
    simpa [prefixWord, tailWord_2202017, baseEnd_2202017] using wordTrace_append hprefix tailTrace_2202017
  have hstable : (prefixWord ++ tailWord_2202017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202017).length < 2 ^ (prefixWord ++ tailWord_2202017).sum := by decide
  have hdescent : baseEnd_2202017 < baseStart_2202017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202049 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2202049 : Nat := 118140960795 + 2202049 * 2 ^ 59
def prefixEnd_2202049 : Nat := 4983230072969 + 3 ^ 40 * 2202049 * 2
def baseEnd_2202049 : Nat := 753806374501706804573645

theorem tailTrace_2202049 : CollatzResearch.WordTrace tailWord_2202049 prefixEnd_2202049 753806374501706804573645 := by
  unfold tailWord_2202049
  simp only [CollatzResearch.WordTrace]
  refine ⟨80315325199360027873049201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53543550132906685248699467 80315325199360027873049201)
  ·
    refine ⟨60236493899520020904786901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80315325199360027873049201 60236493899520020904786901)
    ·
      refine ⟨1411792825770000489955943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 60236493899520020904786901 1411792825770000489955943)
      ·
        refine ⟨2117689238655000734933915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411792825770000489955943 2117689238655000734933915)
        ·
          refine ⟨3176533857982501102400873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117689238655000734933915 3176533857982501102400873)
          ·
            refine ⟨2382400393486875826800655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3176533857982501102400873 2382400393486875826800655)
            ·
              refine ⟨3573600590230313740200983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382400393486875826800655 3573600590230313740200983)
              ·
                refine ⟨5360400885345470610301475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3573600590230313740200983 5360400885345470610301475)
                ·
                  refine ⟨8040601328018205915452213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360400885345470610301475 8040601328018205915452213)
                  ·
                    refine ⟨753806374501706804573645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8040601328018205915452213 753806374501706804573645)
                    ·
                      rfl

theorem cell22_2202049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2202049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202049 prefixEnd_2202049 := by exact prefixLift 2202049
  have htrace : WordTrace (prefixWord ++ tailWord_2202049) baseStart_2202049 baseEnd_2202049 := by
    simpa [prefixWord, tailWord_2202049, baseEnd_2202049] using wordTrace_append hprefix tailTrace_2202049
  have hstable : (prefixWord ++ tailWord_2202049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202049).length < 2 ^ (prefixWord ++ tailWord_2202049).sum := by decide
  have hdescent : baseEnd_2202049 < baseStart_2202049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202094 : List Nat := [4, 1, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2202094 : Nat := 118140960795 + 2202094 * 2 ^ 59
def prefixEnd_2202094 : Nat := 4983230072969 + 3 ^ 40 * 2202094 * 2
def baseEnd_2202094 : Nat := 753821778921341687198507

theorem tailTrace_2202094 : CollatzResearch.WordTrace tailWord_2202094 prefixEnd_2202094 753821778921341687198507 := by
  unfold tailWord_2202094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10039620810524625069804667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53544644322798000372291557 10039620810524625069804667)
  ·
    refine ⟨15059431215786937604707001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10039620810524625069804667 15059431215786937604707001)
    ·
      refine ⟨11294573411840203203530251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15059431215786937604707001 11294573411840203203530251)
      ·
        refine ⟨16941860117760304805295377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11294573411840203203530251 16941860117760304805295377)
        ·
          refine ⟨12706395088320228603971533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16941860117760304805295377 12706395088320228603971533)
          ·
            refine ⟨4764898158120085726489325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12706395088320228603971533 4764898158120085726489325)
            ·
              refine ⟨1786836809295032147433497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4764898158120085726489325 1786836809295032147433497)
              ·
                refine ⟨1340127606971274110575123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786836809295032147433497 1340127606971274110575123)
                ·
                  refine ⟨2010191410456911165862685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340127606971274110575123 2010191410456911165862685)
                  ·
                    refine ⟨753821778921341687198507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2010191410456911165862685 753821778921341687198507)
                    ·
                      rfl

theorem cell22_2202094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2202094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202094 prefixEnd_2202094 := by exact prefixLift 2202094
  have htrace : WordTrace (prefixWord ++ tailWord_2202094) baseStart_2202094 baseEnd_2202094 := by
    simpa [prefixWord, tailWord_2202094, baseEnd_2202094] using wordTrace_append hprefix tailTrace_2202094
  have hstable : (prefixWord ++ tailWord_2202094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202094).length < 2 ^ (prefixWord ++ tailWord_2202094).sum := by decide
  have hdescent : baseEnd_2202094 < baseStart_2202094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202133 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2202133 : Nat := 118140960795 + 2202133 * 2 ^ 59
def prefixEnd_2202133 : Nat := 4983230072969 + 3 ^ 40 * 2202133 * 2
def baseEnd_2202133 : Nat := 753835129418358585473387

theorem tailTrace_2202133 : CollatzResearch.WordTrace tailWord_2202133 prefixEnd_2202133 753835129418358585473387 := by
  unfold tailWord_2202133
  simp only [CollatzResearch.WordTrace]
  refine ⟨80318388931055710219107053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53545592620703806812738035 80318388931055710219107053)
  ·
    refine ⟨30119395849145891332165145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80318388931055710219107053 30119395849145891332165145)
    ·
      refine ⟨22589546886859418499123859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30119395849145891332165145 22589546886859418499123859)
      ·
        refine ⟨33884320330289127748685789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22589546886859418499123859 33884320330289127748685789)
        ·
          refine ⟨12706620123858422905757171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33884320330289127748685789 12706620123858422905757171)
          ·
            refine ⟨19059930185787634358635757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12706620123858422905757171 19059930185787634358635757)
            ·
              refine ⟨7147473819670362884488409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19059930185787634358635757 7147473819670362884488409)
              ·
                refine ⟨5360605364752772163366307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7147473819670362884488409 5360605364752772163366307)
                ·
                  refine ⟨8040908047129158245049461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360605364752772163366307 8040908047129158245049461)
                  ·
                    refine ⟨753835129418358585473387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8040908047129158245049461 753835129418358585473387)
                    ·
                      rfl

theorem cell22_2202133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2202133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202133 prefixEnd_2202133 := by exact prefixLift 2202133
  have htrace : WordTrace (prefixWord ++ tailWord_2202133) baseStart_2202133 baseEnd_2202133 := by
    simpa [prefixWord, tailWord_2202133, baseEnd_2202133] using wordTrace_append hprefix tailTrace_2202133
  have hstable : (prefixWord ++ tailWord_2202133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202133).length < 2 ^ (prefixWord ++ tailWord_2202133).sum := by decide
  have hdescent : baseEnd_2202133 < baseStart_2202133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202152 : List Nat := [2, 1, 5, 2, 1, 2, 1, 4, 4]
def baseStart_2202152 : Nat := 118140960795 + 2202152 * 2 ^ 59
def prefixEnd_2202152 : Nat := 4983230072969 + 3 ^ 40 * 2202152 * 2
def baseEnd_2202152 : Nat := 251280544502216289749443

theorem tailTrace_2202152 : CollatzResearch.WordTrace tailWord_2202152 prefixEnd_2202152 251280544502216289749443 := by
  unfold tailWord_2202152
  simp only [CollatzResearch.WordTrace]
  refine ⟨40159540958993438232024355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53546054611991250976032473 40159540958993438232024355)
  ·
    refine ⟨60239311438490157348036533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40159540958993438232024355 60239311438490157348036533)
    ·
      refine ⟨5647435447358452251378425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60239311438490157348036533 5647435447358452251378425)
      ·
        refine ⟨4235576585518839188533819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5647435447358452251378425 4235576585518839188533819)
        ·
          refine ⟨6353364878278258782800729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235576585518839188533819 6353364878278258782800729)
          ·
            refine ⟨4765023658708694087100547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6353364878278258782800729 4765023658708694087100547)
            ·
              refine ⟨7147535488063041130650821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765023658708694087100547 7147535488063041130650821)
              ·
                refine ⟨1340162904011820211997029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7147535488063041130650821 1340162904011820211997029)
                ·
                  refine ⟨251280544502216289749443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340162904011820211997029 251280544502216289749443)
                  ·
                    rfl

theorem cell22_2202152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 4].length) (baseStart_2202152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202152 prefixEnd_2202152 := by exact prefixLift 2202152
  have htrace : WordTrace (prefixWord ++ tailWord_2202152) baseStart_2202152 baseEnd_2202152 := by
    simpa [prefixWord, tailWord_2202152, baseEnd_2202152] using wordTrace_append hprefix tailTrace_2202152
  have hstable : (prefixWord ++ tailWord_2202152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202152).length < 2 ^ (prefixWord ++ tailWord_2202152).sum := by decide
  have hdescent : baseEnd_2202152 < baseStart_2202152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202182 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2202182 : Nat := 118140960795 + 2202182 * 2 ^ 59
def prefixEnd_2202182 : Nat := 4983230072969 + 3 ^ 40 * 2202182 * 2
def baseEnd_2202182 : Nat := 753851903119738790998237

theorem tailTrace_2202182 : CollatzResearch.WordTrace tailWord_2202182 prefixEnd_2202182 753851903119738790998237 := by
  unfold tailWord_2202182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510005503371193487113775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53546784071918794391760533 2510005503371193487113775)
  ·
    refine ⟨3765008255056790230670663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2510005503371193487113775 3765008255056790230670663)
    ·
      refine ⟨5647512382585185346005995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3765008255056790230670663 5647512382585185346005995)
      ·
        refine ⟨8471268573877778019008993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5647512382585185346005995 8471268573877778019008993)
        ·
          refine ⟨6353451430408333514256745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8471268573877778019008993 6353451430408333514256745)
          ·
            refine ⟨4765088572806250135692559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6353451430408333514256745 4765088572806250135692559)
            ·
              refine ⟨7147632859209375203538839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765088572806250135692559 7147632859209375203538839)
              ·
                refine ⟨10721449288814062805308259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7147632859209375203538839 10721449288814062805308259)
                ·
                  refine ⟨16082173933221094207962389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10721449288814062805308259 16082173933221094207962389)
                  ·
                    refine ⟨753851903119738790998237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16082173933221094207962389 753851903119738790998237)
                    ·
                      rfl

theorem cell22_2202182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2202182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202182 prefixEnd_2202182 := by exact prefixLift 2202182
  have htrace : WordTrace (prefixWord ++ tailWord_2202182) baseStart_2202182 baseEnd_2202182 := by
    simpa [prefixWord, tailWord_2202182, baseEnd_2202182] using wordTrace_append hprefix tailTrace_2202182
  have hstable : (prefixWord ++ tailWord_2202182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202182).length < 2 ^ (prefixWord ++ tailWord_2202182).sum := by decide
  have hdescent : baseEnd_2202182 < baseStart_2202182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202212 : List Nat := [2, 3, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_2202212 : Nat := 118140960795 + 2202212 * 2 ^ 59
def prefixEnd_2202212 : Nat := 4983230072969 + 3 ^ 40 * 2202212 * 2
def baseEnd_2202212 : Nat := 753862172732828712748145

theorem tailTrace_2202212 : CollatzResearch.WordTrace tailWord_2202212 prefixEnd_2202212 753862172732828712748145 := by
  unfold tailWord_2202212
  simp only [CollatzResearch.WordTrace]
  refine ⟨40160635148884753355616445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53547513531846337807488593 40160635148884753355616445)
  ·
    refine ⟨15060238180831782508356167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40160635148884753355616445 15060238180831782508356167)
    ·
      refine ⟨22590357271247673762534251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15060238180831782508356167 22590357271247673762534251)
      ·
        refine ⟨33885535906871510643801377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22590357271247673762534251 33885535906871510643801377)
        ·
          refine ⟨25414151930153632982851033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33885535906871510643801377 25414151930153632982851033)
          ·
            refine ⟨19060613947615224737138275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25414151930153632982851033 19060613947615224737138275)
            ·
              refine ⟨28590920921422837105707413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19060613947615224737138275 28590920921422837105707413)
              ·
                refine ⟨1340199418191695489330035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28590920921422837105707413 1340199418191695489330035)
                ·
                  refine ⟨2010299127287543233995053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340199418191695489330035 2010299127287543233995053)
                  ·
                    refine ⟨753862172732828712748145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2010299127287543233995053 753862172732828712748145)
                    ·
                      rfl

theorem cell22_2202212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_2202212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202212 prefixEnd_2202212 := by exact prefixLift 2202212
  have htrace : WordTrace (prefixWord ++ tailWord_2202212) baseStart_2202212 baseEnd_2202212 := by
    simpa [prefixWord, tailWord_2202212, baseEnd_2202212] using wordTrace_append hprefix tailTrace_2202212
  have hstable : (prefixWord ++ tailWord_2202212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202212).length < 2 ^ (prefixWord ++ tailWord_2202212).sum := by decide
  have hdescent : baseEnd_2202212 < baseStart_2202212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202223 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 2, 5]
def baseStart_2202223 : Nat := 118140960795 + 2202223 * 2 ^ 59
def prefixEnd_2202223 : Nat := 4983230072969 + 3 ^ 40 * 2202223 * 2
def baseEnd_2202223 : Nat := 753865938257628350723111

theorem tailTrace_2202223 : CollatzResearch.WordTrace tailWord_2202223 prefixEnd_2202223 753865938257628350723111 := by
  unfold tailWord_2202223
  simp only [CollatzResearch.WordTrace]
  refine ⟨80321671500729655589883323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53547781000486437059922215 80321671500729655589883323)
  ·
    refine ⟨120482507251094483384824985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80321671500729655589883323 120482507251094483384824985)
    ·
      refine ⟨90361880438320862538618739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120482507251094483384824985 90361880438320862538618739)
      ·
        refine ⟨135542820657481293807928109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90361880438320862538618739 135542820657481293807928109)
        ·
          refine ⟨50828557746555485177973041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135542820657481293807928109 50828557746555485177973041)
          ·
            refine ⟨38121418309916613883479781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50828557746555485177973041 38121418309916613883479781)
            ·
              refine ⟨7147765933109365103152459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38121418309916613883479781 7147765933109365103152459)
              ·
                refine ⟨10721648899664047654728689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7147765933109365103152459 10721648899664047654728689)
                ·
                  refine ⟨8041236674748035741046517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10721648899664047654728689 8041236674748035741046517)
                  ·
                    refine ⟨753865938257628350723111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8041236674748035741046517 753865938257628350723111)
                    ·
                      rfl

theorem cell22_2202223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_2202223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202223 prefixEnd_2202223 := by exact prefixLift 2202223
  have htrace : WordTrace (prefixWord ++ tailWord_2202223) baseStart_2202223 baseEnd_2202223 := by
    simpa [prefixWord, tailWord_2202223, baseEnd_2202223] using wordTrace_append hprefix tailTrace_2202223
  have hstable : (prefixWord ++ tailWord_2202223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202223).length < 2 ^ (prefixWord ++ tailWord_2202223).sum := by decide
  have hdescent : baseEnd_2202223 < baseStart_2202223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202298 : List Nat := [3, 1, 1, 1, 2, 3, 1, 10]
def baseStart_2202298 : Nat := 118140960795 + 2202298 * 2 ^ 59
def prefixEnd_2202298 : Nat := 4983230072969 + 3 ^ 40 * 2202298 * 2
def baseEnd_2202298 : Nat := 83765734698928128344209

theorem tailTrace_2202298 : CollatzResearch.WordTrace tailWord_2202298 prefixEnd_2202298 83765734698928128344209 := by
  unfold tailWord_2202298
  simp only [CollatzResearch.WordTrace]
  refine ⟨20081101743864485849715887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53549604650305295599242365 20081101743864485849715887)
  ·
    refine ⟨30121652615796728774573831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20081101743864485849715887 30121652615796728774573831)
    ·
      refine ⟨45182478923695093161860747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30121652615796728774573831 45182478923695093161860747)
      ·
        refine ⟨67773718385542639742791121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45182478923695093161860747 67773718385542639742791121)
        ·
          refine ⟨50830288789156979807093341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67773718385542639742791121 50830288789156979807093341)
          ·
            refine ⟨19061358295933867427660003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50830288789156979807093341 19061358295933867427660003)
            ·
              refine ⟨28592037443900801141490005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19061358295933867427660003 28592037443900801141490005)
              ·
                refine ⟨83765734698928128344209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28592037443900801141490005 83765734698928128344209)
                ·
                  rfl

theorem cell22_2202298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_2202298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202298 prefixEnd_2202298 := by exact prefixLift 2202298
  have htrace : WordTrace (prefixWord ++ tailWord_2202298) baseStart_2202298 baseEnd_2202298 := by
    simpa [prefixWord, tailWord_2202298, baseEnd_2202298] using wordTrace_append hprefix tailTrace_2202298
  have hstable : (prefixWord ++ tailWord_2202298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202298).length < 2 ^ (prefixWord ++ tailWord_2202298).sum := by decide
  have hdescent : baseEnd_2202298 < baseStart_2202298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202332 : List Nat := [2, 2, 5, 1, 1, 1, 3, 7]
def baseStart_2202332 : Nat := 118140960795 + 2202332 * 2 ^ 59
def prefixEnd_2202332 : Nat := 4983230072969 + 3 ^ 40 * 2202332 * 2
def baseEnd_2202332 : Nat := 83767027909465377749753

theorem tailTrace_2202332 : CollatzResearch.WordTrace tailWord_2202332 prefixEnd_2202332 83767027909465377749753 := by
  unfold tailWord_2202332
  simp only [CollatzResearch.WordTrace]
  refine ⟨40162823528667383602800625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53550431371556511470400833 40162823528667383602800625)
  ·
    refine ⟨30122117646500537702100469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40162823528667383602800625 30122117646500537702100469)
    ·
      refine ⟨2823948529359425409571919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30122117646500537702100469 2823948529359425409571919)
      ·
        refine ⟨4235922794039138114357879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823948529359425409571919 4235922794039138114357879)
        ·
          refine ⟨6353884191058707171536819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235922794039138114357879 6353884191058707171536819)
          ·
            refine ⟨9530826286588060757305229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6353884191058707171536819 9530826286588060757305229)
            ·
              refine ⟨3574059857470522783989461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9530826286588060757305229 3574059857470522783989461)
              ·
                refine ⟨83767027909465377749753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3574059857470522783989461 83767027909465377749753)
                ·
                  rfl

theorem cell22_2202332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 7].length) (baseStart_2202332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202332 prefixEnd_2202332 := by exact prefixLift 2202332
  have htrace : WordTrace (prefixWord ++ tailWord_2202332) baseStart_2202332 baseEnd_2202332 := by
    simpa [prefixWord, tailWord_2202332, baseEnd_2202332] using wordTrace_append hprefix tailTrace_2202332
  have hstable : (prefixWord ++ tailWord_2202332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202332).length < 2 ^ (prefixWord ++ tailWord_2202332).sum := by decide
  have hdescent : baseEnd_2202332 < baseStart_2202332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202364 : List Nat := [2, 2, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_2202364 : Nat := 118140960795 + 2202364 * 2 ^ 59
def prefixEnd_2202364 : Nat := 4983230072969 + 3 ^ 40 * 2202364 * 2
def baseEnd_2202364 : Nat := 753914205439150982947679

theorem tailTrace_2202364 : CollatzResearch.WordTrace tailWord_2202364 prefixEnd_2202364 753914205439150982947679 := by
  unfold tailWord_2202364
  simp only [CollatzResearch.WordTrace]
  refine ⟨40163407096609418335383073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53551209462145891113844097 40163407096609418335383073)
  ·
    refine ⟨30122555322457063751537305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40163407096609418335383073 30122555322457063751537305)
    ·
      refine ⟨22591916491842797813652979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30122555322457063751537305 22591916491842797813652979)
      ·
        refine ⟨33887874737764196720479469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22591916491842797813652979 33887874737764196720479469)
        ·
          refine ⟨12707953026661573770179801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33887874737764196720479469 12707953026661573770179801)
          ·
            refine ⟨9530964769996180327634851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12707953026661573770179801 9530964769996180327634851)
            ·
              refine ⟨14296447154994270491452277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9530964769996180327634851 14296447154994270491452277)
              ·
                refine ⟨1340291920780712858573651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14296447154994270491452277 1340291920780712858573651)
                ·
                  refine ⟨2010437881171069287860477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340291920780712858573651 2010437881171069287860477)
                  ·
                    refine ⟨753914205439150982947679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2010437881171069287860477 753914205439150982947679)
                    ·
                      rfl

theorem cell22_2202364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_2202364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202364 prefixEnd_2202364 := by exact prefixLift 2202364
  have htrace : WordTrace (prefixWord ++ tailWord_2202364) baseStart_2202364 baseEnd_2202364 := by
    simpa [prefixWord, tailWord_2202364, baseEnd_2202364] using wordTrace_append hprefix tailTrace_2202364
  have hstable : (prefixWord ++ tailWord_2202364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202364).length < 2 ^ (prefixWord ++ tailWord_2202364).sum := by decide
  have hdescent : baseEnd_2202364 < baseStart_2202364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202405 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 6]
def baseStart_2202405 : Nat := 118140960795 + 2202405 * 2 ^ 59
def prefixEnd_2202405 : Nat := 4983230072969 + 3 ^ 40 * 2202405 * 2
def baseEnd_2202405 : Nat := 251309413525680180890851

theorem tailTrace_2202405 : CollatzResearch.WordTrace tailWord_2202405 prefixEnd_2202405 251309413525680180890851 := by
  unfold tailWord_2202405
  simp only [CollatzResearch.WordTrace]
  refine ⟨80328309586070300673008669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53552206390713533782005779 80328309586070300673008669)
  ·
    refine ⟨30123116094776362752378251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80328309586070300673008669 30123116094776362752378251)
    ·
      refine ⟨45184674142164544128567377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30123116094776362752378251 45184674142164544128567377)
      ·
        refine ⟨33888505606623408096425533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45184674142164544128567377 33888505606623408096425533)
        ·
          refine ⟨12708189602483778036159575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33888505606623408096425533 12708189602483778036159575)
          ·
            refine ⟨19062284403725667054239363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12708189602483778036159575 19062284403725667054239363)
            ·
              refine ⟨28593426605588500581359045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19062284403725667054239363 28593426605588500581359045)
              ·
                refine ⟨5361267488547843859004821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28593426605588500581359045 5361267488547843859004821)
                ·
                  refine ⟨251309413525680180890851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5361267488547843859004821 251309413525680180890851)
                  ·
                    rfl

theorem cell22_2202405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_2202405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202405 prefixEnd_2202405 := by exact prefixLift 2202405
  have htrace : WordTrace (prefixWord ++ tailWord_2202405) baseStart_2202405 baseEnd_2202405 := by
    simpa [prefixWord, tailWord_2202405, baseEnd_2202405] using wordTrace_append hprefix tailTrace_2202405
  have hstable : (prefixWord ++ tailWord_2202405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202405).length < 2 ^ (prefixWord ++ tailWord_2202405).sum := by decide
  have hdescent : baseEnd_2202405 < baseStart_2202405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202495 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 7]
def baseStart_2202495 : Nat := 118140960795 + 2202495 * 2 ^ 59
def prefixEnd_2202495 : Nat := 4983230072969 + 3 ^ 40 * 2202495 * 2
def baseEnd_2202495 : Nat := 251319683138770102640759

theorem tailTrace_2202495 : CollatzResearch.WordTrace tailWord_2202495 prefixEnd_2202495 251319683138770102640759 := by
  unfold tailWord_2202495
  simp only [CollatzResearch.WordTrace]
  refine ⟨80331592155744246043784939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53554394770496164029189959 80331592155744246043784939)
  ·
    refine ⟨120497388233616369065677409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80331592155744246043784939 120497388233616369065677409)
    ·
      refine ⟨90373041175212276799258057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120497388233616369065677409 90373041175212276799258057)
      ·
        refine ⟨67779780881409207599443543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90373041175212276799258057 67779780881409207599443543)
        ·
          refine ⟨101669671322113811399165315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67779780881409207599443543 101669671322113811399165315)
          ·
            refine ⟨152504506983170717098747973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101669671322113811399165315 152504506983170717098747973)
            ·
              refine ⟨28594595059344509456015245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152504506983170717098747973 28594595059344509456015245)
              ·
                refine ⟨10722973147254191046005717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28594595059344509456015245 10722973147254191046005717)
                ·
                  refine ⟨251319683138770102640759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10722973147254191046005717 251319683138770102640759)
                  ·
                    rfl

theorem cell22_2202495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 7].length) (baseStart_2202495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202495 prefixEnd_2202495 := by exact prefixLift 2202495
  have htrace : WordTrace (prefixWord ++ tailWord_2202495) baseStart_2202495 baseEnd_2202495 := by
    simpa [prefixWord, tailWord_2202495, baseEnd_2202495] using wordTrace_append hprefix tailTrace_2202495
  have hstable : (prefixWord ++ tailWord_2202495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202495).length < 2 ^ (prefixWord ++ tailWord_2202495).sum := by decide
  have hdescent : baseEnd_2202495 < baseStart_2202495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202518 : List Nat := [5, 3, 1, 1, 1, 2, 3, 6]
def baseStart_2202518 : Nat := 118140960795 + 2202518 * 2 ^ 59
def prefixEnd_2202518 : Nat := 4983230072969 + 3 ^ 40 * 2202518 * 2
def baseEnd_2202518 : Nat := 83774102531816212733023

theorem tailTrace_2202518 : CollatzResearch.WordTrace tailWord_2202518 prefixEnd_2202518 83774102531816212733023 := by
  unfold tailWord_2202518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020776939666307560742013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53554954023107280647914805 5020776939666307560742013)
  ·
    refine ⟨1882791352374865335278255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5020776939666307560742013 1882791352374865335278255)
    ·
      refine ⟨2824187028562298002917383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1882791352374865335278255 2824187028562298002917383)
      ·
        refine ⟨4236280542843447004376075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824187028562298002917383 4236280542843447004376075)
        ·
          refine ⟨6354420814265170506564113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236280542843447004376075 6354420814265170506564113)
          ·
            refine ⟨4765815610698877879923085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6354420814265170506564113 4765815610698877879923085)
            ·
              refine ⟨1787180854012079204971157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4765815610698877879923085 1787180854012079204971157)
              ·
                refine ⟨83774102531816212733023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1787180854012079204971157 83774102531816212733023)
                ·
                  rfl

theorem cell22_2202518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_2202518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202518 prefixEnd_2202518 := by exact prefixLift 2202518
  have htrace : WordTrace (prefixWord ++ tailWord_2202518) baseStart_2202518 baseEnd_2202518 := by
    simpa [prefixWord, tailWord_2202518, baseEnd_2202518] using wordTrace_append hprefix tailTrace_2202518
  have hstable : (prefixWord ++ tailWord_2202518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202518).length < 2 ^ (prefixWord ++ tailWord_2202518).sum := by decide
  have hdescent : baseEnd_2202518 < baseStart_2202518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202602 : List Nat := [3, 1, 3, 1, 2, 2, 10]
def baseStart_2202602 : Nat := 118140960795 + 2202602 * 2 ^ 59
def prefixEnd_2202602 : Nat := 4983230072969 + 3 ^ 40 * 2202602 * 2
def baseEnd_2202602 : Nat := 27925765840851766499887

theorem tailTrace_2202602 : CollatzResearch.WordTrace tailWord_2202602 prefixEnd_2202602 27925765840851766499887 := by
  unfold tailWord_2202602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20083873691589150829482515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53556996510904402211953373 20083873691589150829482515)
  ·
    refine ⟨30125810537383726244223773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20083873691589150829482515 30125810537383726244223773)
    ·
      refine ⟨11297178951518897341583915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30125810537383726244223773 11297178951518897341583915)
      ·
        refine ⟨16945768427278346012375873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11297178951518897341583915 16945768427278346012375873)
        ·
          refine ⟨12709326320458759509281905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16945768427278346012375873 12709326320458759509281905)
          ·
            refine ⟨9531994740344069631961429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12709326320458759509281905 9531994740344069631961429)
            ·
              refine ⟨27925765840851766499887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9531994740344069631961429 27925765840851766499887)
              ·
                rfl

theorem cell22_2202602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 10].length) (baseStart_2202602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202602 prefixEnd_2202602 := by exact prefixLift 2202602
  have htrace : WordTrace (prefixWord ++ tailWord_2202602) baseStart_2202602 baseEnd_2202602 := by
    simpa [prefixWord, tailWord_2202602, baseEnd_2202602] using wordTrace_append hprefix tailTrace_2202602
  have hstable : (prefixWord ++ tailWord_2202602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202602).length < 2 ^ (prefixWord ++ tailWord_2202602).sum := by decide
  have hdescent : baseEnd_2202602 < baseStart_2202602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202760 : List Nat := [2, 1, 3, 4, 2, 2, 1, 3, 4]
def baseStart_2202760 : Nat := 118140960795 + 2202760 * 2 ^ 59
def prefixEnd_2202760 : Nat := 4983230072969 + 3 ^ 40 * 2202760 * 2
def baseEnd_2202760 : Nat := 251349921443979316682155

theorem tailTrace_2202760 : CollatzResearch.WordTrace tailWord_2202760 prefixEnd_2202760 251349921443979316682155 := by
  unfold tailWord_2202760
  simp only [CollatzResearch.WordTrace]
  refine ⟨40170628749892098151090867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53560838333189464201454489 40170628749892098151090867)
  ·
    refine ⟨60255943124838147226636301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40170628749892098151090867 60255943124838147226636301)
    ·
      refine ⟨22595978671814305209988613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60255943124838147226636301 22595978671814305209988613)
      ·
        refine ⟨4236746000965182226872865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22595978671814305209988613 4236746000965182226872865)
        ·
          refine ⟨3177559500723886670154649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4236746000965182226872865 3177559500723886670154649)
          ·
            refine ⟨2383169625542915002615987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3177559500723886670154649 2383169625542915002615987)
            ·
              refine ⟨3574754438314372503923981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383169625542915002615987 3574754438314372503923981)
              ·
                refine ⟨1340532914367889688971493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3574754438314372503923981 1340532914367889688971493)
                ·
                  refine ⟨251349921443979316682155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340532914367889688971493 251349921443979316682155)
                  ·
                    rfl

theorem cell22_2202760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 4].length) (baseStart_2202760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202760 prefixEnd_2202760 := by exact prefixLift 2202760
  have htrace : WordTrace (prefixWord ++ tailWord_2202760) baseStart_2202760 baseEnd_2202760 := by
    simpa [prefixWord, tailWord_2202760, baseEnd_2202760] using wordTrace_append hprefix tailTrace_2202760
  have hstable : (prefixWord ++ tailWord_2202760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202760).length < 2 ^ (prefixWord ++ tailWord_2202760).sum := by decide
  have hdescent : baseEnd_2202760 < baseStart_2202760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202784 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_2202784 : Nat := 118140960795 + 2202784 * 2 ^ 59
def prefixEnd_2202784 : Nat := 4983230072969 + 3 ^ 40 * 2202784 * 2
def baseEnd_2202784 : Nat := 754057980022409887446391

theorem tailTrace_2202784 : CollatzResearch.WordTrace tailWord_2202784 prefixEnd_2202784 754057980022409887446391 := by
  unfold tailWord_2202784
  simp only [CollatzResearch.WordTrace]
  refine ⟨40171066425848624200527703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53561421901131498934036937 40171066425848624200527703)
  ·
    refine ⟨60256599638772936300791555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40171066425848624200527703 60256599638772936300791555)
    ·
      refine ⟨90384899458159404451187333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60256599638772936300791555 90384899458159404451187333)
      ·
        refine ⟨16947168648404888334597625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90384899458159404451187333 16947168648404888334597625)
        ·
          refine ⟨12710376486303666250948219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16947168648404888334597625 12710376486303666250948219)
          ·
            refine ⟨19065564729455499376422329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12710376486303666250948219 19065564729455499376422329)
            ·
              refine ⟨14299173547091624532316747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19065564729455499376422329 14299173547091624532316747)
              ·
                refine ⟨21448760320637436798475121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14299173547091624532316747 21448760320637436798475121)
                ·
                  refine ⟨16086570240478077598856341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21448760320637436798475121 16086570240478077598856341)
                  ·
                    refine ⟨754057980022409887446391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16086570240478077598856341 754057980022409887446391)
                    ·
                      rfl

theorem cell22_2202784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_2202784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202784 prefixEnd_2202784 := by exact prefixLift 2202784
  have htrace : WordTrace (prefixWord ++ tailWord_2202784) baseStart_2202784 baseEnd_2202784 := by
    simpa [prefixWord, tailWord_2202784, baseEnd_2202784] using wordTrace_append hprefix tailTrace_2202784
  have hstable : (prefixWord ++ tailWord_2202784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202784).length < 2 ^ (prefixWord ++ tailWord_2202784).sum := by decide
  have hdescent : baseEnd_2202784 < baseStart_2202784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202837 : List Nat := [1, 3, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_2202837 : Nat := 118140960795 + 2202837 * 2 ^ 59
def prefixEnd_2202837 : Nat := 4983230072969 + 3 ^ 40 * 2202837 * 2
def baseEnd_2202837 : Nat := 754076123005535415871229

theorem tailTrace_2202837 : CollatzResearch.WordTrace tailWord_2202837 prefixEnd_2202837 754076123005535415871229 := by
  unfold tailWord_2202837
  simp only [CollatzResearch.WordTrace]
  refine ⟨80344065920505238452734765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53562710613670158968489843 80344065920505238452734765)
  ·
    refine ⟨30129024720189464419775537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80344065920505238452734765 30129024720189464419775537)
    ·
      refine ⟨22596768540142098314831653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30129024720189464419775537 22596768540142098314831653)
      ·
        refine ⟨4236894101276643434030935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22596768540142098314831653 4236894101276643434030935)
        ·
          refine ⟨6355341151914965151046403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236894101276643434030935 6355341151914965151046403)
          ·
            refine ⟨9533011727872447726569605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6355341151914965151046403 9533011727872447726569605)
            ·
              refine ⟨1787439698976083948731801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9533011727872447726569605 1787439698976083948731801)
              ·
                refine ⟨1340579774232062961548851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787439698976083948731801 1340579774232062961548851)
                ·
                  refine ⟨2010869661348094442323277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340579774232062961548851 2010869661348094442323277)
                  ·
                    refine ⟨754076123005535415871229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2010869661348094442323277 754076123005535415871229)
                    ·
                      rfl

theorem cell22_2202837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_2202837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202837 prefixEnd_2202837 := by exact prefixLift 2202837
  have htrace : WordTrace (prefixWord ++ tailWord_2202837) baseStart_2202837 baseEnd_2202837 := by
    simpa [prefixWord, tailWord_2202837, baseEnd_2202837] using wordTrace_append hprefix tailTrace_2202837
  have hstable : (prefixWord ++ tailWord_2202837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202837).length < 2 ^ (prefixWord ++ tailWord_2202837).sum := by decide
  have hdescent : baseEnd_2202837 < baseStart_2202837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202861 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2202861 : Nat := 118140960795 + 2202861 * 2 ^ 59
def prefixEnd_2202861 : Nat := 4983230072969 + 3 ^ 40 * 2202861 * 2
def baseEnd_2202861 : Nat := 251361446232002451090385

theorem tailTrace_2202861 : CollatzResearch.WordTrace tailWord_2202861 prefixEnd_2202861 251361446232002451090385 := by
  unfold tailWord_2202861
  simp only [CollatzResearch.WordTrace]
  refine ⟨80344941272418290551608437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53563294181612193701072291 80344941272418290551608437)
  ·
    refine ⟨7532338244289214739213291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80344941272418290551608437 7532338244289214739213291)
    ·
      refine ⟨11298507366433822108819937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7532338244289214739213291 11298507366433822108819937)
      ·
        refine ⟨8473880524825366581614953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11298507366433822108819937 8473880524825366581614953)
        ·
          refine ⟨6355410393619024936211215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8473880524825366581614953 6355410393619024936211215)
          ·
            refine ⟨9533115590428537404316823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6355410393619024936211215 9533115590428537404316823)
            ·
              refine ⟨14299673385642806106475235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9533115590428537404316823 14299673385642806106475235)
              ·
                refine ⟨21449510078464209159712853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14299673385642806106475235 21449510078464209159712853)
                ·
                  refine ⟨251361446232002451090385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21449510078464209159712853 251361446232002451090385)
                  ·
                    rfl

theorem cell22_2202861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2202861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202861 prefixEnd_2202861 := by exact prefixLift 2202861
  have htrace : WordTrace (prefixWord ++ tailWord_2202861) baseStart_2202861 baseEnd_2202861 := by
    simpa [prefixWord, tailWord_2202861, baseEnd_2202861] using wordTrace_append hprefix tailTrace_2202861
  have hstable : (prefixWord ++ tailWord_2202861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202861).length < 2 ^ (prefixWord ++ tailWord_2202861).sum := by decide
  have hdescent : baseEnd_2202861 < baseStart_2202861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202889 : List Nat := [1, 2, 1, 1, 3, 3, 11]
def baseStart_2202889 : Nat := 118140960795 + 2202889 * 2 ^ 59
def prefixEnd_2202889 : Nat := 4983230072969 + 3 ^ 40 * 2202889 * 2
def baseEnd_2202889 : Nat := 27929404580304615317447

theorem tailTrace_2202889 : CollatzResearch.WordTrace tailWord_2202889 prefixEnd_2202889 27929404580304615317447 := by
  unfold tailWord_2202889
  simp only [CollatzResearch.WordTrace]
  refine ⟨80345962516316851333627721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53563975010877900889085147 80345962516316851333627721)
  ·
    refine ⟨60259471887237638500220791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80345962516316851333627721 60259471887237638500220791)
    ·
      refine ⟨90389207830856457750331187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60259471887237638500220791 90389207830856457750331187)
      ·
        refine ⟨135583811746284686625496781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90389207830856457750331187 135583811746284686625496781)
        ·
          refine ⟨50843929404856757484561293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135583811746284686625496781 50843929404856757484561293)
          ·
            refine ⟨19066473526821284056710485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50843929404856757484561293 19066473526821284056710485)
            ·
              refine ⟨27929404580304615317447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19066473526821284056710485 27929404580304615317447)
              ·
                rfl

theorem cell22_2202889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 11].length) (baseStart_2202889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202889 prefixEnd_2202889 := by exact prefixLift 2202889
  have htrace : WordTrace (prefixWord ++ tailWord_2202889) baseStart_2202889 baseEnd_2202889 := by
    simpa [prefixWord, tailWord_2202889, baseEnd_2202889] using wordTrace_append hprefix tailTrace_2202889
  have hstable : (prefixWord ++ tailWord_2202889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202889).length < 2 ^ (prefixWord ++ tailWord_2202889).sum := by decide
  have hdescent : baseEnd_2202889 < baseStart_2202889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202921 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 9, 3]
def baseStart_2202921 : Nat := 118140960795 + 2202921 * 2 ^ 59
def prefixEnd_2202921 : Nat := 4983230072969 + 3 ^ 40 * 2202921 * 2
def baseEnd_2202921 : Nat := 754104877922187196770971

theorem tailTrace_2202921 : CollatzResearch.WordTrace tailWord_2202921 prefixEnd_2202921 754104877922187196770971 := by
  unfold tailWord_2202921
  simp only [CollatzResearch.WordTrace]
  refine ⟨80347129652200920798792617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53564753101467280532528411 80347129652200920798792617)
  ·
    refine ⟨60260347239150690599094463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80347129652200920798792617 60260347239150690599094463)
    ·
      refine ⟨90390520858726035898641695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60260347239150690599094463 90390520858726035898641695)
      ·
        refine ⟨135585781288089053847962543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90390520858726035898641695 135585781288089053847962543)
        ·
          refine ⟨203378671932133580771943815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135585781288089053847962543 203378671932133580771943815)
          ·
            refine ⟨305068007898200371157915723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203378671932133580771943815 305068007898200371157915723)
            ·
              refine ⟨457602011847300556736873585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305068007898200371157915723 457602011847300556736873585)
              ·
                refine ⟨343201508885475417552655189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457602011847300556736873585 343201508885475417552655189)
                ·
                  refine ⟨2010946341125832524722589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 343201508885475417552655189 2010946341125832524722589)
                  ·
                    refine ⟨754104877922187196770971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2010946341125832524722589 754104877922187196770971)
                    ·
                      rfl

theorem cell22_2202921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_2202921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202921 prefixEnd_2202921 := by exact prefixLift 2202921
  have htrace : WordTrace (prefixWord ++ tailWord_2202921) baseStart_2202921 baseEnd_2202921 := by
    simpa [prefixWord, tailWord_2202921, baseEnd_2202921] using wordTrace_append hprefix tailTrace_2202921
  have hstable : (prefixWord ++ tailWord_2202921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202921).length < 2 ^ (prefixWord ++ tailWord_2202921).sum := by decide
  have hdescent : baseEnd_2202921 < baseStart_2202921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202951 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 7]
def baseStart_2202951 : Nat := 118140960795 + 2202951 * 2 ^ 59
def prefixEnd_2202951 : Nat := 4983230072969 + 3 ^ 40 * 2202951 * 2
def baseEnd_2202951 : Nat := 251371715845092372840293

theorem tailTrace_2202951 : CollatzResearch.WordTrace tailWord_2202951 prefixEnd_2202951 251371715845092372840293 := by
  unfold tailWord_2202951
  simp only [CollatzResearch.WordTrace]
  refine ⟨80348223842092235922384707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53565482561394823948256471 80348223842092235922384707)
  ·
    refine ⟨120522335763138353883577061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80348223842092235922384707 120522335763138353883577061)
    ·
      refine ⟨22597937955588441353170699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120522335763138353883577061 22597937955588441353170699)
      ·
        refine ⟨33896906933382662029756049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22597937955588441353170699 33896906933382662029756049)
        ·
          refine ⟨25422680200036996522317037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33896906933382662029756049 25422680200036996522317037)
          ·
            refine ⟨9533505075013873695868889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25422680200036996522317037 9533505075013873695868889)
            ·
              refine ⟨7150128806260405271901667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9533505075013873695868889 7150128806260405271901667)
              ·
                refine ⟨10725193209390607907852501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150128806260405271901667 10725193209390607907852501)
                ·
                  refine ⟨251371715845092372840293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10725193209390607907852501 251371715845092372840293)
                  ·
                    rfl

theorem cell22_2202951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 7].length) (baseStart_2202951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202951 prefixEnd_2202951 := by exact prefixLift 2202951
  have htrace : WordTrace (prefixWord ++ tailWord_2202951) baseStart_2202951 baseEnd_2202951 := by
    simpa [prefixWord, tailWord_2202951, baseEnd_2202951] using wordTrace_append hprefix tailTrace_2202951
  have hstable : (prefixWord ++ tailWord_2202951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202951).length < 2 ^ (prefixWord ++ tailWord_2202951).sum := by decide
  have hdescent : baseEnd_2202951 < baseStart_2202951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203006 : List Nat := [4, 2, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2203006 : Nat := 118140960795 + 2203006 * 2 ^ 59
def prefixEnd_2203006 : Nat := 4983230072969 + 3 ^ 40 * 2203006 * 2
def baseEnd_2203006 : Nat := 754133975159275308395711

theorem tailTrace_2203006 : CollatzResearch.WordTrace tailWord_2203006 prefixEnd_2203006 754133975159275308395711 := by
  unfold tailWord_2203006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10043778732111622539454609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53566819904595320210424581 10043778732111622539454609)
  ·
    refine ⟨7532834049083716904590957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10043778732111622539454609 7532834049083716904590957)
    ·
      refine ⟨2824812768406393839221609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7532834049083716904590957 2824812768406393839221609)
      ·
        refine ⟨2118609576304795379416207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2824812768406393839221609 2118609576304795379416207)
        ·
          refine ⟨3177914364457193069124311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118609576304795379416207 3177914364457193069124311)
          ·
            refine ⟨4766871546685789603686467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3177914364457193069124311 4766871546685789603686467)
            ·
              refine ⟨7150307320028684405529701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4766871546685789603686467 7150307320028684405529701)
              ·
                refine ⟨1340682622505378326036819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7150307320028684405529701 1340682622505378326036819)
                ·
                  refine ⟨2011023933758067489055229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340682622505378326036819 2011023933758067489055229)
                  ·
                    refine ⟨754133975159275308395711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011023933758067489055229 754133975159275308395711)
                    ·
                      rfl

theorem cell22_2203006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2203006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203006 prefixEnd_2203006 := by exact prefixLift 2203006
  have htrace : WordTrace (prefixWord ++ tailWord_2203006) baseStart_2203006 baseEnd_2203006 := by
    simpa [prefixWord, tailWord_2203006, baseEnd_2203006] using wordTrace_append hprefix tailTrace_2203006
  have hstable : (prefixWord ++ tailWord_2203006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203006).length < 2 ^ (prefixWord ++ tailWord_2203006).sum := by decide
  have hdescent : baseEnd_2203006 < baseStart_2203006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203071 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 1, 8]
def baseStart_2203071 : Nat := 118140960795 + 2203071 * 2 ^ 59
def prefixEnd_2203071 : Nat := 4983230072969 + 3 ^ 40 * 2203071 * 2
def baseEnd_2203071 : Nat := 754156225987636805520511

theorem tailTrace_2203071 : CollatzResearch.WordTrace tailWord_2203071 prefixEnd_2203071 754156225987636805520511 := by
  unfold tailWord_2203071
  simp only [CollatzResearch.WordTrace]
  refine ⟨80352600601657496416753067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53568400401104997611168711 80352600601657496416753067)
  ·
    refine ⟨120528900902486244625129601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80352600601657496416753067 120528900902486244625129601)
    ·
      refine ⟨90396675676864683468847201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120528900902486244625129601 90396675676864683468847201)
      ·
        refine ⟨67797506757648512601635401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90396675676864683468847201 67797506757648512601635401)
        ·
          refine ⟨50848130068236384451226551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67797506757648512601635401 50848130068236384451226551)
          ·
            refine ⟨76272195102354576676839827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50848130068236384451226551 76272195102354576676839827)
            ·
              refine ⟨114408292653531865015259741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76272195102354576676839827 114408292653531865015259741)
              ·
                refine ⟨42903109745074449380722403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114408292653531865015259741 42903109745074449380722403)
                ·
                  refine ⟨64354664617611674071083605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42903109745074449380722403 64354664617611674071083605)
                  ·
                    refine ⟨754156225987636805520511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64354664617611674071083605 754156225987636805520511)
                    ·
                      rfl

theorem cell22_2203071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_2203071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203071 prefixEnd_2203071 := by exact prefixLift 2203071
  have htrace : WordTrace (prefixWord ++ tailWord_2203071) baseStart_2203071 baseEnd_2203071 := by
    simpa [prefixWord, tailWord_2203071, baseEnd_2203071] using wordTrace_append hprefix tailTrace_2203071
  have hstable : (prefixWord ++ tailWord_2203071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203071).length < 2 ^ (prefixWord ++ tailWord_2203071).sum := by decide
  have hdescent : baseEnd_2203071 < baseStart_2203071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203092 : List Nat := [2, 4, 1, 2, 3, 2, 2, 6]
def baseStart_2203092 : Nat := 118140960795 + 2203092 * 2 ^ 59
def prefixEnd_2203092 : Nat := 4983230072969 + 3 ^ 40 * 2203092 * 2
def baseEnd_2203092 : Nat := 83795934968533305638383

theorem tailTrace_2203092 : CollatzResearch.WordTrace tailWord_2203092 prefixEnd_2203092 83795934968533305638383 := by
  unfold tailWord_2203092
  simp only [CollatzResearch.WordTrace]
  refine ⟨40176683267290708501633765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53568911023054278002178353 40176683267290708501633765)
  ·
    refine ⟨7533128112617007844056331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40176683267290708501633765 7533128112617007844056331)
    ·
      refine ⟨11299692168925511766084497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7533128112617007844056331 11299692168925511766084497)
      ·
        refine ⟨8474769126694133824563373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11299692168925511766084497 8474769126694133824563373)
        ·
          refine ⟨3178038422510300184211265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8474769126694133824563373 3178038422510300184211265)
          ·
            refine ⟨2383528816882725138158449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3178038422510300184211265 2383528816882725138158449)
            ·
              refine ⟨1787646612662043853618837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2383528816882725138158449 1787646612662043853618837)
              ·
                refine ⟨83795934968533305638383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1787646612662043853618837 83795934968533305638383)
                ·
                  rfl

theorem cell22_2203092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 6].length) (baseStart_2203092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203092 prefixEnd_2203092 := by exact prefixLift 2203092
  have htrace : WordTrace (prefixWord ++ tailWord_2203092) baseStart_2203092 baseEnd_2203092 := by
    simpa [prefixWord, tailWord_2203092, baseEnd_2203092] using wordTrace_append hprefix tailTrace_2203092
  have hstable : (prefixWord ++ tailWord_2203092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203092).length < 2 ^ (prefixWord ++ tailWord_2203092).sum := by decide
  have hdescent : baseEnd_2203092 < baseStart_2203092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203197 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_2203197 : Nat := 118140960795 + 2203197 * 2 ^ 59
def prefixEnd_2203197 : Nat := 4983230072969 + 3 ^ 40 * 2203197 * 2
def baseEnd_2203197 : Nat := 754199358362614476870125

theorem tailTrace_2203197 : CollatzResearch.WordTrace tailWord_2203197 prefixEnd_2203197 754199358362614476870125 := by
  unfold tailWord_2203197
  simp only [CollatzResearch.WordTrace]
  refine ⟨80357196199201019935839845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53571464132800679957226563 80357196199201019935839845)
  ·
    refine ⟨15066974287350191237969971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80357196199201019935839845 15066974287350191237969971)
    ·
      refine ⟨22600461431025286856954957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15066974287350191237969971 22600461431025286856954957)
      ·
        refine ⟨8475173036634482571358109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22600461431025286856954957 8475173036634482571358109)
        ·
          refine ⟨3178189888737930964259291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8475173036634482571358109 3178189888737930964259291)
          ·
            refine ⟨4767284833106896446388937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178189888737930964259291 4767284833106896446388937)
            ·
              refine ⟨3575463624830172334791703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4767284833106896446388937 3575463624830172334791703)
              ·
                refine ⟨5363195437245258502187555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575463624830172334791703 5363195437245258502187555)
                ·
                  refine ⟨8044793155867887753281333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363195437245258502187555 8044793155867887753281333)
                  ·
                    refine ⟨754199358362614476870125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8044793155867887753281333 754199358362614476870125)
                    ·
                      rfl

theorem cell22_2203197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_2203197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203197 prefixEnd_2203197 := by exact prefixLift 2203197
  have htrace : WordTrace (prefixWord ++ tailWord_2203197) baseStart_2203197 baseEnd_2203197 := by
    simpa [prefixWord, tailWord_2203197, baseEnd_2203197] using wordTrace_append hprefix tailTrace_2203197
  have hstable : (prefixWord ++ tailWord_2203197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203197).length < 2 ^ (prefixWord ++ tailWord_2203197).sum := by decide
  have hdescent : baseEnd_2203197 < baseStart_2203197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203210 : List Nat := [3, 1, 2, 1, 1, 3, 5, 6]
def baseStart_2203210 : Nat := 118140960795 + 2203210 * 2 ^ 59
def prefixEnd_2203210 : Nat := 4983230072969 + 3 ^ 40 * 2203210 * 2
def baseEnd_2203210 : Nat := 83800423169809641810565

theorem tailTrace_2203210 : CollatzResearch.WordTrace tailWord_2203210 prefixEnd_2203210 83800423169809641810565 := by
  unfold tailWord_2203210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20089417587038480789015771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53571780232102615437375389 20089417587038480789015771)
  ·
    refine ⟨30134126380557721183523657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20089417587038480789015771 30134126380557721183523657)
    ·
      refine ⟨22600594785418290887642743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30134126380557721183523657 22600594785418290887642743)
      ·
        refine ⟨33900892178127436331464115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22600594785418290887642743 33900892178127436331464115)
        ·
          refine ⟨50851338267191154497196173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33900892178127436331464115 50851338267191154497196173)
          ·
            refine ⟨19069251850196682936448565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50851338267191154497196173 19069251850196682936448565)
            ·
              refine ⟨1787742360955939025292053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19069251850196682936448565 1787742360955939025292053)
              ·
                refine ⟨83800423169809641810565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1787742360955939025292053 83800423169809641810565)
                ·
                  rfl

theorem cell22_2203210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_2203210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203210 prefixEnd_2203210 := by exact prefixLift 2203210
  have htrace : WordTrace (prefixWord ++ tailWord_2203210) baseStart_2203210 baseEnd_2203210 := by
    simpa [prefixWord, tailWord_2203210, baseEnd_2203210] using wordTrace_append hprefix tailTrace_2203210
  have hstable : (prefixWord ++ tailWord_2203210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203210).length < 2 ^ (prefixWord ++ tailWord_2203210).sum := by decide
  have hdescent : baseEnd_2203210 < baseStart_2203210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203212 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_2203212 : Nat := 118140960795 + 2203212 * 2 ^ 59
def prefixEnd_2203212 : Nat := 4983230072969 + 3 ^ 40 * 2203212 * 2
def baseEnd_2203212 : Nat := 754204493169159437745079

theorem tailTrace_2203212 : CollatzResearch.WordTrace tailWord_2203212 prefixEnd_2203212 754204493169159437745079 := by
  unfold tailWord_2203212
  simp only [CollatzResearch.WordTrace]
  refine ⟨40178871647073338748817945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53571828862764451665090593 40178871647073338748817945)
  ·
    refine ⟨30134153735305004061613459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40178871647073338748817945 30134153735305004061613459)
    ·
      refine ⟨45201230602957506092420189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30134153735305004061613459 45201230602957506092420189)
      ·
        refine ⟨16950461476109064784657571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45201230602957506092420189 16950461476109064784657571)
        ·
          refine ⟨25425692214163597176986357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16950461476109064784657571 25425692214163597176986357)
          ·
            refine ⟨2383658645077837235342471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25425692214163597176986357 2383658645077837235342471)
            ·
              refine ⟨3575487967616755853013707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383658645077837235342471 3575487967616755853013707)
              ·
                refine ⟨5363231951425133779520561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575487967616755853013707 5363231951425133779520561)
                ·
                  refine ⟨4022423963568850334640421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363231951425133779520561 4022423963568850334640421)
                  ·
                    refine ⟨754204493169159437745079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4022423963568850334640421 754204493169159437745079)
                    ·
                      rfl

theorem cell22_2203212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_2203212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203212 prefixEnd_2203212 := by exact prefixLift 2203212
  have htrace : WordTrace (prefixWord ++ tailWord_2203212) baseStart_2203212 baseEnd_2203212 := by
    simpa [prefixWord, tailWord_2203212, baseEnd_2203212] using wordTrace_append hprefix tailTrace_2203212
  have hstable : (prefixWord ++ tailWord_2203212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203212).length < 2 ^ (prefixWord ++ tailWord_2203212).sum := by decide
  have hdescent : baseEnd_2203212 < baseStart_2203212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203242 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_2203242 : Nat := 118140960795 + 2203242 * 2 ^ 59
def prefixEnd_2203242 : Nat := 4983230072969 + 3 ^ 40 * 2203242 * 2
def baseEnd_2203242 : Nat := 754214762782249359494987

theorem tailTrace_2203242 : CollatzResearch.WordTrace tailWord_2203242 prefixEnd_2203242 754214762782249359494987 := by
  unfold tailWord_2203242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20089709371009498155306995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53572558322691995080818653 20089709371009498155306995)
  ·
    refine ⟨30134564056514247232960493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20089709371009498155306995 30134564056514247232960493)
    ·
      refine ⟨11300461521192842712360185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30134564056514247232960493 11300461521192842712360185)
      ·
        refine ⟨8475346140894632034270139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11300461521192842712360185 8475346140894632034270139)
        ·
          refine ⟨12713019211341948051405209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8475346140894632034270139 12713019211341948051405209)
          ·
            refine ⟨9534764408506461038553907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12713019211341948051405209 9534764408506461038553907)
            ·
              refine ⟨14302146612759691557830861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9534764408506461038553907 14302146612759691557830861)
              ·
                refine ⟨5363304979784884334186573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14302146612759691557830861 5363304979784884334186573)
                ·
                  refine ⟨2011239367419331625319965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5363304979784884334186573 2011239367419331625319965)
                  ·
                    refine ⟨754214762782249359494987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011239367419331625319965 754214762782249359494987)
                    ·
                      rfl

theorem cell22_2203242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_2203242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203242 prefixEnd_2203242 := by exact prefixLift 2203242
  have htrace : WordTrace (prefixWord ++ tailWord_2203242) baseStart_2203242 baseEnd_2203242 := by
    simpa [prefixWord, tailWord_2203242, baseEnd_2203242] using wordTrace_append hprefix tailTrace_2203242
  have hstable : (prefixWord ++ tailWord_2203242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203242).length < 2 ^ (prefixWord ++ tailWord_2203242).sum := by decide
  have hdescent : baseEnd_2203242 < baseStart_2203242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203315 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 1, 5]
def baseStart_2203315 : Nat := 118140960795 + 2203315 * 2 ^ 59
def prefixEnd_2203315 : Nat := 4983230072969 + 3 ^ 40 * 2203315 * 2
def baseEnd_2203315 : Nat := 754239752174101502419763

theorem tailTrace_2203315 : CollatzResearch.WordTrace tailWord_2203315 prefixEnd_2203315 754239752174101502419763 := by
  unfold tailWord_2203315
  simp only [CollatzResearch.WordTrace]
  refine ⟨80361500012773526088635399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53574333341849017392423599 80361500012773526088635399)
  ·
    refine ⟨120542250019160289132953099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80361500012773526088635399 120542250019160289132953099)
    ·
      refine ⟨180813375028740433699429649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120542250019160289132953099 180813375028740433699429649)
      ·
        refine ⟨135610031271555325274572237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180813375028740433699429649 135610031271555325274572237)
        ·
          refine ⟨50853761726833246977964589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135610031271555325274572237 50853761726833246977964589)
          ·
            refine ⟨19070160647562467616736721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50853761726833246977964589 19070160647562467616736721)
            ·
              refine ⟨14302620485671850712552541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19070160647562467616736721 14302620485671850712552541)
              ·
                refine ⟨5363482682126944017207203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14302620485671850712552541 5363482682126944017207203)
                ·
                  refine ⟨8045224023190416025810805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363482682126944017207203 8045224023190416025810805)
                  ·
                    refine ⟨754239752174101502419763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8045224023190416025810805 754239752174101502419763)
                    ·
                      rfl

theorem cell22_2203315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_2203315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203315 prefixEnd_2203315 := by exact prefixLift 2203315
  have htrace : WordTrace (prefixWord ++ tailWord_2203315) baseStart_2203315 baseEnd_2203315 := by
    simpa [prefixWord, tailWord_2203315, baseEnd_2203315] using wordTrace_append hprefix tailTrace_2203315
  have hstable : (prefixWord ++ tailWord_2203315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203315).length < 2 ^ (prefixWord ++ tailWord_2203315).sum := by decide
  have hdescent : baseEnd_2203315 < baseStart_2203315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203319 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 1, 4]
def baseStart_2203319 : Nat := 118140960795 + 2203319 * 2 ^ 59
def prefixEnd_2203319 : Nat := 4983230072969 + 3 ^ 40 * 2203319 * 2
def baseEnd_2203319 : Nat := 754241121455846825319751

theorem tailTrace_2203319 : CollatzResearch.WordTrace tailWord_2203319 prefixEnd_2203319 754241121455846825319751 := by
  unfold tailWord_2203319
  simp only [CollatzResearch.WordTrace]
  refine ⟨80361645904759034771781011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53574430603172689847854007 80361645904759034771781011)
  ·
    refine ⟨120542468857138552157671517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80361645904759034771781011 120542468857138552157671517)
    ·
      refine ⟨45203425821426957059126819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120542468857138552157671517 45203425821426957059126819)
      ·
        refine ⟨67805138732140435588690229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45203425821426957059126819 67805138732140435588690229)
        ·
          refine ⟨6356731756138165836439709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67805138732140435588690229 6356731756138165836439709)
          ·
            refine ⟨2383774408551812188664891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6356731756138165836439709 2383774408551812188664891)
            ·
              refine ⟨3575661612827718282997337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383774408551812188664891 3575661612827718282997337)
              ·
                refine ⟨2681746209620788712248003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3575661612827718282997337 2681746209620788712248003)
                ·
                  refine ⟨4022619314431183068372005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681746209620788712248003 4022619314431183068372005)
                  ·
                    refine ⟨754241121455846825319751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4022619314431183068372005 754241121455846825319751)
                    ·
                      rfl

theorem cell22_2203319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_2203319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203319 prefixEnd_2203319 := by exact prefixLift 2203319
  have htrace : WordTrace (prefixWord ++ tailWord_2203319) baseStart_2203319 baseEnd_2203319 := by
    simpa [prefixWord, tailWord_2203319, baseEnd_2203319] using wordTrace_append hprefix tailTrace_2203319
  have hstable : (prefixWord ++ tailWord_2203319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203319).length < 2 ^ (prefixWord ++ tailWord_2203319).sum := by decide
  have hdescent : baseEnd_2203319 < baseStart_2203319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203332 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2203332 : Nat := 118140960795 + 2203332 * 2 ^ 59
def prefixEnd_2203332 : Nat := 4983230072969 + 3 ^ 40 * 2203332 * 2
def baseEnd_2203332 : Nat := 754245571621519124744711

theorem tailTrace_2203332 : CollatzResearch.WordTrace tailWord_2203332 prefixEnd_2203332 754245571621519124744711 := by
  unfold tailWord_2203332
  simp only [CollatzResearch.WordTrace]
  refine ⟨40181060026855968996002125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53574746702474625328002833 40181060026855968996002125)
  ·
    refine ⟨15067897510070988373500797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40181060026855968996002125 15067897510070988373500797)
    ·
      refine ⟨5650461566276620640062799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15067897510070988373500797 5650461566276620640062799)
      ·
        refine ⟨8475692349414930960094199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5650461566276620640062799 8475692349414930960094199)
        ·
          refine ⟨12713538524122396440141299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8475692349414930960094199 12713538524122396440141299)
          ·
            refine ⟨19070307786183594660211949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12713538524122396440141299 19070307786183594660211949)
            ·
              refine ⟨7151365419818847997579481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19070307786183594660211949 7151365419818847997579481)
              ·
                refine ⟨5363524064864135998184611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7151365419818847997579481 5363524064864135998184611)
                ·
                  refine ⟨8045286097296203997276917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363524064864135998184611 8045286097296203997276917)
                  ·
                    refine ⟨754245571621519124744711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8045286097296203997276917 754245571621519124744711)
                    ·
                      rfl

theorem cell22_2203332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2203332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203332 prefixEnd_2203332 := by exact prefixLift 2203332
  have htrace : WordTrace (prefixWord ++ tailWord_2203332) baseStart_2203332 baseEnd_2203332 := by
    simpa [prefixWord, tailWord_2203332, baseEnd_2203332] using wordTrace_append hprefix tailTrace_2203332
  have hstable : (prefixWord ++ tailWord_2203332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203332).length < 2 ^ (prefixWord ++ tailWord_2203332).sum := by decide
  have hdescent : baseEnd_2203332 < baseStart_2203332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203375 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 2, 6]
def baseStart_2203375 : Nat := 118140960795 + 2203375 * 2 ^ 59
def prefixEnd_2203375 : Nat := 4983230072969 + 3 ^ 40 * 2203375 * 2
def baseEnd_2203375 : Nat := 754260291400281345919579

theorem tailTrace_2203375 : CollatzResearch.WordTrace tailWord_2203375 prefixEnd_2203375 754260291400281345919579 := by
  unfold tailWord_2203375
  simp only [CollatzResearch.WordTrace]
  refine ⟨80363688392556156335819579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53575792261704104223879719 80363688392556156335819579)
  ·
    refine ⟨120545532588834234503729369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80363688392556156335819579 120545532588834234503729369)
    ·
      refine ⟨90409149441625675877797027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120545532588834234503729369 90409149441625675877797027)
      ·
        refine ⟨135613724162438513816695541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90409149441625675877797027 135613724162438513816695541)
        ·
          refine ⟨12713786640228610670315207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135613724162438513816695541 12713786640228610670315207)
          ·
            refine ⟨19070679960342916005472811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12713786640228610670315207 19070679960342916005472811)
            ·
              refine ⟨28606019940514374008209217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19070679960342916005472811 28606019940514374008209217)
              ·
                refine ⟨21454514955385780506156913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28606019940514374008209217 21454514955385780506156913)
                ·
                  refine ⟨16090886216539335379617685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21454514955385780506156913 16090886216539335379617685)
                  ·
                    refine ⟨754260291400281345919579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16090886216539335379617685 754260291400281345919579)
                    ·
                      rfl

theorem cell22_2203375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_2203375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203375 prefixEnd_2203375 := by exact prefixLift 2203375
  have htrace : WordTrace (prefixWord ++ tailWord_2203375) baseStart_2203375 baseEnd_2203375 := by
    simpa [prefixWord, tailWord_2203375, baseEnd_2203375] using wordTrace_append hprefix tailTrace_2203375
  have hstable : (prefixWord ++ tailWord_2203375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203375).length < 2 ^ (prefixWord ++ tailWord_2203375).sum := by decide
  have hdescent : baseEnd_2203375 < baseStart_2203375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203377 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 5, 3]
def baseStart_2203377 : Nat := 118140960795 + 2203377 * 2 ^ 59
def prefixEnd_2203377 : Nat := 4983230072969 + 3 ^ 40 * 2203377 * 2
def baseEnd_2203377 : Nat := 754260976041154007369573

theorem tailTrace_2203377 : CollatzResearch.WordTrace tailWord_2203377 prefixEnd_2203377 754260976041154007369573 := by
  unfold tailWord_2203377
  simp only [CollatzResearch.WordTrace]
  refine ⟨80363761338548910677392385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53575840892365940451594923 80363761338548910677392385)
  ·
    refine ⟨60272821003911683008044289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80363761338548910677392385 60272821003911683008044289)
    ·
      refine ⟨45204615752933762256033217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60272821003911683008044289 45204615752933762256033217)
      ·
        refine ⟨33903461814700321692024913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45204615752933762256033217 33903461814700321692024913)
        ·
          refine ⟨25427596361025241269018685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33903461814700321692024913 25427596361025241269018685)
          ·
            refine ⟨9535348635384465475882007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25427596361025241269018685 9535348635384465475882007)
            ·
              refine ⟨14303022953076698213823011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9535348635384465475882007 14303022953076698213823011)
              ·
                refine ⟨21454534429615047320734517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14303022953076698213823011 21454534429615047320734517)
                ·
                  refine ⟨2011362602776410686318861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21454534429615047320734517 2011362602776410686318861)
                  ·
                    refine ⟨754260976041154007369573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011362602776410686318861 754260976041154007369573)
                    ·
                      rfl

theorem cell22_2203377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_2203377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203377 prefixEnd_2203377 := by exact prefixLift 2203377
  have htrace : WordTrace (prefixWord ++ tailWord_2203377) baseStart_2203377 baseEnd_2203377 := by
    simpa [prefixWord, tailWord_2203377, baseEnd_2203377] using wordTrace_append hprefix tailTrace_2203377
  have hstable : (prefixWord ++ tailWord_2203377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203377).length < 2 ^ (prefixWord ++ tailWord_2203377).sum := by decide
  have hdescent : baseEnd_2203377 < baseStart_2203377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203394 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2203394 : Nat := 118140960795 + 2203394 * 2 ^ 59
def prefixEnd_2203394 : Nat := 4983230072969 + 3 ^ 40 * 2203394 * 2
def baseEnd_2203394 : Nat := 754266795488571629694521

theorem tailTrace_2203394 : CollatzResearch.WordTrace tailWord_2203394 prefixEnd_2203394 754266795488571629694521 := by
  unfold tailWord_2203394
  simp only [CollatzResearch.WordTrace]
  refine ⟨20091095344871830645190309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53576254252991548387174157 20091095344871830645190309)
  ·
    refine ⟨3767080377163468245973183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20091095344871830645190309 3767080377163468245973183)
    ·
      refine ⟨5650620565745202368959775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3767080377163468245973183 5650620565745202368959775)
      ·
        refine ⟨8475930848617803553439663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5650620565745202368959775 8475930848617803553439663)
        ·
          refine ⟨12713896272926705330159495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8475930848617803553439663 12713896272926705330159495)
          ·
            refine ⟨19070844409390057995239243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12713896272926705330159495 19070844409390057995239243)
            ·
              refine ⟨28606266614085086992858865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19070844409390057995239243 28606266614085086992858865)
              ·
                refine ⟨21454699960563815244644149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28606266614085086992858865 21454699960563815244644149)
                ·
                  refine ⟨2011378121302857679185389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21454699960563815244644149 2011378121302857679185389)
                  ·
                    refine ⟨754266795488571629694521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011378121302857679185389 754266795488571629694521)
                    ·
                      rfl

theorem cell22_2203394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2203394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203394 prefixEnd_2203394 := by exact prefixLift 2203394
  have htrace : WordTrace (prefixWord ++ tailWord_2203394) baseStart_2203394 baseEnd_2203394 := by
    simpa [prefixWord, tailWord_2203394, baseEnd_2203394] using wordTrace_append hprefix tailTrace_2203394
  have hstable : (prefixWord ++ tailWord_2203394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203394).length < 2 ^ (prefixWord ++ tailWord_2203394).sum := by decide
  have hdescent : baseEnd_2203394 < baseStart_2203394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203424 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 5]
def baseStart_2203424 : Nat := 118140960795 + 2203424 * 2 ^ 59
def prefixEnd_2203424 : Nat := 4983230072969 + 3 ^ 40 * 2203424 * 2
def baseEnd_2203424 : Nat := 251425688367220517148143

theorem tailTrace_2203424 : CollatzResearch.WordTrace tailWord_2203424 prefixEnd_2203424 251425688367220517148143 := by
  unfold tailWord_2203424
  simp only [CollatzResearch.WordTrace]
  refine ⟨40182737784689318852176663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53576983712919091802902217 40182737784689318852176663)
  ·
    refine ⟨60274106677033978278264995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40182737784689318852176663 60274106677033978278264995)
    ·
      refine ⟨90411160015550967417397493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60274106677033978278264995 90411160015550967417397493)
      ·
        refine ⟨8476046251457903195381015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90411160015550967417397493 8476046251457903195381015)
        ·
          refine ⟨12714069377186854793071523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8476046251457903195381015 12714069377186854793071523)
          ·
            refine ⟨19071104065780282189607285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12714069377186854793071523 19071104065780282189607285)
            ·
              refine ⟨1787916006166901455275683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19071104065780282189607285 1787916006166901455275683)
              ·
                refine ⟨2681874009250352182913525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787916006166901455275683 2681874009250352182913525)
                ·
                  refine ⟨251425688367220517148143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2681874009250352182913525 251425688367220517148143)
                  ·
                    rfl

theorem cell22_2203424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_2203424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203424 prefixEnd_2203424 := by exact prefixLift 2203424
  have htrace : WordTrace (prefixWord ++ tailWord_2203424) baseStart_2203424 baseEnd_2203424 := by
    simpa [prefixWord, tailWord_2203424, baseEnd_2203424] using wordTrace_append hprefix tailTrace_2203424
  have hstable : (prefixWord ++ tailWord_2203424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203424).length < 2 ^ (prefixWord ++ tailWord_2203424).sum := by decide
  have hdescent : baseEnd_2203424 < baseStart_2203424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203445 : List Nat := [1, 3, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_2203445 : Nat := 118140960795 + 2203445 * 2 ^ 59
def prefixEnd_2203445 : Nat := 4983230072969 + 3 ^ 40 * 2203445 * 2
def baseEnd_2203445 : Nat := 754284253830824496669365

theorem tailTrace_2203445 : CollatzResearch.WordTrace tailWord_2203445 prefixEnd_2203445 754284253830824496669365 := by
  unfold tailWord_2203445
  simp only [CollatzResearch.WordTrace]
  refine ⟨80366241502302558290867789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53577494334868372193911859 80366241502302558290867789)
  ·
    refine ⟨30137340563363459359075421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80366241502302558290867789 30137340563363459359075421)
    ·
      refine ⟨11301502711261297259653283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30137340563363459359075421 11301502711261297259653283)
      ·
        refine ⟨16952254066891945889479925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11301502711261297259653283 16952254066891945889479925)
        ·
          refine ⟨1589273818771119927138743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16952254066891945889479925 1589273818771119927138743)
          ·
            refine ⟨2383910728156679890708115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589273818771119927138743 2383910728156679890708115)
            ·
              refine ⟨3575866092235019836062173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383910728156679890708115 3575866092235019836062173)
              ·
                refine ⟨1340949784588132438523315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3575866092235019836062173 1340949784588132438523315)
                ·
                  refine ⟨2011424676882198657784973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340949784588132438523315 2011424676882198657784973)
                  ·
                    refine ⟨754284253830824496669365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011424676882198657784973 754284253830824496669365)
                    ·
                      rfl

theorem cell22_2203445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_2203445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203445 prefixEnd_2203445 := by exact prefixLift 2203445
  have htrace : WordTrace (prefixWord ++ tailWord_2203445) baseStart_2203445 baseEnd_2203445 := by
    simpa [prefixWord, tailWord_2203445, baseEnd_2203445] using wordTrace_append hprefix tailTrace_2203445
  have hstable : (prefixWord ++ tailWord_2203445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203445).length < 2 ^ (prefixWord ++ tailWord_2203445).sum := by decide
  have hdescent : baseEnd_2203445 < baseStart_2203445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203462 : List Nat := [6, 1, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2203462 : Nat := 118140960795 + 2203462 * 2 ^ 59
def prefixEnd_2203462 : Nat := 4983230072969 + 3 ^ 40 * 2203462 * 2
def baseEnd_2203462 : Nat := 754290073278242118994313

theorem tailTrace_2203462 : CollatzResearch.WordTrace tailWord_2203462 prefixEnd_2203462 754290073278242118994313 := by
  unfold tailWord_2203462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511464423226280318569895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53577907695493980129491093 2511464423226280318569895)
  ·
    refine ⟨3767196634839420477854843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2511464423226280318569895 3767196634839420477854843)
    ·
      refine ⟨5650794952259130716782265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3767196634839420477854843 5650794952259130716782265)
      ·
        refine ⟨4238096214194348037586699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5650794952259130716782265 4238096214194348037586699)
        ·
          refine ⟨6357144321291522056380049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238096214194348037586699 6357144321291522056380049)
          ·
            refine ⟨4767858240968641542285037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6357144321291522056380049 4767858240968641542285037)
            ·
              refine ⟨1787946840363240578356889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4767858240968641542285037 1787946840363240578356889)
              ·
                refine ⟨1340960130272430433767667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787946840363240578356889 1340960130272430433767667)
                ·
                  refine ⟨2011440195408645650651501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340960130272430433767667 2011440195408645650651501)
                  ·
                    refine ⟨754290073278242118994313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011440195408645650651501 754290073278242118994313)
                    ·
                      rfl

theorem cell22_2203462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2203462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203462 prefixEnd_2203462 := by exact prefixLift 2203462
  have htrace : WordTrace (prefixWord ++ tailWord_2203462) baseStart_2203462 baseEnd_2203462 := by
    simpa [prefixWord, tailWord_2203462, baseEnd_2203462] using wordTrace_append hprefix tailTrace_2203462
  have hstable : (prefixWord ++ tailWord_2203462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203462).length < 2 ^ (prefixWord ++ tailWord_2203462).sum := by decide
  have hdescent : baseEnd_2203462 < baseStart_2203462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203482 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_2203482 : Nat := 118140960795 + 2203482 * 2 ^ 59
def prefixEnd_2203482 : Nat := 4983230072969 + 3 ^ 40 * 2203482 * 2
def baseEnd_2203482 : Nat := 754296919686968733494251

theorem tailTrace_2203482 : CollatzResearch.WordTrace tailWord_2203482 prefixEnd_2203482 754296919686968733494251 := by
  unfold tailWord_2203482
  simp only [CollatzResearch.WordTrace]
  refine ⟨20091897750792128402491175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53578394002112342406643133 20091897750792128402491175)
  ·
    refine ⟨30137846626188192603736763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20091897750792128402491175 30137846626188192603736763)
    ·
      refine ⟨45206769939282288905605145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30137846626188192603736763 45206769939282288905605145)
      ·
        refine ⟨33905077454461716679203859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45206769939282288905605145 33905077454461716679203859)
        ·
          refine ⟨50857616181692575018805789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33905077454461716679203859 50857616181692575018805789)
          ·
            refine ⟨19071606068134715632052171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50857616181692575018805789 19071606068134715632052171)
            ·
              refine ⟨28607409102202073448078257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19071606068134715632052171 28607409102202073448078257)
              ·
                refine ⟨21455556826651555086058693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28607409102202073448078257 21455556826651555086058693)
                ·
                  refine ⟨4022916904997166578636005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21455556826651555086058693 4022916904997166578636005)
                  ·
                    refine ⟨754296919686968733494251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4022916904997166578636005 754296919686968733494251)
                    ·
                      rfl

theorem cell22_2203482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_2203482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203482 prefixEnd_2203482 := by exact prefixLift 2203482
  have htrace : WordTrace (prefixWord ++ tailWord_2203482) baseStart_2203482 baseEnd_2203482 := by
    simpa [prefixWord, tailWord_2203482, baseEnd_2203482] using wordTrace_append hprefix tailTrace_2203482
  have hstable : (prefixWord ++ tailWord_2203482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203482).length < 2 ^ (prefixWord ++ tailWord_2203482).sum := by decide
  have hdescent : baseEnd_2203482 < baseStart_2203482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203518 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2203518 : Nat := 118140960795 + 2203518 * 2 ^ 59
def prefixEnd_2203518 : Nat := 4983230072969 + 3 ^ 40 * 2203518 * 2
def baseEnd_2203518 : Nat := 754309243222676639594141

theorem tailTrace_2203518 : CollatzResearch.WordTrace tailWord_2203518 prefixEnd_2203518 754309243222676639594141 := by
  unfold tailWord_2203518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046113003879761469784401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53579269354025394505516805 10046113003879761469784401)
  ·
    refine ⟨7534584752909821102338301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10046113003879761469784401 7534584752909821102338301)
    ·
      refine ⟨2825469282341182913376863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7534584752909821102338301 2825469282341182913376863)
      ·
        refine ⟨4238203923511774370065295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2825469282341182913376863 4238203923511774370065295)
        ·
          refine ⟨6357305885267661555097943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238203923511774370065295 6357305885267661555097943)
          ·
            refine ⟨9535958827901492332646915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6357305885267661555097943 9535958827901492332646915)
            ·
              refine ⟨14303938241852238498970373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9535958827901492332646915 14303938241852238498970373)
              ·
                refine ⟨2681988420347294718556945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14303938241852238498970373 2681988420347294718556945)
                ·
                  refine ⟨2011491315260471038917709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2681988420347294718556945 2011491315260471038917709)
                  ·
                    refine ⟨754309243222676639594141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011491315260471038917709 754309243222676639594141)
                    ·
                      rfl

theorem cell22_2203518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2203518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203518 prefixEnd_2203518 := by exact prefixLift 2203518
  have htrace : WordTrace (prefixWord ++ tailWord_2203518) baseStart_2203518 baseEnd_2203518 := by
    simpa [prefixWord, tailWord_2203518, baseEnd_2203518] using wordTrace_append hprefix tailTrace_2203518
  have hstable : (prefixWord ++ tailWord_2203518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203518).length < 2 ^ (prefixWord ++ tailWord_2203518).sum := by decide
  have hdescent : baseEnd_2203518 < baseStart_2203518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203529 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 3, 3]
def baseStart_2203529 : Nat := 118140960795 + 2203529 * 2 ^ 59
def prefixEnd_2203529 : Nat := 4983230072969 + 3 ^ 40 * 2203529 * 2
def baseEnd_2203529 : Nat := 754313008747476277569107

theorem tailTrace_2203529 : CollatzResearch.WordTrace tailWord_2203529 prefixEnd_2203529 754313008747476277569107 := by
  unfold tailWord_2203529
  simp only [CollatzResearch.WordTrace]
  refine ⟨80369305233998240636925641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53579536822665493757950427 80369305233998240636925641)
  ·
    refine ⟨60276978925498680477694231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80369305233998240636925641 60276978925498680477694231)
    ·
      refine ⟨90415468388248020716541347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60276978925498680477694231 90415468388248020716541347)
      ·
        refine ⟨135623202582372031074812021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90415468388248020716541347 135623202582372031074812021)
        ·
          refine ⟨12714675242097377913263627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135623202582372031074812021 12714675242097377913263627)
          ·
            refine ⟨19072012863146066869895441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12714675242097377913263627 19072012863146066869895441)
            ·
              refine ⟨14304009647359550152421581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19072012863146066869895441 14304009647359550152421581)
              ·
                refine ⟨5364003617759831307158093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14304009647359550152421581 5364003617759831307158093)
                ·
                  refine ⟨2011501356659936740184285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5364003617759831307158093 2011501356659936740184285)
                  ·
                    refine ⟨754313008747476277569107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011501356659936740184285 754313008747476277569107)
                    ·
                      rfl

theorem cell22_2203529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_2203529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203529 prefixEnd_2203529 := by exact prefixLift 2203529
  have htrace : WordTrace (prefixWord ++ tailWord_2203529) baseStart_2203529 baseEnd_2203529 := by
    simpa [prefixWord, tailWord_2203529, baseEnd_2203529] using wordTrace_append hprefix tailTrace_2203529
  have hstable : (prefixWord ++ tailWord_2203529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203529).length < 2 ^ (prefixWord ++ tailWord_2203529).sum := by decide
  have hdescent : baseEnd_2203529 < baseStart_2203529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203546 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_2203546 : Nat := 118140960795 + 2203546 * 2 ^ 59
def prefixEnd_2203546 : Nat := 4983230072969 + 3 ^ 40 * 2203546 * 2
def baseEnd_2203546 : Nat := 754318828194893899894055

theorem tailTrace_2203546 : CollatzResearch.WordTrace tailWord_2203546 prefixEnd_2203546 754318828194893899894055 := by
  unfold tailWord_2203546
  simp only [CollatzResearch.WordTrace]
  refine ⟨20092481318734163135073623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53579950183291101693529661 20092481318734163135073623)
  ·
    refine ⟨30138721978101244702610435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20092481318734163135073623 30138721978101244702610435)
    ·
      refine ⟨45208082967151867053915653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30138721978101244702610435 45208082967151867053915653)
      ·
        refine ⟨8476515556340975072609185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45208082967151867053915653 8476515556340975072609185)
        ·
          refine ⟨6357386667255731304456889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8476515556340975072609185 6357386667255731304456889)
          ·
            refine ⟨4768040000441798478342667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6357386667255731304456889 4768040000441798478342667)
            ·
              refine ⟨7152060000662697717514001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768040000441798478342667 7152060000662697717514001)
              ·
                refine ⟨5364045000497023288135501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7152060000662697717514001 5364045000497023288135501)
                ·
                  refine ⟨2011516875186383733050813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5364045000497023288135501 2011516875186383733050813)
                  ·
                    refine ⟨754318828194893899894055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011516875186383733050813 754318828194893899894055)
                    ·
                      rfl

theorem cell22_2203546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_2203546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203546 prefixEnd_2203546 := by exact prefixLift 2203546
  have htrace : WordTrace (prefixWord ++ tailWord_2203546) baseStart_2203546 baseEnd_2203546 := by
    simpa [prefixWord, tailWord_2203546, baseEnd_2203546] using wordTrace_append hprefix tailTrace_2203546
  have hstable : (prefixWord ++ tailWord_2203546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203546).length < 2 ^ (prefixWord ++ tailWord_2203546).sum := by decide
  have hdescent : baseEnd_2203546 < baseStart_2203546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203550 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2203550 : Nat := 118140960795 + 2203550 * 2 ^ 59
def prefixEnd_2203550 : Nat := 4983230072969 + 3 ^ 40 * 2203550 * 2
def baseEnd_2203550 : Nat := 754320197476639222794043

theorem tailTrace_2203550 : CollatzResearch.WordTrace tailWord_2203550 prefixEnd_2203550 754320197476639222794043 := by
  unfold tailWord_2203550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046258895865270152930013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53580047444614774148960069 10046258895865270152930013)
  ·
    refine ⟨3767347085949476307348755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10046258895865270152930013 3767347085949476307348755)
    ·
      refine ⟨5651020628924214461023133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3767347085949476307348755 5651020628924214461023133)
      ·
        refine ⟨2119132735846580422883675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5651020628924214461023133 2119132735846580422883675)
        ·
          refine ⟨3178699103769870634325513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119132735846580422883675 3178699103769870634325513)
          ·
            refine ⟨2384024327827402975744135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3178699103769870634325513 2384024327827402975744135)
            ·
              refine ⟨3576036491741104463616203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384024327827402975744135 3576036491741104463616203)
              ·
                refine ⟨5364054737611656695424305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576036491741104463616203 5364054737611656695424305)
                ·
                  refine ⟨4023041053208742521568229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5364054737611656695424305 4023041053208742521568229)
                  ·
                    refine ⟨754320197476639222794043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4023041053208742521568229 754320197476639222794043)
                    ·
                      rfl

theorem cell22_2203550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2203550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203550 prefixEnd_2203550 := by exact prefixLift 2203550
  have htrace : WordTrace (prefixWord ++ tailWord_2203550) baseStart_2203550 baseEnd_2203550 := by
    simpa [prefixWord, tailWord_2203550, baseEnd_2203550] using wordTrace_append hprefix tailTrace_2203550
  have hstable : (prefixWord ++ tailWord_2203550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203550).length < 2 ^ (prefixWord ++ tailWord_2203550).sum := by decide
  have hdescent : baseEnd_2203550 < baseStart_2203550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203604 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 6]
def baseStart_2203604 : Nat := 118140960795 + 2203604 * 2 ^ 59
def prefixEnd_2203604 : Nat := 4983230072969 + 3 ^ 40 * 2203604 * 2
def baseEnd_2203604 : Nat := 251446227593400360647959

theorem tailTrace_2203604 : CollatzResearch.WordTrace tailWord_2203604 prefixEnd_2203604 251446227593400360647959 := by
  unfold tailWord_2203604
  simp only [CollatzResearch.WordTrace]
  refine ⟨40186020354363264222952933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53581360472484352297270577 40186020354363264222952933)
  ·
    refine ⟨7534878816443112041803675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40186020354363264222952933 7534878816443112041803675)
    ·
      refine ⟨11302318224664668062705513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7534878816443112041803675 11302318224664668062705513)
      ·
        refine ⟨8476738668498501047029135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11302318224664668062705513 8476738668498501047029135)
        ·
          refine ⟨12715108002747751570543703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8476738668498501047029135 12715108002747751570543703)
          ·
            refine ⟨19072662004121627355815555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12715108002747751570543703 19072662004121627355815555)
            ·
              refine ⟨28608993006182441033723333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19072662004121627355815555 28608993006182441033723333)
              ·
                refine ⟨5364186188659207693823125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28608993006182441033723333 5364186188659207693823125)
                ·
                  refine ⟨251446227593400360647959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5364186188659207693823125 251446227593400360647959)
                  ·
                    rfl

theorem cell22_2203604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_2203604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203604 prefixEnd_2203604 := by exact prefixLift 2203604
  have htrace : WordTrace (prefixWord ++ tailWord_2203604) baseStart_2203604 baseEnd_2203604 := by
    simpa [prefixWord, tailWord_2203604, baseEnd_2203604] using wordTrace_append hprefix tailTrace_2203604
  have hstable : (prefixWord ++ tailWord_2203604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203604).length < 2 ^ (prefixWord ++ tailWord_2203604).sum := by decide
  have hdescent : baseEnd_2203604 < baseStart_2203604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203632 : List Nat := [2, 1, 1, 1, 3, 2, 12]
def baseStart_2203632 : Nat := 118140960795 + 2203632 * 2 ^ 59
def prefixEnd_2203632 : Nat := 4983230072969 + 3 ^ 40 * 2203632 * 2
def baseEnd_2203632 : Nat := 27938824731571049712733

theorem tailTrace_2203632 : CollatzResearch.WordTrace tailWord_2203632 prefixEnd_2203632 27938824731571049712733 := by
  unfold tailWord_2203632
  simp only [CollatzResearch.WordTrace]
  refine ⟨40186530976312544613962575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53582041301750059485283433 40186530976312544613962575)
  ·
    refine ⟨60279796464468816920943863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40186530976312544613962575 60279796464468816920943863)
    ·
      refine ⟨90419694696703225381415795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60279796464468816920943863 90419694696703225381415795)
      ·
        refine ⟨135629542045054838072123693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90419694696703225381415795 135629542045054838072123693)
        ·
          refine ⟨50861078266895564277046385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135629542045054838072123693 50861078266895564277046385)
          ·
            refine ⟨38145808700171673207784789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50861078266895564277046385 38145808700171673207784789)
            ·
              refine ⟨27938824731571049712733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 38145808700171673207784789 27938824731571049712733)
              ·
                rfl

theorem cell22_2203632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 12].length) (baseStart_2203632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203632 prefixEnd_2203632 := by exact prefixLift 2203632
  have htrace : WordTrace (prefixWord ++ tailWord_2203632) baseStart_2203632 baseEnd_2203632 := by
    simpa [prefixWord, tailWord_2203632, baseEnd_2203632] using wordTrace_append hprefix tailTrace_2203632
  have hstable : (prefixWord ++ tailWord_2203632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203632).length < 2 ^ (prefixWord ++ tailWord_2203632).sum := by decide
  have hdescent : baseEnd_2203632 < baseStart_2203632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203638 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_2203638 : Nat := 118140960795 + 2203638 * 2 ^ 59
def prefixEnd_2203638 : Nat := 4983230072969 + 3 ^ 40 * 2203638 * 2
def baseEnd_2203638 : Nat := 251450107225012108864591

theorem tailTrace_2203638 : CollatzResearch.WordTrace tailWord_2203638 prefixEnd_2203638 251450107225012108864591 := by
  unfold tailWord_2203638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5023330049412709515790223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53582187193735568168429045 5023330049412709515790223)
  ·
    refine ⟨7534995074119064273685335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5023330049412709515790223 7534995074119064273685335)
    ·
      refine ⟨11302492611178596410528003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7534995074119064273685335 11302492611178596410528003)
      ·
        refine ⟨16953738916767894615792005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11302492611178596410528003 16953738916767894615792005)
        ·
          refine ⟨3178826046893980240461001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16953738916767894615792005 3178826046893980240461001)
          ·
            refine ⟨2384119535170485180345751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3178826046893980240461001 2384119535170485180345751)
            ·
              refine ⟨3576179302755727770518627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384119535170485180345751 3576179302755727770518627)
              ·
                refine ⟨5364268954133591655777941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576179302755727770518627 5364268954133591655777941)
                ·
                  refine ⟨251450107225012108864591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5364268954133591655777941 251450107225012108864591)
                  ·
                    rfl

theorem cell22_2203638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_2203638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203638 prefixEnd_2203638 := by exact prefixLift 2203638
  have htrace : WordTrace (prefixWord ++ tailWord_2203638) baseStart_2203638 baseEnd_2203638 := by
    simpa [prefixWord, tailWord_2203638, baseEnd_2203638] using wordTrace_append hprefix tailTrace_2203638
  have hstable : (prefixWord ++ tailWord_2203638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203638).length < 2 ^ (prefixWord ++ tailWord_2203638).sum := by decide
  have hdescent : baseEnd_2203638 < baseStart_2203638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203649 : List Nat := [1, 2, 4, 1, 2, 1, 4, 7]
def baseStart_2203649 : Nat := 118140960795 + 2203649 * 2 ^ 59
def prefixEnd_2203649 : Nat := 4983230072969 + 3 ^ 40 * 2203649 * 2
def baseEnd_2203649 : Nat := 83817120799981773840971

theorem tailTrace_2203649 : CollatzResearch.WordTrace tailWord_2203649 prefixEnd_2203649 83817120799981773840971 := by
  unfold tailWord_2203649
  simp only [CollatzResearch.WordTrace]
  refine ⟨80373681993563501131294001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53582454662375667420862667 80373681993563501131294001)
  ·
    refine ⟨60280261495172625848470501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80373681993563501131294001 60280261495172625848470501)
    ·
      refine ⟨11302549030344867346588219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60280261495172625848470501 11302549030344867346588219)
      ·
        refine ⟨16953823545517301019882329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11302549030344867346588219 16953823545517301019882329)
        ·
          refine ⟨12715367659137975764911747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16953823545517301019882329 12715367659137975764911747)
          ·
            refine ⟨19073051488706963647367621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12715367659137975764911747 19073051488706963647367621)
            ·
              refine ⟨3576197154132555683881429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19073051488706963647367621 3576197154132555683881429)
              ·
                refine ⟨83817120799981773840971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3576197154132555683881429 83817120799981773840971)
                ·
                  rfl

theorem cell22_2203649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 7].length) (baseStart_2203649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203649 prefixEnd_2203649 := by exact prefixLift 2203649
  have htrace : WordTrace (prefixWord ++ tailWord_2203649) baseStart_2203649 baseEnd_2203649 := by
    simpa [prefixWord, tailWord_2203649, baseEnd_2203649] using wordTrace_append hprefix tailTrace_2203649
  have hstable : (prefixWord ++ tailWord_2203649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203649).length < 2 ^ (prefixWord ++ tailWord_2203649).sum := by decide
  have hdescent : baseEnd_2203649 < baseStart_2203649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203653 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_2203653 : Nat := 118140960795 + 2203653 * 2 ^ 59
def prefixEnd_2203653 : Nat := 4983230072969 + 3 ^ 40 * 2203653 * 2
def baseEnd_2203653 : Nat := 754355456481581287468727

theorem tailTrace_2203653 : CollatzResearch.WordTrace tailWord_2203653 prefixEnd_2203653 754355456481581287468727 := by
  unfold tailWord_2203653
  simp only [CollatzResearch.WordTrace]
  refine ⟨80373827885549009814439613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53582551923699339876293075 80373827885549009814439613)
  ·
    refine ⟨30140185457080878680414855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80373827885549009814439613 30140185457080878680414855)
    ·
      refine ⟨45210278185621318020622283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30140185457080878680414855 45210278185621318020622283)
      ·
        refine ⟨67815417278431977030933425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45210278185621318020622283 67815417278431977030933425)
        ·
          refine ⟨50861562958823982773200069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67815417278431977030933425 50861562958823982773200069)
          ·
            refine ⟨9536543054779496769975013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50861562958823982773200069 9536543054779496769975013)
            ·
              refine ⟨1788101822771155644370315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9536543054779496769975013 1788101822771155644370315)
              ·
                refine ⟨2682152734156733466555473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788101822771155644370315 2682152734156733466555473)
                ·
                  refine ⟨2011614550617550099916605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682152734156733466555473 2011614550617550099916605)
                  ·
                    refine ⟨754355456481581287468727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011614550617550099916605 754355456481581287468727)
                    ·
                      rfl

theorem cell22_2203653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_2203653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203653 prefixEnd_2203653 := by exact prefixLift 2203653
  have htrace : WordTrace (prefixWord ++ tailWord_2203653) baseStart_2203653 baseEnd_2203653 := by
    simpa [prefixWord, tailWord_2203653, baseEnd_2203653] using wordTrace_append hprefix tailTrace_2203653
  have hstable : (prefixWord ++ tailWord_2203653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203653).length < 2 ^ (prefixWord ++ tailWord_2203653).sum := by decide
  have hdescent : baseEnd_2203653 < baseStart_2203653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203700 : List Nat := [2, 5, 1, 2, 3, 1, 1, 7]
def baseStart_2203700 : Nat := 118140960795 + 2203700 * 2 ^ 59
def prefixEnd_2203700 : Nat := 4983230072969 + 3 ^ 40 * 2203700 * 2
def baseEnd_2203700 : Nat := 83819060615787647949287

theorem tailTrace_2203700 : CollatzResearch.WordTrace tailWord_2203700 prefixEnd_2203700 83819060615787647949287 := by
  unfold tailWord_2203700
  simp only [CollatzResearch.WordTrace]
  refine ⟨40187771058189368420700277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53583694744252491227600369 40187771058189368420700277)
  ·
    refine ⟨3767603536705253289440651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40187771058189368420700277 3767603536705253289440651)
    ·
      refine ⟨5651405305057879934160977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3767603536705253289440651 5651405305057879934160977)
      ·
        refine ⟨4238553978793409950620733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5651405305057879934160977 4238553978793409950620733)
        ·
          refine ⟨1589457742047528731482775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4238553978793409950620733 1589457742047528731482775)
          ·
            refine ⟨2384186613071293097224163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589457742047528731482775 2384186613071293097224163)
            ·
              refine ⟨3576279919606939645836245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384186613071293097224163 3576279919606939645836245)
              ·
                refine ⟨83819060615787647949287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3576279919606939645836245 83819060615787647949287)
                ·
                  rfl

theorem cell22_2203700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 7].length) (baseStart_2203700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203700 prefixEnd_2203700 := by exact prefixLift 2203700
  have htrace : WordTrace (prefixWord ++ tailWord_2203700) baseStart_2203700 baseEnd_2203700 := by
    simpa [prefixWord, tailWord_2203700, baseEnd_2203700] using wordTrace_append hprefix tailTrace_2203700
  have hstable : (prefixWord ++ tailWord_2203700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203700).length < 2 ^ (prefixWord ++ tailWord_2203700).sum := by decide
  have hdescent : baseEnd_2203700 < baseStart_2203700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203756 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 6]
def baseStart_2203756 : Nat := 118140960795 + 2203756 * 2 ^ 59
def prefixEnd_2203756 : Nat := 4983230072969 + 3 ^ 40 * 2203756 * 2
def baseEnd_2203756 : Nat := 251463571828841117381137

theorem tailTrace_2203756 : CollatzResearch.WordTrace tailWord_2203756 prefixEnd_2203756 251463571828841117381137 := by
  unfold tailWord_2203756
  simp only [CollatzResearch.WordTrace]
  refine ⟨40188792302087929202719561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53585056402783905603626081 40188792302087929202719561)
  ·
    refine ⟨30141594226565946902039671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40188792302087929202719561 30141594226565946902039671)
    ·
      refine ⟨45212391339848920353059507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30141594226565946902039671 45212391339848920353059507)
      ·
        refine ⟨67818587009773380529589261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45212391339848920353059507 67818587009773380529589261)
        ·
          refine ⟨25431970128665017698595973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67818587009773380529589261 25431970128665017698595973)
          ·
            refine ⟨4768494399124690818486745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25431970128665017698595973 4768494399124690818486745)
            ·
              refine ⟨3576370799343518113865059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4768494399124690818486745 3576370799343518113865059)
              ·
                refine ⟨5364556199015277170797589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576370799343518113865059 5364556199015277170797589)
                ·
                  refine ⟨251463571828841117381137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5364556199015277170797589 251463571828841117381137)
                  ·
                    rfl

theorem cell22_2203756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_2203756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203756 prefixEnd_2203756 := by exact prefixLift 2203756
  have htrace : WordTrace (prefixWord ++ tailWord_2203756) baseStart_2203756 baseEnd_2203756 := by
    simpa [prefixWord, tailWord_2203756, baseEnd_2203756] using wordTrace_append hprefix tailTrace_2203756
  have hstable : (prefixWord ++ tailWord_2203756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203756).length < 2 ^ (prefixWord ++ tailWord_2203756).sum := by decide
  have hdescent : baseEnd_2203756 < baseStart_2203756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203786 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_2203786 : Nat := 118140960795 + 2203786 * 2 ^ 59
def prefixEnd_2203786 : Nat := 4983230072969 + 3 ^ 40 * 2203786 * 2
def baseEnd_2203786 : Nat := 754400985099613273893319

theorem tailTrace_2203786 : CollatzResearch.WordTrace tailWord_2203786 prefixEnd_2203786 754400985099613273893319 := by
  unfold tailWord_2203786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20094669698516793382257803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53585785862711449019354141 20094669698516793382257803)
  ·
    refine ⟨30142004547775190073386705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20094669698516793382257803 30142004547775190073386705)
    ·
      refine ⟨22606503410831392555040029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30142004547775190073386705 22606503410831392555040029)
      ·
        refine ⟨8477438779061772208140011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22606503410831392555040029 8477438779061772208140011)
        ·
          refine ⟨12716158168592658312210017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8477438779061772208140011 12716158168592658312210017)
          ·
            refine ⟨9537118626444493734157513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12716158168592658312210017 9537118626444493734157513)
            ·
              refine ⟨7152838969833370300618135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9537118626444493734157513 7152838969833370300618135)
              ·
                refine ⟨10729258454750055450927203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7152838969833370300618135 10729258454750055450927203)
                ·
                  refine ⟨16093887682125083176390805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10729258454750055450927203 16093887682125083176390805)
                  ·
                    refine ⟨754400985099613273893319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16093887682125083176390805 754400985099613273893319)
                    ·
                      rfl

theorem cell22_2203786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_2203786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203786 prefixEnd_2203786 := by exact prefixLift 2203786
  have htrace : WordTrace (prefixWord ++ tailWord_2203786) baseStart_2203786 baseEnd_2203786 := by
    simpa [prefixWord, tailWord_2203786, baseEnd_2203786] using wordTrace_append hprefix tailTrace_2203786
  have hstable : (prefixWord ++ tailWord_2203786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203786).length < 2 ^ (prefixWord ++ tailWord_2203786).sum := by decide
  have hdescent : baseEnd_2203786 < baseStart_2203786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203850 : List Nat := [3, 1, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_2203850 : Nat := 118140960795 + 2203850 * 2 ^ 59
def prefixEnd_2203850 : Nat := 4983230072969 + 3 ^ 40 * 2203850 * 2
def baseEnd_2203850 : Nat := 754422893607538440293123

theorem tailTrace_2203850 : CollatzResearch.WordTrace tailWord_2203850 prefixEnd_2203850 754422893607538440293123 := by
  unfold tailWord_2203850
  simp only [CollatzResearch.WordTrace]
  refine ⟨20095253266458828114840251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53587342043890208306240669 20095253266458828114840251)
  ·
    refine ⟨30142879899688242172260377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20095253266458828114840251 30142879899688242172260377)
    ·
      refine ⟨22607159924766181629195283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30142879899688242172260377 22607159924766181629195283)
      ·
        refine ⟨33910739887149272443792925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22607159924766181629195283 33910739887149272443792925)
        ·
          refine ⟨12716527457680977166422347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33910739887149272443792925 12716527457680977166422347)
          ·
            refine ⟨19074791186521465749633521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12716527457680977166422347 19074791186521465749633521)
            ·
              refine ⟨14306093389891099312225141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19074791186521465749633521 14306093389891099312225141)
              ·
                refine ⟨1341196255302290560521107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14306093389891099312225141 1341196255302290560521107)
                ·
                  refine ⟨2011794382953435840781661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341196255302290560521107 2011794382953435840781661)
                  ·
                    refine ⟨754422893607538440293123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011794382953435840781661 754422893607538440293123)
                    ·
                      rfl

theorem cell22_2203850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_2203850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203850 prefixEnd_2203850 := by exact prefixLift 2203850
  have htrace : WordTrace (prefixWord ++ tailWord_2203850) baseStart_2203850 baseEnd_2203850 := by
    simpa [prefixWord, tailWord_2203850, baseEnd_2203850] using wordTrace_append hprefix tailTrace_2203850
  have hstable : (prefixWord ++ tailWord_2203850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203850).length < 2 ^ (prefixWord ++ tailWord_2203850).sum := by decide
  have hdescent : baseEnd_2203850 < baseStart_2203850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203891 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 6]
def baseStart_2203891 : Nat := 118140960795 + 2203891 * 2 ^ 59
def prefixEnd_2203891 : Nat := 4983230072969 + 3 ^ 40 * 2203891 * 2
def baseEnd_2203891 : Nat := 251478976248476000005999

theorem tailTrace_2203891 : CollatzResearch.WordTrace tailWord_2203891 prefixEnd_2203891 251478976248476000005999 := by
  unfold tailWord_2203891
  simp only [CollatzResearch.WordTrace]
  refine ⟨80382508458686776461603527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53588338972457850974402351 80382508458686776461603527)
  ·
    refine ⟨120573762688030164692405291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80382508458686776461603527 120573762688030164692405291)
    ·
      refine ⟨180860644032045247038607937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120573762688030164692405291 180860644032045247038607937)
      ·
        refine ⟨135645483024033935278955953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180860644032045247038607937 135645483024033935278955953)
        ·
          refine ⟨101734112268025451459216965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135645483024033935278955953 101734112268025451459216965)
          ·
            refine ⟨19075146050254772148603181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101734112268025451459216965 19075146050254772148603181)
            ·
              refine ⟨7153179768845539555726193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19075146050254772148603181 7153179768845539555726193)
              ·
                refine ⟨5364884826634154666794645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7153179768845539555726193 5364884826634154666794645)
                ·
                  refine ⟨251478976248476000005999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5364884826634154666794645 251478976248476000005999)
                  ·
                    rfl

theorem cell22_2203891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 6].length) (baseStart_2203891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203891 prefixEnd_2203891 := by exact prefixLift 2203891
  have htrace : WordTrace (prefixWord ++ tailWord_2203891) baseStart_2203891 baseEnd_2203891 := by
    simpa [prefixWord, tailWord_2203891, baseEnd_2203891] using wordTrace_append hprefix tailTrace_2203891
  have hstable : (prefixWord ++ tailWord_2203891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203891).length < 2 ^ (prefixWord ++ tailWord_2203891).sum := by decide
  have hdescent : baseEnd_2203891 < baseStart_2203891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203938 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2203938 : Nat := 118140960795 + 2203938 * 2 ^ 59
def prefixEnd_2203938 : Nat := 4983230072969 + 3 ^ 40 * 2203938 * 2
def baseEnd_2203938 : Nat := 754453017805935544092853

theorem tailTrace_2203938 : CollatzResearch.WordTrace tailWord_2203938 prefixEnd_2203938 754453017805935544092853 := by
  unfold tailWord_2203938
  simp only [CollatzResearch.WordTrace]
  refine ⟨20096055672379125872141117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53589481793011002325709645 20096055672379125872141117)
  ·
    refine ⟨7536020877142172202052919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20096055672379125872141117 7536020877142172202052919)
    ·
      refine ⟨11304031315713258303079379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7536020877142172202052919 11304031315713258303079379)
      ·
        refine ⟨16956046973569887454619069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11304031315713258303079379 16956046973569887454619069)
        ·
          refine ⟨6358517615088707795482151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16956046973569887454619069 6358517615088707795482151)
          ·
            refine ⟨9537776422633061693223227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358517615088707795482151 9537776422633061693223227)
            ·
              refine ⟨14306664633949592539834841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537776422633061693223227 14306664633949592539834841)
              ·
                refine ⟨10729998475462194404876131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14306664633949592539834841 10729998475462194404876131)
                ·
                  refine ⟨16094997713193291607314197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10729998475462194404876131 16094997713193291607314197)
                  ·
                    refine ⟨754453017805935544092853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16094997713193291607314197 754453017805935544092853)
                    ·
                      rfl

theorem cell22_2203938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2203938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203938 prefixEnd_2203938 := by exact prefixLift 2203938
  have htrace : WordTrace (prefixWord ++ tailWord_2203938) baseStart_2203938 baseEnd_2203938 := by
    simpa [prefixWord, tailWord_2203938, baseEnd_2203938] using wordTrace_append hprefix tailTrace_2203938
  have hstable : (prefixWord ++ tailWord_2203938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203938).length < 2 ^ (prefixWord ++ tailWord_2203938).sum := by decide
  have hdescent : baseEnd_2203938 < baseStart_2203938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203940 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_2203940 : Nat := 118140960795 + 2203940 * 2 ^ 59
def prefixEnd_2203940 : Nat := 4983230072969 + 3 ^ 40 * 2203940 * 2
def baseEnd_2203940 : Nat := 754453702446808205542847

theorem tailTrace_2203940 : CollatzResearch.WordTrace tailWord_2203940 prefixEnd_2203940 754453702446808205542847 := by
  unfold tailWord_2203940
  simp only [CollatzResearch.WordTrace]
  refine ⟨40192147817754628915068637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53589530423672838553424849 40192147817754628915068637)
  ·
    refine ⟨15072055431657985843150739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40192147817754628915068637 15072055431657985843150739)
    ·
      refine ⟨22608083147486978764726109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15072055431657985843150739 22608083147486978764726109)
      ·
        refine ⟨8478031180307617036772291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22608083147486978764726109 8478031180307617036772291)
        ·
          refine ⟨12717046770461425555158437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8478031180307617036772291 12717046770461425555158437)
          ·
            refine ⟨2384446269461517291592207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12717046770461425555158437 2384446269461517291592207)
            ·
              refine ⟨3576669404192275937388311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384446269461517291592207 3576669404192275937388311)
              ·
                refine ⟨5365004106288413906082467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576669404192275937388311 5365004106288413906082467)
                ·
                  refine ⟨8047506159432620859123701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5365004106288413906082467 8047506159432620859123701)
                  ·
                    refine ⟨754453702446808205542847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8047506159432620859123701 754453702446808205542847)
                    ·
                      rfl

theorem cell22_2203940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_2203940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203940 prefixEnd_2203940 := by exact prefixLift 2203940
  have htrace : WordTrace (prefixWord ++ tailWord_2203940) baseStart_2203940 baseEnd_2203940 := by
    simpa [prefixWord, tailWord_2203940, baseEnd_2203940] using wordTrace_append hprefix tailTrace_2203940
  have hstable : (prefixWord ++ tailWord_2203940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203940).length < 2 ^ (prefixWord ++ tailWord_2203940).sum := by decide
  have hdescent : baseEnd_2203940 < baseStart_2203940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203953 : List Nat := [1, 2, 2, 3, 4, 1, 1, 8]
def baseStart_2203953 : Nat := 118140960795 + 2203953 * 2 ^ 59
def prefixEnd_2203953 : Nat := 4983230072969 + 3 ^ 40 * 2203953 * 2
def baseEnd_2203953 : Nat := 83828683623608944996423

theorem tailTrace_2203953 : CollatzResearch.WordTrace tailWord_2203953 prefixEnd_2203953 83828683623608944996423 := by
  unfold tailWord_2203953
  simp only [CollatzResearch.WordTrace]
  refine ⟨80384769784462161050360513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53589846522974774033573675 80384769784462161050360513)
  ·
    refine ⟨60288577338346620787770385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80384769784462161050360513 60288577338346620787770385)
    ·
      refine ⟨45216433003759965590827789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60288577338346620787770385 45216433003759965590827789)
      ·
        refine ⟨16956162376409987096560421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45216433003759965590827789 16956162376409987096560421)
        ·
          refine ⟨3179280445576872580605079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16956162376409987096560421 3179280445576872580605079)
          ·
            refine ⟨4768920668365308870907619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179280445576872580605079 4768920668365308870907619)
            ·
              refine ⟨7153381002547963306361429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768920668365308870907619 7153381002547963306361429)
              ·
                refine ⟨83828683623608944996423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7153381002547963306361429 83828683623608944996423)
                ·
                  rfl

theorem cell22_2203953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 8].length) (baseStart_2203953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203953 prefixEnd_2203953 := by exact prefixLift 2203953
  have htrace : WordTrace (prefixWord ++ tailWord_2203953) baseStart_2203953 baseEnd_2203953 := by
    simpa [prefixWord, tailWord_2203953, baseEnd_2203953] using wordTrace_append hprefix tailTrace_2203953
  have hstable : (prefixWord ++ tailWord_2203953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203953).length < 2 ^ (prefixWord ++ tailWord_2203953).sum := by decide
  have hdescent : baseEnd_2203953 < baseStart_2203953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203972 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2203972 : Nat := 118140960795 + 2203972 * 2 ^ 59
def prefixEnd_2203972 : Nat := 4983230072969 + 3 ^ 40 * 2203972 * 2
def baseEnd_2203972 : Nat := 754464656700770788742749

theorem tailTrace_2203972 : CollatzResearch.WordTrace tailWord_2203972 prefixEnd_2203972 754464656700770788742749 := by
  unfold tailWord_2203972
  simp only [CollatzResearch.WordTrace]
  refine ⟨40192731385696663647651085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53590308514262218196868113 40192731385696663647651085)
  ·
    refine ⟨15072274269636248867869157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40192731385696663647651085 15072274269636248867869157)
    ·
      refine ⟨2826051425556796662725467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15072274269636248867869157 2826051425556796662725467)
      ·
        refine ⟨4239077138335194994088201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2826051425556796662725467 4239077138335194994088201)
        ·
          refine ⟨3179307853751396245566151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4239077138335194994088201 3179307853751396245566151)
          ·
            refine ⟨4768961780627094368349227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179307853751396245566151 4768961780627094368349227)
            ·
              refine ⟨7153442670940641552523841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768961780627094368349227 7153442670940641552523841)
              ·
                refine ⟨5365082003205481164392881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7153442670940641552523841 5365082003205481164392881)
                ·
                  refine ⟨4023811502404110873294661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5365082003205481164392881 4023811502404110873294661)
                  ·
                    refine ⟨754464656700770788742749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4023811502404110873294661 754464656700770788742749)
                    ·
                      rfl

theorem cell22_2203972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2203972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203972 prefixEnd_2203972 := by exact prefixLift 2203972
  have htrace : WordTrace (prefixWord ++ tailWord_2203972) baseStart_2203972 baseEnd_2203972 := by
    simpa [prefixWord, tailWord_2203972, baseEnd_2203972] using wordTrace_append hprefix tailTrace_2203972
  have hstable : (prefixWord ++ tailWord_2203972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203972).length < 2 ^ (prefixWord ++ tailWord_2203972).sum := by decide
  have hdescent : baseEnd_2203972 < baseStart_2203972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203985 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 3, 3]
def baseStart_2203985 : Nat := 118140960795 + 2203985 * 2 ^ 59
def prefixEnd_2203985 : Nat := 4983230072969 + 3 ^ 40 * 2203985 * 2
def baseEnd_2203985 : Nat := 754469106866443088167709

theorem tailTrace_2203985 : CollatzResearch.WordTrace tailWord_2203985 prefixEnd_2203985 754469106866443088167709 := by
  unfold tailWord_2203985
  simp only [CollatzResearch.WordTrace]
  refine ⟨80385936920346230515525409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53590624613564153677016939 80385936920346230515525409)
  ·
    refine ⟨60289452690259672886644057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80385936920346230515525409 60289452690259672886644057)
    ·
      refine ⟨45217089517694754664983043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60289452690259672886644057 45217089517694754664983043)
      ·
        refine ⟨67825634276542131997474565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45217089517694754664983043 67825634276542131997474565)
        ·
          refine ⟨12717306426851649749526481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67825634276542131997474565 12717306426851649749526481)
          ·
            refine ⟨9537979820138737312144861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12717306426851649749526481 9537979820138737312144861)
            ·
              refine ⟨3576742432552026492054323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9537979820138737312144861 3576742432552026492054323)
              ·
                refine ⟨5365113648828039738081485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576742432552026492054323 5365113648828039738081485)
                ·
                  refine ⟨2011917618310514901780557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5365113648828039738081485 2011917618310514901780557)
                  ·
                    refine ⟨754469106866443088167709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011917618310514901780557 754469106866443088167709)
                    ·
                      rfl

theorem cell22_2203985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_2203985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2203985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2203985 prefixEnd_2203985 := by exact prefixLift 2203985
  have htrace : WordTrace (prefixWord ++ tailWord_2203985) baseStart_2203985 baseEnd_2203985 := by
    simpa [prefixWord, tailWord_2203985, baseEnd_2203985] using wordTrace_append hprefix tailTrace_2203985
  have hstable : (prefixWord ++ tailWord_2203985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203985).length < 2 ^ (prefixWord ++ tailWord_2203985).sum := by decide
  have hdescent : baseEnd_2203985 < baseStart_2203985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204011 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 8]
def baseStart_2204011 : Nat := 118140960795 + 2204011 * 2 ^ 59
def prefixEnd_2204011 : Nat := 4983230072969 + 3 ^ 40 * 2204011 * 2
def baseEnd_2204011 : Nat := 754478007197787687017629

theorem tailTrace_2204011 : CollatzResearch.WordTrace tailWord_2204011 prefixEnd_2204011 754478007197787687017629 := by
  unfold tailWord_2204011
  simp only [CollatzResearch.WordTrace]
  refine ⟨80386885218252036955971887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53591256812168024637314591 80386885218252036955971887)
  ·
    refine ⟨120580327827378055433957831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80386885218252036955971887 120580327827378055433957831)
    ·
      refine ⟨180870491741067083150936747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120580327827378055433957831 180870491741067083150936747)
      ·
        refine ⟨271305737611600624726405121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180870491741067083150936747 271305737611600624726405121)
        ·
          refine ⟨203479303208700468544803841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271305737611600624726405121 203479303208700468544803841)
          ·
            refine ⟨152609477406525351408602881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203479303208700468544803841 152609477406525351408602881)
            ·
              refine ⟨114457108054894013556452161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152609477406525351408602881 114457108054894013556452161)
              ·
                refine ⟨85842831041170510167339121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114457108054894013556452161 85842831041170510167339121)
                ·
                  refine ⟨64382123280877882625504341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85842831041170510167339121 64382123280877882625504341)
                  ·
                    refine ⟨754478007197787687017629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64382123280877882625504341 754478007197787687017629)
                    ·
                      rfl

theorem cell22_2204011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_2204011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204011 prefixEnd_2204011 := by exact prefixLift 2204011
  have htrace : WordTrace (prefixWord ++ tailWord_2204011) baseStart_2204011 baseEnd_2204011 := by
    simpa [prefixWord, tailWord_2204011, baseEnd_2204011] using wordTrace_append hprefix tailTrace_2204011
  have hstable : (prefixWord ++ tailWord_2204011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204011).length < 2 ^ (prefixWord ++ tailWord_2204011).sum := by decide
  have hdescent : baseEnd_2204011 < baseStart_2204011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204062 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2204062 : Nat := 118140960795 + 2204062 * 2 ^ 59
def prefixEnd_2204062 : Nat := 4983230072969 + 3 ^ 40 * 2204062 * 2
def baseEnd_2204062 : Nat := 754495465540040553992473

theorem tailTrace_2204062 : CollatzResearch.WordTrace tailWord_2204062 prefixEnd_2204062 754495465540040553992473 := by
  unfold tailWord_2204062
  simp only [CollatzResearch.WordTrace]
  refine ⟨10048593167633409083259805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53592496894044848444052293 10048593167633409083259805)
  ·
    refine ⟨3768222437862528406222427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10048593167633409083259805 3768222437862528406222427)
    ·
      refine ⟨5652333656793792609333641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3768222437862528406222427 5652333656793792609333641)
      ·
        refine ⟨4239250242595344457000231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5652333656793792609333641 4239250242595344457000231)
        ·
          refine ⟨6358875363893016685500347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239250242595344457000231 6358875363893016685500347)
          ·
            refine ⟨9538313045839525028250521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358875363893016685500347 9538313045839525028250521)
            ·
              refine ⟨7153734784379643771187891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9538313045839525028250521 7153734784379643771187891)
              ·
                refine ⟨10730602176569465656781837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7153734784379643771187891 10730602176569465656781837)
                ·
                  refine ⟨4023975816213549621293189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10730602176569465656781837 4023975816213549621293189)
                  ·
                    refine ⟨754495465540040553992473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4023975816213549621293189 754495465540040553992473)
                    ·
                      rfl

theorem cell22_2204062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2204062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204062 prefixEnd_2204062 := by exact prefixLift 2204062
  have htrace : WordTrace (prefixWord ++ tailWord_2204062) baseStart_2204062 baseEnd_2204062 := by
    simpa [prefixWord, tailWord_2204062, baseEnd_2204062] using wordTrace_append hprefix tailTrace_2204062
  have hstable : (prefixWord ++ tailWord_2204062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204062).length < 2 ^ (prefixWord ++ tailWord_2204062).sum := by decide
  have hdescent : baseEnd_2204062 < baseStart_2204062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
