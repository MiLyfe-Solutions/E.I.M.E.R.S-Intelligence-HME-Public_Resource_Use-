import V185TrunkScan23Chunk1275

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7559973 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 2, 4, 2]
def baseStart_7559973 : Nat := 118140960795 + 7559973 * 2 ^ 59
def prefixEnd_7559973 : Nat := 4983230072969 + 3 ^ 40 * 7559973 * 2
def baseEnd_7559973 : Nat := 3881899884012855304569823

theorem tailTrace_7559973 : CollatzResearch.WordTrace tailWord_7559973 prefixEnd_7559973 3881899884012855304569823 := by
  unfold tailWord_7559973
  simp only [CollatzResearch.WordTrace]
  refine ⟨275734867840516436440556573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183823245227010957627037715 275734867840516436440556573)
  ·
    refine ⟨103400575440193663665208715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275734867840516436440556573 103400575440193663665208715)
    ·
      refine ⟨155100863160290495497813073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103400575440193663665208715 155100863160290495497813073)
      ·
        refine ⟨116325647370217871623359805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155100863160290495497813073 116325647370217871623359805)
        ·
          refine ⟨43622117763831701858759927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116325647370217871623359805 43622117763831701858759927)
          ·
            refine ⟨65433176645747552788139891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43622117763831701858759927 65433176645747552788139891)
            ·
              refine ⟨98149764968621329182209837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65433176645747552788139891 98149764968621329182209837)
              ·
                refine ⟨36806161863232998443328689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98149764968621329182209837 36806161863232998443328689)
                ·
                  refine ⟨27604621397424748832496517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36806161863232998443328689 27604621397424748832496517)
                  ·
                    refine ⟨5175866512017140406093097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27604621397424748832496517 5175866512017140406093097)
                    ·
                      refine ⟨3881899884012855304569823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175866512017140406093097 3881899884012855304569823)
                      ·
                        rfl

theorem cell23_7559973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_7559973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559973 prefixEnd_7559973 := by exact prefixLift 7559973
  have htrace : WordTrace (prefixWord ++ tailWord_7559973) baseStart_7559973 baseEnd_7559973 := by
    simpa [prefixWord, tailWord_7559973, baseEnd_7559973] using wordTrace_append hprefix tailTrace_7559973
  have hstable : (prefixWord ++ tailWord_7559973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559973).length < 2 ^ (prefixWord ++ tailWord_7559973).sum := by decide
  have hdescent : baseEnd_7559973 < baseStart_7559973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559979 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 10]
def baseStart_7559979 : Nat := 118140960795 + 7559979 * 2 ^ 59
def prefixEnd_7559979 : Nat := 4983230072969 + 3 ^ 40 * 7559979 * 2
def baseEnd_7559979 : Nat := 431322551655198031232755

theorem tailTrace_7559979 : CollatzResearch.WordTrace tailWord_7559979 prefixEnd_7559979 431322551655198031232755 := by
  unfold tailWord_7559979
  simp only [CollatzResearch.WordTrace]
  refine ⟨275735086678494699465274991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183823391118996466310183327 275735086678494699465274991)
  ·
    refine ⟨413602630017742049197912487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275735086678494699465274991 413602630017742049197912487)
    ·
      refine ⟨620403945026613073796868731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413602630017742049197912487 620403945026613073796868731)
      ·
        refine ⟨930605917539919610695303097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620403945026613073796868731 930605917539919610695303097)
        ·
          refine ⟨697954438154939708021477323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930605917539919610695303097 697954438154939708021477323)
          ·
            refine ⟨1046931657232409562032215985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697954438154939708021477323 1046931657232409562032215985)
            ·
              refine ⟨785198742924307171524161989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046931657232409562032215985 785198742924307171524161989)
              ·
                refine ⟨147224764298307594660780373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785198742924307171524161989 147224764298307594660780373)
                ·
                  refine ⟨431322551655198031232755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 147224764298307594660780373 431322551655198031232755)
                  ·
                    rfl

theorem cell23_7559979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 10].length) (baseStart_7559979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559979 prefixEnd_7559979 := by exact prefixLift 7559979
  have htrace : WordTrace (prefixWord ++ tailWord_7559979) baseStart_7559979 baseEnd_7559979 := by
    simpa [prefixWord, tailWord_7559979, baseEnd_7559979] using wordTrace_append hprefix tailTrace_7559979
  have hstable : (prefixWord ++ tailWord_7559979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559979).length < 2 ^ (prefixWord ++ tailWord_7559979).sum := by decide
  have hdescent : baseEnd_7559979 < baseStart_7559979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559986 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_7559986 : Nat := 118140960795 + 7559986 * 2 ^ 59
def prefixEnd_7559986 : Nat := 4983230072969 + 3 ^ 40 * 7559986 * 2
def baseEnd_7559986 : Nat := 3881906559261363753707263

theorem tailTrace_7559986 : CollatzResearch.WordTrace tailWord_7559986 prefixEnd_7559986 3881906559261363753707263 := by
  unfold tailWord_7559986
  simp only [CollatzResearch.WordTrace]
  refine ⟨68933835497367334915194953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183823561326312893107186541 68933835497367334915194953)
  ·
    refine ⟨51700376623025501186396215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68933835497367334915194953 51700376623025501186396215)
    ·
      refine ⟨77550564934538251779594323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51700376623025501186396215 77550564934538251779594323)
      ·
        refine ⟨116325847401807377669391485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77550564934538251779594323 116325847401807377669391485)
        ·
          refine ⟨43622192775677766626021807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116325847401807377669391485 43622192775677766626021807)
          ·
            refine ⟨65433289163516649939032711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43622192775677766626021807 65433289163516649939032711)
            ·
              refine ⟨98149933745274974908549067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65433289163516649939032711 98149933745274974908549067)
              ·
                refine ⟨147224900617912462362823601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98149933745274974908549067 147224900617912462362823601)
                ·
                  refine ⟨110418675463434346772117701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147224900617912462362823601 110418675463434346772117701)
                  ·
                    refine ⟨20703501649393940019772069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110418675463434346772117701 20703501649393940019772069)
                    ·
                      refine ⟨3881906559261363753707263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20703501649393940019772069 3881906559261363753707263)
                      ·
                        rfl

theorem cell23_7559986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_7559986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559986 prefixEnd_7559986 := by exact prefixLift 7559986
  have htrace : WordTrace (prefixWord ++ tailWord_7559986) baseStart_7559986 baseEnd_7559986 := by
    simpa [prefixWord, tailWord_7559986, baseEnd_7559986] using wordTrace_append hprefix tailTrace_7559986
  have hstable : (prefixWord ++ tailWord_7559986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559986).length < 2 ^ (prefixWord ++ tailWord_7559986).sum := by decide
  have hdescent : baseEnd_7559986 < baseStart_7559986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560017 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 3, 4]
def baseStart_7560017 : Nat := 118140960795 + 7560017 * 2 ^ 59
def prefixEnd_7560017 : Nat := 4983230072969 + 3 ^ 40 * 7560017 * 2
def baseEnd_7560017 : Nat := 1293974159053884377473207

theorem tailTrace_7560017 : CollatzResearch.WordTrace tailWord_7560017 prefixEnd_7560017 1293974159053884377473207 := by
  unfold tailWord_7560017
  simp only [CollatzResearch.WordTrace]
  refine ⟨275736472652357031955158305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183824315101571354636772203 275736472652357031955158305)
  ·
    refine ⟨206802354489267773966368729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275736472652357031955158305 206802354489267773966368729)
    ·
      refine ⟨155101765866950830474776547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206802354489267773966368729 155101765866950830474776547)
      ·
        refine ⟨232652648800426245712164821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155101765866950830474776547 232652648800426245712164821)
        ·
          refine ⟨5452796456259990133878863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 232652648800426245712164821 5452796456259990133878863)
          ·
            refine ⟨8179194684389985200818295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5452796456259990133878863 8179194684389985200818295)
            ·
              refine ⟨12268792026584977801227443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8179194684389985200818295 12268792026584977801227443)
              ·
                refine ⟨18403188039877466701841165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12268792026584977801227443 18403188039877466701841165)
                ·
                  refine ⟨6901195514954050013190437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18403188039877466701841165 6901195514954050013190437)
                  ·
                    refine ⟨1293974159053884377473207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6901195514954050013190437 1293974159053884377473207)
                    ·
                      rfl

theorem cell23_7560017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_7560017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560017 prefixEnd_7560017 := by exact prefixLift 7560017
  have htrace : WordTrace (prefixWord ++ tailWord_7560017) baseStart_7560017 baseEnd_7560017 := by
    simpa [prefixWord, tailWord_7560017, baseEnd_7560017] using wordTrace_append hprefix tailTrace_7560017
  have hstable : (prefixWord ++ tailWord_7560017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560017).length < 2 ^ (prefixWord ++ tailWord_7560017).sum := by decide
  have hdescent : baseEnd_7560017 < baseStart_7560017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560033 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_7560033 : Nat := 118140960795 + 7560033 * 2 ^ 59
def prefixEnd_7560033 : Nat := 4983230072969 + 3 ^ 40 * 7560033 * 2
def baseEnd_7560033 : Nat := 3881930692852125069819547

theorem tailTrace_7560033 : CollatzResearch.WordTrace tailWord_7560033 prefixEnd_7560033 3881930692852125069819547 := by
  unfold tailWord_7560033
  simp only [CollatzResearch.WordTrace]
  refine ⟨275737056220299066687740753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183824704146866044458493835 275737056220299066687740753)
  ·
    refine ⟨206802792165224300015805565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275737056220299066687740753 206802792165224300015805565)
    ·
      refine ⟨77551047061959112505927087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206802792165224300015805565 77551047061959112505927087)
      ·
        refine ⟨116326570592938668758890631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77551047061959112505927087 116326570592938668758890631)
        ·
          refine ⟨174489855889408003138335947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116326570592938668758890631 174489855889408003138335947)
          ·
            refine ⟨261734783834112004707503921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174489855889408003138335947 261734783834112004707503921)
            ·
              refine ⟨196301087875584003530627941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261734783834112004707503921 196301087875584003530627941)
              ·
                refine ⟨36806453976672000661992739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196301087875584003530627941 36806453976672000661992739)
                ·
                  refine ⟨55209680965008000992989109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36806453976672000661992739 55209680965008000992989109)
                  ·
                    refine ⟨5175907590469500093092729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55209680965008000992989109 5175907590469500093092729)
                    ·
                      refine ⟨3881930692852125069819547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175907590469500093092729 3881930692852125069819547)
                      ·
                        rfl

theorem cell23_7560033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_7560033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560033 prefixEnd_7560033 := by exact prefixLift 7560033
  have htrace : WordTrace (prefixWord ++ tailWord_7560033) baseStart_7560033 baseEnd_7560033 := by
    simpa [prefixWord, tailWord_7560033, baseEnd_7560033] using wordTrace_append hprefix tailTrace_7560033
  have hstable : (prefixWord ++ tailWord_7560033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560033).length < 2 ^ (prefixWord ++ tailWord_7560033).sum := by decide
  have hdescent : baseEnd_7560033 < baseStart_7560033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560043 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 1, 5]
def baseStart_7560043 : Nat := 118140960795 + 7560043 * 2 ^ 59
def prefixEnd_7560043 : Nat := 4983230072969 + 3 ^ 40 * 7560043 * 2
def baseEnd_7560043 : Nat := 1293978609219556676898167

theorem tailTrace_7560043 : CollatzResearch.WordTrace tailWord_7560043 prefixEnd_7560043 1293978609219556676898167 := by
  unfold tailWord_7560043
  simp only [CollatzResearch.WordTrace]
  refine ⟨275737420950262838395604783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183824947300175225597069855 275737420950262838395604783)
  ·
    refine ⟨413606131425394257593407175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275737420950262838395604783 413606131425394257593407175)
    ·
      refine ⟨620409197138091386390110763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413606131425394257593407175 620409197138091386390110763)
      ·
        refine ⟨930613795707137079585166145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620409197138091386390110763 930613795707137079585166145)
        ·
          refine ⟨697960346780352809688874609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930613795707137079585166145 697960346780352809688874609)
          ·
            refine ⟨523470260085264607266655957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697960346780352809688874609 523470260085264607266655957)
            ·
              refine ⟨12268834220748389232812249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 523470260085264607266655957 12268834220748389232812249)
              ·
                refine ⟨9201625665561291924609187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12268834220748389232812249 9201625665561291924609187)
                ·
                  refine ⟨13802438498341937886913781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9201625665561291924609187 13802438498341937886913781)
                  ·
                    refine ⟨1293978609219556676898167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13802438498341937886913781 1293978609219556676898167)
                    ·
                      rfl

theorem cell23_7560043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 5].length) (baseStart_7560043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560043 prefixEnd_7560043 := by exact prefixLift 7560043
  have htrace : WordTrace (prefixWord ++ tailWord_7560043) baseStart_7560043 baseEnd_7560043 := by
    simpa [prefixWord, tailWord_7560043, baseEnd_7560043] using wordTrace_append hprefix tailTrace_7560043
  have hstable : (prefixWord ++ tailWord_7560043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560043).length < 2 ^ (prefixWord ++ tailWord_7560043).sum := by decide
  have hdescent : baseEnd_7560043 < baseStart_7560043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560050 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_7560050 : Nat := 118140960795 + 7560050 * 2 ^ 59
def prefixEnd_7560050 : Nat := 4983230072969 + 3 ^ 40 * 7560050 * 2
def baseEnd_7560050 : Nat := 3881939422023251503306969

theorem tailTrace_7560050 : CollatzResearch.WordTrace tailWord_7560050 prefixEnd_7560050 3881939422023251503306969 := by
  unfold tailWord_7560050
  simp only [CollatzResearch.WordTrace]
  refine ⟨68934419065309369647777401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183825117507491652394073069 68934419065309369647777401)
  ·
    refine ⟨51700814298982027235833051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68934419065309369647777401 51700814298982027235833051)
    ·
      refine ⟨77551221448473040853749577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51700814298982027235833051 77551221448473040853749577)
      ·
        refine ⟨58163416086354780640312183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77551221448473040853749577 58163416086354780640312183)
        ·
          refine ⟨87245124129532170960468275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58163416086354780640312183 87245124129532170960468275)
          ·
            refine ⟨130867686194298256440702413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87245124129532170960468275 130867686194298256440702413)
            ·
              refine ⟨49075382322861846165263405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130867686194298256440702413 49075382322861846165263405)
              ·
                refine ⟨18403268371073192311973777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49075382322861846165263405 18403268371073192311973777)
                ·
                  refine ⟨13802451278304894233980333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18403268371073192311973777 13802451278304894233980333)
                  ·
                    refine ⟨5175919229364335337742625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13802451278304894233980333 5175919229364335337742625)
                    ·
                      refine ⟨3881939422023251503306969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175919229364335337742625 3881939422023251503306969)
                      ·
                        rfl

theorem cell23_7560050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_7560050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560050 prefixEnd_7560050 := by exact prefixLift 7560050
  have htrace : WordTrace (prefixWord ++ tailWord_7560050) baseStart_7560050 baseEnd_7560050 := by
    simpa [prefixWord, tailWord_7560050, baseEnd_7560050] using wordTrace_append hprefix tailTrace_7560050
  have hstable : (prefixWord ++ tailWord_7560050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560050).length < 2 ^ (prefixWord ++ tailWord_7560050).sum := by decide
  have hdescent : baseEnd_7560050 < baseStart_7560050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560063 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 4]
def baseStart_7560063 : Nat := 118140960795 + 7560063 * 2 ^ 59
def prefixEnd_7560063 : Nat := 4983230072969 + 3 ^ 40 * 7560063 * 2
def baseEnd_7560063 : Nat := 3881946097271759952444409

theorem tailTrace_7560063 : CollatzResearch.WordTrace tailWord_7560063 prefixEnd_7560063 3881946097271759952444409 := by
  unfold tailWord_7560063
  simp only [CollatzResearch.WordTrace]
  refine ⟨275738150410190381811332843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183825433606793587874221895 275738150410190381811332843)
  ·
    refine ⟨413607225615285572716999265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275738150410190381811332843 413607225615285572716999265)
    ·
      refine ⟨310205419211464179537749449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413607225615285572716999265 310205419211464179537749449)
      ·
        refine ⟨232654064408598134653312087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310205419211464179537749449 232654064408598134653312087)
        ·
          refine ⟨348981096612897201979968131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232654064408598134653312087 348981096612897201979968131)
          ·
            refine ⟨523471644919345802969952197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348981096612897201979968131 523471644919345802969952197)
            ·
              refine ⟨98150933422377338056866037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 523471644919345802969952197 98150933422377338056866037)
              ·
                refine ⟨9201650008347875442831191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98150933422377338056866037 9201650008347875442831191)
                ·
                  refine ⟨13802475012521813164246787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9201650008347875442831191 13802475012521813164246787)
                  ·
                    refine ⟨20703712518782719746370181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13802475012521813164246787 20703712518782719746370181)
                    ·
                      refine ⟨3881946097271759952444409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20703712518782719746370181 3881946097271759952444409)
                      ·
                        rfl

theorem cell23_7560063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_7560063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560063 prefixEnd_7560063 := by exact prefixLift 7560063
  have htrace : WordTrace (prefixWord ++ tailWord_7560063) baseStart_7560063 baseEnd_7560063 := by
    simpa [prefixWord, tailWord_7560063, baseEnd_7560063] using wordTrace_append hprefix tailTrace_7560063
  have hstable : (prefixWord ++ tailWord_7560063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560063).length < 2 ^ (prefixWord ++ tailWord_7560063).sum := by decide
  have hdescent : baseEnd_7560063 < baseStart_7560063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560074 : List Nat := [3, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_7560074 : Nat := 118140960795 + 7560074 * 2 ^ 59
def prefixEnd_7560074 : Nat := 4983230072969 + 3 ^ 40 * 7560074 * 2
def baseEnd_7560074 : Nat := 3881951745558959409406859

theorem tailTrace_7560074 : CollatzResearch.WordTrace tailWord_7560074 prefixEnd_7560074 3881951745558959409406859 := by
  unfold tailWord_7560074
  simp only [CollatzResearch.WordTrace]
  refine ⟨68934637903287632672495819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183825701075433687126655517 68934637903287632672495819)
  ·
    refine ⟨103401956854931449008743729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68934637903287632672495819 103401956854931449008743729)
    ·
      refine ⟨77551467641198586756557797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103401956854931449008743729 77551467641198586756557797)
      ·
        refine ⟨14540900182724735016854587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77551467641198586756557797 14540900182724735016854587)
        ·
          refine ⟨21811350274087102525281881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14540900182724735016854587 21811350274087102525281881)
          ·
            refine ⟨16358512705565326893961411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21811350274087102525281881 16358512705565326893961411)
            ·
              refine ⟨24537769058347990340942117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16358512705565326893961411 24537769058347990340942117)
              ·
                refine ⟨4600831698440248188926647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24537769058347990340942117 4600831698440248188926647)
                ·
                  refine ⟨6901247547660372283389971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600831698440248188926647 6901247547660372283389971)
                  ·
                    refine ⟨10351871321490558425084957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6901247547660372283389971 10351871321490558425084957)
                    ·
                      refine ⟨3881951745558959409406859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10351871321490558425084957 3881951745558959409406859)
                      ·
                        rfl

theorem cell23_7560074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_7560074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560074 prefixEnd_7560074 := by exact prefixLift 7560074
  have htrace : WordTrace (prefixWord ++ tailWord_7560074) baseStart_7560074 baseEnd_7560074 := by
    simpa [prefixWord, tailWord_7560074, baseEnd_7560074] using wordTrace_append hprefix tailTrace_7560074
  have hstable : (prefixWord ++ tailWord_7560074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560074).length < 2 ^ (prefixWord ++ tailWord_7560074).sum := by decide
  have hdescent : baseEnd_7560074 < baseStart_7560074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560076 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_7560076 : Nat := 118140960795 + 7560076 * 2 ^ 59
def prefixEnd_7560076 : Nat := 4983230072969 + 3 ^ 40 * 7560076 * 2
def baseEnd_7560076 : Nat := 3881952772520268401581849

theorem tailTrace_7560076 : CollatzResearch.WordTrace tailWord_7560076 prefixEnd_7560076 3881952772520268401581849 := by
  unfold tailWord_7560076
  simp only [CollatzResearch.WordTrace]
  refine ⟨137869312279571642515778041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183825749706095523354370721 137869312279571642515778041)
  ·
    refine ⟨103401984209678731886833531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137869312279571642515778041 103401984209678731886833531)
    ·
      refine ⟨155102976314518097830250297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103401984209678731886833531 155102976314518097830250297)
      ·
        refine ⟨116327232235888573372687723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155102976314518097830250297 116327232235888573372687723)
        ·
          refine ⟨174490848353832860059031585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116327232235888573372687723 174490848353832860059031585)
          ·
            refine ⟨130868136265374645044273689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174490848353832860059031585 130868136265374645044273689)
            ·
              refine ⟨98151102199030983783205267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130868136265374645044273689 98151102199030983783205267)
              ·
                refine ⟨147226653298546475674807901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98151102199030983783205267 147226653298546475674807901)
                ·
                  refine ⟨55209994986954928378052963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147226653298546475674807901 55209994986954928378052963)
                  ·
                    refine ⟨82814992480432392567079445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55209994986954928378052963 82814992480432392567079445)
                    ·
                      refine ⟨3881952772520268401581849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82814992480432392567079445 3881952772520268401581849)
                      ·
                        rfl

theorem cell23_7560076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_7560076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560076 prefixEnd_7560076 := by exact prefixLift 7560076
  have htrace : WordTrace (prefixWord ++ tailWord_7560076) baseStart_7560076 baseEnd_7560076 := by
    simpa [prefixWord, tailWord_7560076, baseEnd_7560076] using wordTrace_append hprefix tailTrace_7560076
  have hstable : (prefixWord ++ tailWord_7560076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560076).length < 2 ^ (prefixWord ++ tailWord_7560076).sum := by decide
  have hdescent : baseEnd_7560076 < baseStart_7560076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560090 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_7560090 : Nat := 118140960795 + 7560090 * 2 ^ 59
def prefixEnd_7560090 : Nat := 4983230072969 + 3 ^ 40 * 7560090 * 2
def baseEnd_7560090 : Nat := 1293986653749810448935595

theorem tailTrace_7560090 : CollatzResearch.WordTrace tailWord_7560090 prefixEnd_7560090 1293986653749810448935595 := by
  unfold tailWord_7560090
  simp only [CollatzResearch.WordTrace]
  refine ⟨68934783795273141355641431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183826090120728376948377149 68934783795273141355641431)
  ·
    refine ⟨103402175692909712033462147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68934783795273141355641431 103402175692909712033462147)
    ·
      refine ⟨155103263539364568050193221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103402175692909712033462147 155103263539364568050193221)
      ·
        refine ⟨29081861913630856509411229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155103263539364568050193221 29081861913630856509411229)
        ·
          refine ⟨10905698217611571191029211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29081861913630856509411229 10905698217611571191029211)
          ·
            refine ⟨16358547326417356786543817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10905698217611571191029211 16358547326417356786543817)
            ·
              refine ⟨12268910494813017589907863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16358547326417356786543817 12268910494813017589907863)
              ·
                refine ⟨18403365742219526384861795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12268910494813017589907863 18403365742219526384861795)
                ·
                  refine ⟨27605048613329289577292693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18403365742219526384861795 27605048613329289577292693)
                  ·
                    refine ⟨1293986653749810448935595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27605048613329289577292693 1293986653749810448935595)
                    ·
                      rfl

theorem cell23_7560090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_7560090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560090 prefixEnd_7560090 := by exact prefixLift 7560090
  have htrace : WordTrace (prefixWord ++ tailWord_7560090) baseStart_7560090 baseEnd_7560090 := by
    simpa [prefixWord, tailWord_7560090, baseEnd_7560090] using wordTrace_append hprefix tailTrace_7560090
  have hstable : (prefixWord ++ tailWord_7560090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560090).length < 2 ^ (prefixWord ++ tailWord_7560090).sum := by decide
  have hdescent : baseEnd_7560090 < baseStart_7560090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560097 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7560097 : Nat := 118140960795 + 7560097 * 2 ^ 59
def prefixEnd_7560097 : Nat := 4983230072969 + 3 ^ 40 * 7560097 * 2
def baseEnd_7560097 : Nat := 3881963555614012819419253

theorem tailTrace_7560097 : CollatzResearch.WordTrace tailWord_7560097 prefixEnd_7560097 3881963555614012819419253 := by
  unfold tailWord_7560097
  simp only [CollatzResearch.WordTrace]
  refine ⟨275739390492067205618070545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183826260328044803745380363 275739390492067205618070545)
  ·
    refine ⟨206804542869050404213552909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275739390492067205618070545 206804542869050404213552909)
    ·
      refine ⟨77551703575893901580082341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206804542869050404213552909 77551703575893901580082341)
      ·
        refine ⟨14540944420480106546265439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77551703575893901580082341 14540944420480106546265439)
        ·
          refine ⟨21811416630720159819398159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14540944420480106546265439 21811416630720159819398159)
          ·
            refine ⟨32717124946080239729097239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21811416630720159819398159 32717124946080239729097239)
            ·
              refine ⟨49075687419120359593645859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32717124946080239729097239 49075687419120359593645859)
              ·
                refine ⟨73613531128680539390468789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49075687419120359593645859 73613531128680539390468789)
                ·
                  refine ⟨6901268543313800567856449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73613531128680539390468789 6901268543313800567856449)
                  ·
                    refine ⟨5175951407485350425892337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6901268543313800567856449 5175951407485350425892337)
                    ·
                      refine ⟨3881963555614012819419253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175951407485350425892337 3881963555614012819419253)
                      ·
                        rfl

theorem cell23_7560097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7560097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560097 prefixEnd_7560097 := by exact prefixLift 7560097
  have htrace : WordTrace (prefixWord ++ tailWord_7560097) baseStart_7560097 baseEnd_7560097 := by
    simpa [prefixWord, tailWord_7560097, baseEnd_7560097] using wordTrace_append hprefix tailTrace_7560097
  have hstable : (prefixWord ++ tailWord_7560097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560097).length < 2 ^ (prefixWord ++ tailWord_7560097).sum := by decide
  have hdescent : baseEnd_7560097 < baseStart_7560097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560100 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_7560100 : Nat := 118140960795 + 7560100 * 2 ^ 59
def prefixEnd_7560100 : Nat := 4983230072969 + 3 ^ 40 * 7560100 * 2
def baseEnd_7560100 : Nat := 3881965096055976307681739

theorem tailTrace_7560100 : CollatzResearch.WordTrace tailWord_7560100 prefixEnd_7560100 3881965096055976307681739 := by
  unfold tailWord_7560100
  simp only [CollatzResearch.WordTrace]
  refine ⟨137869749955528168565214877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183826333274037558086953169 137869749955528168565214877)
  ·
    refine ⟨51701156233323063211955579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137869749955528168565214877 51701156233323063211955579)
    ·
      refine ⟨77551734349984594817933369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51701156233323063211955579 77551734349984594817933369)
      ·
        refine ⟨58163800762488446113450027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77551734349984594817933369 58163800762488446113450027)
        ·
          refine ⟨87245701143732669170175041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58163800762488446113450027 87245701143732669170175041)
          ·
            refine ⟨65434275857799501877631281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87245701143732669170175041 65434275857799501877631281)
            ·
              refine ⟨49075706893349626408223461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65434275857799501877631281 49075706893349626408223461)
              ·
                refine ⟨9201695042503054951541899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49075706893349626408223461 9201695042503054951541899)
                ·
                  refine ⟨13802542563754582427312849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9201695042503054951541899 13802542563754582427312849)
                  ·
                    refine ⟨10351906922815936820484637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13802542563754582427312849 10351906922815936820484637)
                    ·
                      refine ⟨3881965096055976307681739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10351906922815936820484637 3881965096055976307681739)
                      ·
                        rfl

theorem cell23_7560100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_7560100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560100 prefixEnd_7560100 := by exact prefixLift 7560100
  have htrace : WordTrace (prefixWord ++ tailWord_7560100) baseStart_7560100 baseEnd_7560100 := by
    simpa [prefixWord, tailWord_7560100, baseEnd_7560100] using wordTrace_append hprefix tailTrace_7560100
  have hstable : (prefixWord ++ tailWord_7560100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560100).length < 2 ^ (prefixWord ++ tailWord_7560100).sum := by decide
  have hdescent : baseEnd_7560100 < baseStart_7560100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560123 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 9, 2]
def baseStart_7560123 : Nat := 118140960795 + 7560123 * 2 ^ 59
def prefixEnd_7560123 : Nat := 4983230072969 + 3 ^ 40 * 7560123 * 2
def baseEnd_7560123 : Nat := 3881976906111029717694133

theorem tailTrace_7560123 : CollatzResearch.WordTrace tailWord_7560123 prefixEnd_7560123 3881976906111029717694133 := by
  unfold tailWord_7560123
  simp only [CollatzResearch.WordTrace]
  refine ⟨275740338789973012058517023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183826892526648674705678015 275740338789973012058517023)
  ·
    refine ⟨413610508184959518087775535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275740338789973012058517023 413610508184959518087775535)
    ·
      refine ⟨620415762277439277131663303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413610508184959518087775535 620415762277439277131663303)
      ·
        refine ⟨930623643416158915697494955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620415762277439277131663303 930623643416158915697494955)
        ·
          refine ⟨1395935465124238373546242433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930623643416158915697494955 1395935465124238373546242433)
          ·
            refine ⟨1046951598843178780159681825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395935465124238373546242433 1046951598843178780159681825)
            ·
              refine ⟨785213699132384085119761369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046951598843178780159681825 785213699132384085119761369)
              ·
                refine ⟨588910274349288063839821027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785213699132384085119761369 588910274349288063839821027)
                ·
                  refine ⟨883365411523932095759731541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588910274349288063839821027 883365411523932095759731541)
                  ·
                    refine ⟨5175969208148039623592177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 883365411523932095759731541 5175969208148039623592177)
                    ·
                      refine ⟨3881976906111029717694133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175969208148039623592177 3881976906111029717694133)
                      ·
                        rfl

theorem cell23_7560123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 9, 2].length) (baseStart_7560123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560123 prefixEnd_7560123 := by exact prefixLift 7560123
  have htrace : WordTrace (prefixWord ++ tailWord_7560123) baseStart_7560123 baseEnd_7560123 := by
    simpa [prefixWord, tailWord_7560123, baseEnd_7560123] using wordTrace_append hprefix tailTrace_7560123
  have hstable : (prefixWord ++ tailWord_7560123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560123).length < 2 ^ (prefixWord ++ tailWord_7560123).sum := by decide
  have hdescent : baseEnd_7560123 < baseStart_7560123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560141 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7560141 : Nat := 118140960795 + 7560141 * 2 ^ 59
def prefixEnd_7560141 : Nat := 4983230072969 + 3 ^ 40 * 7560141 * 2
def baseEnd_7560141 : Nat := 1293995382920936882423017

theorem tailTrace_7560141 : CollatzResearch.WordTrace tailWord_7560141 prefixEnd_7560141 1293995382920936882423017 := by
  unfold tailWord_7560141
  simp only [CollatzResearch.WordTrace]
  refine ⟨275740995303907801132672277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183827330202605200755114851 275740995303907801132672277)
  ·
    refine ⟨12925359154870678178094013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 275740995303907801132672277 12925359154870678178094013)
    ·
      refine ⟨4847009683076504316785255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12925359154870678178094013 4847009683076504316785255)
      ·
        refine ⟨7270514524614756475177883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4847009683076504316785255 7270514524614756475177883)
        ·
          refine ⟨10905771786922134712766825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7270514524614756475177883 10905771786922134712766825)
          ·
            refine ⟨8179328840191601034575119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10905771786922134712766825 8179328840191601034575119)
            ·
              refine ⟨12268993260287401551862679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8179328840191601034575119 12268993260287401551862679)
              ·
                refine ⟨18403489890431102327794019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12268993260287401551862679 18403489890431102327794019)
                ·
                  refine ⟨27605234835646653491691029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18403489890431102327794019 27605234835646653491691029)
                  ·
                    refine ⟨1293995382920936882423017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27605234835646653491691029 1293995382920936882423017)
                    ·
                      rfl

theorem cell23_7560141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7560141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560141 prefixEnd_7560141 := by exact prefixLift 7560141
  have htrace : WordTrace (prefixWord ++ tailWord_7560141) baseStart_7560141 baseEnd_7560141 := by
    simpa [prefixWord, tailWord_7560141, baseEnd_7560141] using wordTrace_append hprefix tailTrace_7560141
  have hstable : (prefixWord ++ tailWord_7560141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560141).length < 2 ^ (prefixWord ++ tailWord_7560141).sum := by decide
  have hdescent : baseEnd_7560141 < baseStart_7560141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560165 : List Nat := [1, 3, 1, 6, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7560165 : Nat := 118140960795 + 7560165 * 2 ^ 59
def prefixEnd_7560165 : Nat := 4983230072969 + 3 ^ 40 * 7560165 * 2
def baseEnd_7560165 : Nat := 3881998472298518553368941

theorem tailTrace_7560165 : CollatzResearch.WordTrace tailWord_7560165 prefixEnd_7560165 3881998472298518553368941 := by
  unfold tailWord_7560165
  simp only [CollatzResearch.WordTrace]
  refine ⟨275741870655820853231545949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183827913770547235487697299 275741870655820853231545949)
  ·
    refine ⟨103403201495932819961829731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275741870655820853231545949 103403201495932819961829731)
    ·
      refine ⟨155104802243899229942744597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103403201495932819961829731 155104802243899229942744597)
      ·
        refine ⟨7270537605182776403566153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155104802243899229942744597 7270537605182776403566153)
        ·
          refine ⟨5452903203887082302674615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7270537605182776403566153 5452903203887082302674615)
          ·
            refine ⟨8179354805830623454011923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5452903203887082302674615 8179354805830623454011923)
            ·
              refine ⟨12269032208745935181017885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8179354805830623454011923 12269032208745935181017885)
              ·
                refine ⟨4600887078279725692881707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12269032208745935181017885 4600887078279725692881707)
                ·
                  refine ⟨6901330617419588539322561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600887078279725692881707 6901330617419588539322561)
                  ·
                    refine ⟨5175997963064691404491921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6901330617419588539322561 5175997963064691404491921)
                    ·
                      refine ⟨3881998472298518553368941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175997963064691404491921 3881998472298518553368941)
                      ·
                        rfl

theorem cell23_7560165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7560165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560165 prefixEnd_7560165 := by exact prefixLift 7560165
  have htrace : WordTrace (prefixWord ++ tailWord_7560165) baseStart_7560165 baseEnd_7560165 := by
    simpa [prefixWord, tailWord_7560165, baseEnd_7560165] using wordTrace_append hprefix tailTrace_7560165
  have hstable : (prefixWord ++ tailWord_7560165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560165).length < 2 ^ (prefixWord ++ tailWord_7560165).sum := by decide
  have hdescent : baseEnd_7560165 < baseStart_7560165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560187 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 2, 2, 2]
def baseStart_7560187 : Nat := 118140960795 + 7560187 * 2 ^ 59
def prefixEnd_7560187 : Nat := 4983230072969 + 3 ^ 40 * 7560187 * 2
def baseEnd_7560187 : Nat := 3882009768872917467293839

theorem tailTrace_7560187 : CollatzResearch.WordTrace tailWord_7560187 prefixEnd_7560187 3882009768872917467293839 := by
  unfold tailWord_7560187
  simp only [CollatzResearch.WordTrace]
  refine ⟨275742673061741150988846815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183828448707827433992564543 275742673061741150988846815)
  ·
    refine ⟨413614009592611726483270223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275742673061741150988846815 413614009592611726483270223)
    ·
      refine ⟨620421014388917589724905335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413614009592611726483270223 620421014388917589724905335)
      ·
        refine ⟨930631521583376384587358003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620421014388917589724905335 930631521583376384587358003)
        ·
          refine ⟨1395947282375064576881037005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930631521583376384587358003 1395947282375064576881037005)
          ·
            refine ⟨523480230890649216330388877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1395947282375064576881037005 523480230890649216330388877)
            ·
              refine ⟨196305086583993456123895829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523480230890649216330388877 196305086583993456123895829)
              ·
                refine ⟨9201800933624693255807617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196305086583993456123895829 9201800933624693255807617)
                ·
                  refine ⟨6901350700218519941855713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9201800933624693255807617 6901350700218519941855713)
                  ·
                    refine ⟨5176013025163889956391785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6901350700218519941855713 5176013025163889956391785)
                    ·
                      refine ⟨3882009768872917467293839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5176013025163889956391785 3882009768872917467293839)
                      ·
                        rfl

theorem cell23_7560187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 2, 2].length) (baseStart_7560187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560187 prefixEnd_7560187 := by exact prefixLift 7560187
  have htrace : WordTrace (prefixWord ++ tailWord_7560187) baseStart_7560187 baseEnd_7560187 := by
    simpa [prefixWord, tailWord_7560187, baseEnd_7560187] using wordTrace_append hprefix tailTrace_7560187
  have hstable : (prefixWord ++ tailWord_7560187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560187).length < 2 ^ (prefixWord ++ tailWord_7560187).sum := by decide
  have hdescent : baseEnd_7560187 < baseStart_7560187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560204 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 2, 2, 2]
def baseStart_7560204 : Nat := 118140960795 + 7560204 * 2 ^ 59
def prefixEnd_7560204 : Nat := 4983230072969 + 3 ^ 40 * 7560204 * 2
def baseEnd_7560204 : Nat := 3882018498044043900781261

theorem tailTrace_7560204 : CollatzResearch.WordTrace tailWord_7560204 prefixEnd_7560204 3882018498044043900781261 := by
  unfold tailWord_7560204
  simp only [CollatzResearch.WordTrace]
  refine ⟨137871646551339781446107833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183828862068453041928143777 137871646551339781446107833)
  ·
    refine ⟨103403734913504836084580875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137871646551339781446107833 103403734913504836084580875)
    ·
      refine ⟨155105602370257254126871313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103403734913504836084580875 155105602370257254126871313)
      ·
        refine ⟨116329201777692940595153485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155105602370257254126871313 116329201777692940595153485)
        ·
          refine ⟨43623450666634852723182557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116329201777692940595153485 43623450666634852723182557)
          ·
            refine ⟨16358793999988069771193459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43623450666634852723182557 16358793999988069771193459)
            ·
              refine ⟨24538190999982104656790189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16358793999988069771193459 24538190999982104656790189)
              ·
                refine ⟨9201821624993289246296321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24538190999982104656790189 9201821624993289246296321)
                ·
                  refine ⟨6901366218744966934722241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9201821624993289246296321 6901366218744966934722241)
                  ·
                    refine ⟨5176024664058725201041681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6901366218744966934722241 5176024664058725201041681)
                    ·
                      refine ⟨3882018498044043900781261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5176024664058725201041681 3882018498044043900781261)
                      ·
                        rfl

theorem cell23_7560204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_7560204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560204 prefixEnd_7560204 := by exact prefixLift 7560204
  have htrace : WordTrace (prefixWord ++ tailWord_7560204) baseStart_7560204 baseEnd_7560204 := by
    simpa [prefixWord, tailWord_7560204, baseEnd_7560204] using wordTrace_append hprefix tailTrace_7560204
  have hstable : (prefixWord ++ tailWord_7560204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560204).length < 2 ^ (prefixWord ++ tailWord_7560204).sum := by decide
  have hdescent : baseEnd_7560204 < baseStart_7560204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560243 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 4]
def baseStart_7560243 : Nat := 118140960795 + 7560243 * 2 ^ 59
def prefixEnd_7560243 : Nat := 4983230072969 + 3 ^ 40 * 7560243 * 2
def baseEnd_7560243 : Nat := 3882038523789569248193581

theorem tailTrace_7560243 : CollatzResearch.WordTrace tailWord_7560243 prefixEnd_7560243 3882038523789569248193581 := by
  unfold tailWord_7560243
  simp only [CollatzResearch.WordTrace]
  refine ⟨275744715549538272552885383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183829810366358848368590255 275744715549538272552885383)
  ·
    refine ⟨413617073324307408829328075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275744715549538272552885383 413617073324307408829328075)
    ·
      refine ⟨620425609986461113243992113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413617073324307408829328075 620425609986461113243992113)
      ·
        refine ⟨465319207489845834932994085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620425609986461113243992113 465319207489845834932994085)
        ·
          refine ⟨87247351404346094049936391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465319207489845834932994085 87247351404346094049936391)
          ·
            refine ⟨130871027106519141074904587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87247351404346094049936391 130871027106519141074904587)
            ·
              refine ⟨196306540659778711612356881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130871027106519141074904587 196306540659778711612356881)
              ·
                refine ⟨147229905494834033709267661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196306540659778711612356881 147229905494834033709267661)
                ·
                  refine ⟨55211214560562762640975373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147229905494834033709267661 55211214560562762640975373)
                  ·
                    refine ⟨20704205460211035990365765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55211214560562762640975373 20704205460211035990365765)
                    ·
                      refine ⟨3882038523789569248193581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20704205460211035990365765 3882038523789569248193581)
                      ·
                        rfl

theorem cell23_7560243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_7560243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560243 prefixEnd_7560243 := by exact prefixLift 7560243
  have htrace : WordTrace (prefixWord ++ tailWord_7560243) baseStart_7560243 baseEnd_7560243 := by
    simpa [prefixWord, tailWord_7560243, baseEnd_7560243] using wordTrace_append hprefix tailTrace_7560243
  have hstable : (prefixWord ++ tailWord_7560243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560243).length < 2 ^ (prefixWord ++ tailWord_7560243).sum := by decide
  have hdescent : baseEnd_7560243 < baseStart_7560243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560244 : List Nat := [2, 5, 1, 2, 1, 2, 1, 4, 5]
def baseStart_7560244 : Nat := 118140960795 + 7560244 * 2 ^ 59
def prefixEnd_7560244 : Nat := 4983230072969 + 3 ^ 40 * 7560244 * 2
def baseEnd_7560244 : Nat := 431337670807802638253453

theorem tailTrace_7560244 : CollatzResearch.WordTrace tailWord_7560244 prefixEnd_7560244 431337670807802638253453 := by
  unfold tailWord_7560244
  simp only [CollatzResearch.WordTrace]
  refine ⟨137872376011267324861835893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183829834681689766482447857 137872376011267324861835893)
  ·
    refine ⟨12925535251056311705797115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137872376011267324861835893 12925535251056311705797115)
    ·
      refine ⟨19388302876584467558695673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12925535251056311705797115 19388302876584467558695673)
      ·
        refine ⟨14541227157438350669021755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19388302876584467558695673 14541227157438350669021755)
        ·
          refine ⟨21811840736157526003532633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14541227157438350669021755 21811840736157526003532633)
          ·
            refine ⟨16358880552118144502649475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21811840736157526003532633 16358880552118144502649475)
            ·
              refine ⟨24538320828177216753974213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16358880552118144502649475 24538320828177216753974213)
              ·
                refine ⟨4600935155283228141370165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24538320828177216753974213 4600935155283228141370165)
                ·
                  refine ⟨431337670807802638253453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4600935155283228141370165 431337670807802638253453)
                  ·
                    rfl

theorem cell23_7560244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_7560244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560244 prefixEnd_7560244 := by exact prefixLift 7560244
  have htrace : WordTrace (prefixWord ++ tailWord_7560244) baseStart_7560244 baseEnd_7560244 := by
    simpa [prefixWord, tailWord_7560244, baseEnd_7560244] using wordTrace_append hprefix tailTrace_7560244
  have hstable : (prefixWord ++ tailWord_7560244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560244).length < 2 ^ (prefixWord ++ tailWord_7560244).sum := by decide
  have hdescent : baseEnd_7560244 < baseStart_7560244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560280 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_7560280 : Nat := 118140960795 + 7560280 * 2 ^ 59
def prefixEnd_7560280 : Nat := 4983230072969 + 3 ^ 40 * 7560280 * 2
def baseEnd_7560280 : Nat := 3882057522573785603430911

theorem tailTrace_7560280 : CollatzResearch.WordTrace tailWord_7560280 prefixEnd_7560280 3882057522573785603430911 := by
  unfold tailWord_7560280
  simp only [CollatzResearch.WordTrace]
  refine ⟨137873032525202113935991147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183830710033602818581321529 137873032525202113935991147)
  ·
    refine ⟨206809548787803170903986721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137873032525202113935991147 206809548787803170903986721)
    ·
      refine ⟨155107161590852378177990041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206809548787803170903986721 155107161590852378177990041)
      ·
        refine ⟨116330371193139283633492531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155107161590852378177990041 116330371193139283633492531)
        ·
          refine ⟨174495556789708925450238797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116330371193139283633492531 174495556789708925450238797)
          ·
            refine ⟨65435833796140847043839549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174495556789708925450238797 65435833796140847043839549)
            ·
              refine ⟨24538437673552817641439831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65435833796140847043839549 24538437673552817641439831)
              ·
                refine ⟨36807656510329226462159747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24538437673552817641439831 36807656510329226462159747)
                ·
                  refine ⟨55211484765493839693239621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36807656510329226462159747 55211484765493839693239621)
                  ·
                    refine ⟨10352153393530094942482429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55211484765493839693239621 10352153393530094942482429)
                    ·
                      refine ⟨3882057522573785603430911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10352153393530094942482429 3882057522573785603430911)
                      ·
                        rfl

theorem cell23_7560280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_7560280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560280 prefixEnd_7560280 := by exact prefixLift 7560280
  have htrace : WordTrace (prefixWord ++ tailWord_7560280) baseStart_7560280 baseEnd_7560280 := by
    simpa [prefixWord, tailWord_7560280, baseEnd_7560280] using wordTrace_append hprefix tailTrace_7560280
  have hstable : (prefixWord ++ tailWord_7560280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560280).length < 2 ^ (prefixWord ++ tailWord_7560280).sum := by decide
  have hdescent : baseEnd_7560280 < baseStart_7560280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560303 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_7560303 : Nat := 118140960795 + 7560303 * 2 ^ 59
def prefixEnd_7560303 : Nat := 4983230072969 + 3 ^ 40 * 7560303 * 2
def baseEnd_7560303 : Nat := 3882069332628839013443305

theorem tailTrace_7560303 : CollatzResearch.WordTrace tailWord_7560303 prefixEnd_7560303 3882069332628839013443305 := by
  unfold tailWord_7560303
  simp only [CollatzResearch.WordTrace]
  refine ⟨275746903929320902800069563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183831269286213935200046375 275746903929320902800069563)
  ·
    refine ⟨413620355893981354200104345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275746903929320902800069563 413620355893981354200104345)
    ·
      refine ⟨310215266920486015650078259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413620355893981354200104345 310215266920486015650078259)
      ·
        refine ⟨465322900380729023475117389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310215266920486015650078259 465322900380729023475117389)
        ·
          refine ⟨174496087642773383803169021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465322900380729023475117389 174496087642773383803169021)
          ·
            refine ⟨65436032866040018926188383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174496087642773383803169021 65436032866040018926188383)
            ·
              refine ⟨98154049299060028389282575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65436032866040018926188383 98154049299060028389282575)
              ·
                refine ⟨147231073948590042583923863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98154049299060028389282575 147231073948590042583923863)
                ·
                  refine ⟨220846610922885063875885795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147231073948590042583923863 220846610922885063875885795)
                  ·
                    refine ⟨331269916384327595813828693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220846610922885063875885795 331269916384327595813828693)
                    ·
                      refine ⟨3882069332628839013443305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 331269916384327595813828693 3882069332628839013443305)
                      ·
                        rfl

theorem cell23_7560303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_7560303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560303 prefixEnd_7560303 := by exact prefixLift 7560303
  have htrace : WordTrace (prefixWord ++ tailWord_7560303) baseStart_7560303 baseEnd_7560303 := by
    simpa [prefixWord, tailWord_7560303, baseEnd_7560303] using wordTrace_append hprefix tailTrace_7560303
  have hstable : (prefixWord ++ tailWord_7560303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560303).length < 2 ^ (prefixWord ++ tailWord_7560303).sum := by decide
  have hdescent : baseEnd_7560303 < baseStart_7560303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560317 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 6]
def baseStart_7560317 : Nat := 118140960795 + 7560317 * 2 ^ 59
def prefixEnd_7560317 : Nat := 4983230072969 + 3 ^ 40 * 7560317 * 2
def baseEnd_7560317 : Nat := 431341835706444662074249

theorem tailTrace_7560317 : CollatzResearch.WordTrace tailWord_7560317 prefixEnd_7560317 431341835706444662074249 := by
  unfold tailWord_7560317
  simp only [CollatzResearch.WordTrace]
  refine ⟨275747414551270183191079205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183831609700846788794052803 275747414551270183191079205)
  ·
    refine ⟨51702640228363159348327351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275747414551270183191079205 51702640228363159348327351)
    ·
      refine ⟨77553960342544739022491027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51702640228363159348327351 77553960342544739022491027)
      ·
        refine ⟨116330940513817108533736541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77553960342544739022491027 116330940513817108533736541)
        ·
          refine ⟨43624102692681415700151203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116330940513817108533736541 43624102692681415700151203)
          ·
            refine ⟨65436154039022123550226805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43624102692681415700151203 65436154039022123550226805)
            ·
              refine ⟨6134639441158324082833763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65436154039022123550226805 6134639441158324082833763)
              ·
                refine ⟨9201959161737486124250645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6134639441158324082833763 9201959161737486124250645)
                ·
                  refine ⟨431341835706444662074249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9201959161737486124250645 431341835706444662074249)
                  ·
                    rfl

theorem cell23_7560317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_7560317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560317 prefixEnd_7560317 := by exact prefixLift 7560317
  have htrace : WordTrace (prefixWord ++ tailWord_7560317) baseStart_7560317 baseEnd_7560317 := by
    simpa [prefixWord, tailWord_7560317, baseEnd_7560317] using wordTrace_append hprefix tailTrace_7560317
  have hstable : (prefixWord ++ tailWord_7560317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560317).length < 2 ^ (prefixWord ++ tailWord_7560317).sum := by decide
  have hdescent : baseEnd_7560317 < baseStart_7560317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560387 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 3]
def baseStart_7560387 : Nat := 118140960795 + 7560387 * 2 ^ 59
def prefixEnd_7560387 : Nat := 4983230072969 + 3 ^ 40 * 7560387 * 2
def baseEnd_7560387 : Nat := 3882112465003816684792919

theorem tailTrace_7560387 : CollatzResearch.WordTrace tailWord_7560387 prefixEnd_7560387 3882112465003816684792919 := by
  unfold tailWord_7560387
  simp only [CollatzResearch.WordTrace]
  refine ⟨275749967661016585146127415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183833311774011056764084943 275749967661016585146127415)
  ·
    refine ⟨413624951491524877719191123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275749967661016585146127415 413624951491524877719191123)
    ·
      refine ⟨620437427237287316578786685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413624951491524877719191123 620437427237287316578786685)
      ·
        refine ⟨232664035213982743717045007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620437427237287316578786685 232664035213982743717045007)
        ·
          refine ⟨348996052820974115575567511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232664035213982743717045007 348996052820974115575567511)
          ·
            refine ⟨523494079231461173363351267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348996052820974115575567511 523494079231461173363351267)
            ·
              refine ⟨785241118847191760045026901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523494079231461173363351267 785241118847191760045026901)
              ·
                refine ⟨9202044361490528438027659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 785241118847191760045026901 9202044361490528438027659)
                ·
                  refine ⟨13803066542235792657041489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9202044361490528438027659 13803066542235792657041489)
                  ·
                    refine ⟨10352299906676844492781117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13803066542235792657041489 10352299906676844492781117)
                    ·
                      refine ⟨3882112465003816684792919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10352299906676844492781117 3882112465003816684792919)
                      ·
                        rfl

theorem cell23_7560387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_7560387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560387 prefixEnd_7560387 := by exact prefixLift 7560387
  have htrace : WordTrace (prefixWord ++ tailWord_7560387) baseStart_7560387 baseEnd_7560387 := by
    simpa [prefixWord, tailWord_7560387, baseEnd_7560387] using wordTrace_append hprefix tailTrace_7560387
  have hstable : (prefixWord ++ tailWord_7560387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560387).length < 2 ^ (prefixWord ++ tailWord_7560387).sum := by decide
  have hdescent : baseEnd_7560387 < baseStart_7560387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560401 : List Nat := [1, 2, 2, 1, 2, 2, 1, 7, 1, 2, 2]
def baseStart_7560401 : Nat := 118140960795 + 7560401 * 2 ^ 59
def prefixEnd_7560401 : Nat := 4983230072969 + 3 ^ 40 * 7560401 * 2
def baseEnd_7560401 : Nat := 3882119653732979630017855

theorem tailTrace_7560401 : CollatzResearch.WordTrace tailWord_7560401 prefixEnd_7560401 3882119653732979630017855 := by
  unfold tailWord_7560401
  simp only [CollatzResearch.WordTrace]
  refine ⟨275750478282965865537137057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183833652188643910358091371 275750478282965865537137057)
  ·
    refine ⟨206812858712224399152852793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275750478282965865537137057 206812858712224399152852793)
    ·
      refine ⟨155109644034168299364639595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206812858712224399152852793 155109644034168299364639595)
      ·
        refine ⟨232664466051252449046959393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155109644034168299364639595 232664466051252449046959393)
        ·
          refine ⟨174498349538439336785219545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232664466051252449046959393 174498349538439336785219545)
          ·
            refine ⟨130873762153829502588914659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174498349538439336785219545 130873762153829502588914659)
            ·
              refine ⟨196310643230744253883371989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130873762153829502588914659 196310643230744253883371989)
              ·
                refine ⟨4601030700720568450391531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 196310643230744253883371989 4601030700720568450391531)
                ·
                  refine ⟨6901546051080852675587297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601030700720568450391531 6901546051080852675587297)
                  ·
                    refine ⟨5176159538310639506690473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6901546051080852675587297 5176159538310639506690473)
                    ·
                      refine ⟨3882119653732979630017855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5176159538310639506690473 3882119653732979630017855)
                      ·
                        rfl

theorem cell23_7560401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_7560401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560401 prefixEnd_7560401 := by exact prefixLift 7560401
  have htrace : WordTrace (prefixWord ++ tailWord_7560401) baseStart_7560401 baseEnd_7560401 := by
    simpa [prefixWord, tailWord_7560401, baseEnd_7560401] using wordTrace_append hprefix tailTrace_7560401
  have hstable : (prefixWord ++ tailWord_7560401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560401).length < 2 ^ (prefixWord ++ tailWord_7560401).sum := by decide
  have hdescent : baseEnd_7560401 < baseStart_7560401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560420 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_7560420 : Nat := 118140960795 + 7560420 * 2 ^ 59
def prefixEnd_7560420 : Nat := 4983230072969 + 3 ^ 40 * 7560420 * 2
def baseEnd_7560420 : Nat := 1294043136621805018560089

theorem tailTrace_7560420 : CollatzResearch.WordTrace tailWord_7560420 prefixEnd_7560420 1294043136621805018560089 := by
  unfold tailWord_7560420
  simp only [CollatzResearch.WordTrace]
  refine ⟨137875585634948515891039357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183834114179931354521385809 137875585634948515891039357)
  ·
    refine ⟨51703344613105693459139759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137875585634948515891039357 51703344613105693459139759)
    ·
      refine ⟨77555016919658540188709639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51703344613105693459139759 77555016919658540188709639)
      ·
        refine ⟨116332525379487810283064459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77555016919658540188709639 116332525379487810283064459)
        ·
          refine ⟨174498788069231715424596689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116332525379487810283064459 174498788069231715424596689)
          ·
            refine ⟨130874091051923786568447517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174498788069231715424596689 130874091051923786568447517)
            ·
              refine ⟨49077784144471419963167819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130874091051923786568447517 49077784144471419963167819)
              ·
                refine ⟨73616676216707129944751729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49077784144471419963167819 73616676216707129944751729)
                ·
                  refine ⟨55212507162530347458563797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73616676216707129944751729 55212507162530347458563797)
                  ·
                    refine ⟨1294043136621805018560089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55212507162530347458563797 1294043136621805018560089)
                    ·
                      rfl

theorem cell23_7560420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_7560420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560420 prefixEnd_7560420 := by exact prefixLift 7560420
  have htrace : WordTrace (prefixWord ++ tailWord_7560420) baseStart_7560420 baseEnd_7560420 := by
    simpa [prefixWord, tailWord_7560420, baseEnd_7560420] using wordTrace_append hprefix tailTrace_7560420
  have hstable : (prefixWord ++ tailWord_7560420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560420).length < 2 ^ (prefixWord ++ tailWord_7560420).sum := by decide
  have hdescent : baseEnd_7560420 < baseStart_7560420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560497 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 7]
def baseStart_7560497 : Nat := 118140960795 + 7560497 * 2 ^ 59
def prefixEnd_7560497 : Nat := 4983230072969 + 3 ^ 40 * 7560497 * 2
def baseEnd_7560497 : Nat := 431352105319534583824157

theorem tailTrace_7560497 : CollatzResearch.WordTrace tailWord_7560497 prefixEnd_7560497 431352105319534583824157 := by
  unfold tailWord_7560497
  simp only [CollatzResearch.WordTrace]
  refine ⟨275753979690618073932631745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183835986460412049288421163 275753979690618073932631745)
  ·
    refine ⟨206815484767963555449473809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275753979690618073932631745 206815484767963555449473809)
    ·
      refine ⟨155111613575972666587105357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206815484767963555449473809 155111613575972666587105357)
      ·
        refine ⟨58166855090989749970164509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155111613575972666587105357 58166855090989749970164509)
        ·
          refine ⟨21812570659121156238811691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58166855090989749970164509 21812570659121156238811691)
          ·
            refine ⟨32718855988681734358217537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21812570659121156238811691 32718855988681734358217537)
            ·
              refine ⟨24539141991511300768663153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32718855988681734358217537 24539141991511300768663153)
              ·
                refine ⟨18404356493633475576497365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24539141991511300768663153 18404356493633475576497365)
                ·
                  refine ⟨431352105319534583824157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18404356493633475576497365 431352105319534583824157)
                  ·
                    rfl

theorem cell23_7560497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 7].length) (baseStart_7560497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560497 prefixEnd_7560497 := by exact prefixLift 7560497
  have htrace : WordTrace (prefixWord ++ tailWord_7560497) baseStart_7560497 baseEnd_7560497 := by
    simpa [prefixWord, tailWord_7560497, baseEnd_7560497] using wordTrace_append hprefix tailTrace_7560497
  have hstable : (prefixWord ++ tailWord_7560497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560497).length < 2 ^ (prefixWord ++ tailWord_7560497).sum := by decide
  have hdescent : baseEnd_7560497 < baseStart_7560497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560648 : List Nat := [2, 1, 3, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_7560648 : Nat := 118140960795 + 7560648 * 2 ^ 59
def prefixEnd_7560648 : Nat := 4983230072969 + 3 ^ 40 * 7560648 * 2
def baseEnd_7560648 : Nat := 3882246483454640163629219

theorem tailTrace_7560648 : CollatzResearch.WordTrace tailWord_7560648 prefixEnd_7560648 3882246483454640163629219 := by
  unfold tailWord_7560648
  simp only [CollatzResearch.WordTrace]
  refine ⟨137879743556535513360689299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183839658075380684480919065 137879743556535513360689299)
  ·
    refine ⟨206819615334803270041033949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137879743556535513360689299 206819615334803270041033949)
    ·
      refine ⟨77557355750551226265387731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206819615334803270041033949 77557355750551226265387731)
      ·
        refine ⟨116336033625826839398081597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77557355750551226265387731 116336033625826839398081597)
        ·
          refine ⟨43626012609685064774280599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116336033625826839398081597 43626012609685064774280599)
          ·
            refine ⟨65439018914527597161420899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43626012609685064774280599 65439018914527597161420899)
            ·
              refine ⟨98158528371791395742131349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65439018914527597161420899 98158528371791395742131349)
              ·
                refine ⟨4601181017427721675412407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98158528371791395742131349 4601181017427721675412407)
                ·
                  refine ⟨6901771526141582513118611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601181017427721675412407 6901771526141582513118611)
                  ·
                    refine ⟨10352657289212373769677917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6901771526141582513118611 10352657289212373769677917)
                    ·
                      refine ⟨3882246483454640163629219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10352657289212373769677917 3882246483454640163629219)
                      ·
                        rfl

theorem cell23_7560648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_7560648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560648 prefixEnd_7560648 := by exact prefixLift 7560648
  have htrace : WordTrace (prefixWord ++ tailWord_7560648) baseStart_7560648 baseEnd_7560648 := by
    simpa [prefixWord, tailWord_7560648, baseEnd_7560648] using wordTrace_append hprefix tailTrace_7560648
  have hstable : (prefixWord ++ tailWord_7560648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560648).length < 2 ^ (prefixWord ++ tailWord_7560648).sum := by decide
  have hdescent : baseEnd_7560648 < baseStart_7560648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560654 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_7560654 : Nat := 118140960795 + 7560654 * 2 ^ 59
def prefixEnd_7560654 : Nat := 4983230072969 + 3 ^ 40 * 7560654 * 2
def baseEnd_7560654 : Nat := 3882249564338567140154191

theorem tailTrace_7560654 : CollatzResearch.WordTrace tailWord_7560654 prefixEnd_7560654 3882249564338567140154191 := by
  unfold tailWord_7560654
  simp only [CollatzResearch.WordTrace]
  refine ⟨34469963243881161218262127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183839803967366193164064677 34469963243881161218262127)
  ·
    refine ⟨51704944865821741827393191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34469963243881161218262127 51704944865821741827393191)
    ·
      refine ⟨77557417298732612741089787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51704944865821741827393191 77557417298732612741089787)
      ·
        refine ⟨116336125948098919111634681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77557417298732612741089787 116336125948098919111634681)
        ·
          refine ⟨87252094461074189333726011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116336125948098919111634681 87252094461074189333726011)
          ·
            refine ⟨130878141691611284000589017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87252094461074189333726011 130878141691611284000589017)
            ·
              refine ⟨98158606268708463000441763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130878141691611284000589017 98158606268708463000441763)
              ·
                refine ⟨147237909403062694500662645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98158606268708463000441763 147237909403062694500662645)
                ·
                  refine ⟨13803554006537127609437123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147237909403062694500662645 13803554006537127609437123)
                  ·
                    refine ⟨20705331009805691414155685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13803554006537127609437123 20705331009805691414155685)
                    ·
                      refine ⟨3882249564338567140154191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20705331009805691414155685 3882249564338567140154191)
                      ·
                        rfl

theorem cell23_7560654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_7560654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560654 prefixEnd_7560654 := by exact prefixLift 7560654
  have htrace : WordTrace (prefixWord ++ tailWord_7560654) baseStart_7560654 baseEnd_7560654 := by
    simpa [prefixWord, tailWord_7560654, baseEnd_7560654] using wordTrace_append hprefix tailTrace_7560654
  have hstable : (prefixWord ++ tailWord_7560654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560654).length < 2 ^ (prefixWord ++ tailWord_7560654).sum := by decide
  have hdescent : baseEnd_7560654 < baseStart_7560654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560664 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 1, 6]
def baseStart_7560664 : Nat := 118140960795 + 7560664 * 2 ^ 59
def prefixEnd_7560664 : Nat := 4983230072969 + 3 ^ 40 * 7560664 * 2
def baseEnd_7560664 : Nat := 1294084899715037367009715

theorem tailTrace_7560664 : CollatzResearch.WordTrace tailWord_7560664 prefixEnd_7560664 1294084899715037367009715 := by
  unfold tailWord_7560664
  simp only [CollatzResearch.WordTrace]
  refine ⟨137880035340506530726980523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183840047120675374302640697 137880035340506530726980523)
  ·
    refine ⟨206820053010759796090470785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137880035340506530726980523 206820053010759796090470785)
    ·
      refine ⟨155115039758069847067853089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206820053010759796090470785 155115039758069847067853089)
      ·
        refine ⟨116336279818552385300889817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155115039758069847067853089 116336279818552385300889817)
        ·
          refine ⟨87252209863914288975667363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116336279818552385300889817 87252209863914288975667363)
          ·
            refine ⟨130878314795871433463501045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87252209863914288975667363 130878314795871433463501045)
            ·
              refine ⟨12269842012112946887203223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130878314795871433463501045 12269842012112946887203223)
              ·
                refine ⟨18404763018169420330804835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12269842012112946887203223 18404763018169420330804835)
                ·
                  refine ⟨27607144527254130496207253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18404763018169420330804835 27607144527254130496207253)
                  ·
                    refine ⟨1294084899715037367009715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27607144527254130496207253 1294084899715037367009715)
                    ·
                      rfl

theorem cell23_7560664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_7560664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560664 prefixEnd_7560664 := by exact prefixLift 7560664
  have htrace : WordTrace (prefixWord ++ tailWord_7560664) baseStart_7560664 baseEnd_7560664 := by
    simpa [prefixWord, tailWord_7560664, baseEnd_7560664] using wordTrace_append hprefix tailTrace_7560664
  have hstable : (prefixWord ++ tailWord_7560664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560664).length < 2 ^ (prefixWord ++ tailWord_7560664).sum := by decide
  have hdescent : baseEnd_7560664 < baseStart_7560664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560667 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 4]
def baseStart_7560667 : Nat := 118140960795 + 7560667 * 2 ^ 59
def prefixEnd_7560667 : Nat := 4983230072969 + 3 ^ 40 * 7560667 * 2
def baseEnd_7560667 : Nat := 3882256239587075589291631

theorem tailTrace_7560667 : CollatzResearch.WordTrace tailWord_7560667 prefixEnd_7560667 3882256239587075589291631 := by
  unfold tailWord_7560667
  simp only [CollatzResearch.WordTrace]
  refine ⟨275760180100002192966320255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183840120066668128644213503 275760180100002192966320255)
  ·
    refine ⟨413640270150003289449480383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275760180100002192966320255 413640270150003289449480383)
    ·
      refine ⟨620460405225004934174220575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413640270150003289449480383 620460405225004934174220575)
      ·
        refine ⟨930690607837507401261330863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620460405225004934174220575 930690607837507401261330863)
        ·
          refine ⟨1396035911756261101891996295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930690607837507401261330863 1396035911756261101891996295)
          ·
            refine ⟨2094053867634391652837994443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396035911756261101891996295 2094053867634391652837994443)
            ·
              refine ⟨3141080801451587479256991665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094053867634391652837994443 3141080801451587479256991665)
              ·
                refine ⟨2355810601088690609442743749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141080801451587479256991665 2355810601088690609442743749)
                ·
                  refine ⟨441714487704129489270514453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2355810601088690609442743749 441714487704129489270514453)
                  ·
                    refine ⟨20705366611131069809555365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 441714487704129489270514453 20705366611131069809555365)
                    ·
                      refine ⟨3882256239587075589291631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20705366611131069809555365 3882256239587075589291631)
                      ·
                        rfl

theorem cell23_7560667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 4].length) (baseStart_7560667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560667 prefixEnd_7560667 := by exact prefixLift 7560667
  have htrace : WordTrace (prefixWord ++ tailWord_7560667) baseStart_7560667 baseEnd_7560667 := by
    simpa [prefixWord, tailWord_7560667, baseEnd_7560667] using wordTrace_append hprefix tailTrace_7560667
  have hstable : (prefixWord ++ tailWord_7560667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560667).length < 2 ^ (prefixWord ++ tailWord_7560667).sum := by decide
  have hdescent : baseEnd_7560667 < baseStart_7560667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560671 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 4]
def baseStart_7560671 : Nat := 118140960795 + 7560671 * 2 ^ 59
def prefixEnd_7560671 : Nat := 4983230072969 + 3 ^ 40 * 7560671 * 2
def baseEnd_7560671 : Nat := 3882258293509693573641613

theorem tailTrace_7560671 : CollatzResearch.WordTrace tailWord_7560671 prefixEnd_7560671 3882258293509693573641613 := by
  unfold tailWord_7560671
  simp only [CollatzResearch.WordTrace]
  refine ⟨275760325991987701649465867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183840217327991801099643911 275760325991987701649465867)
  ·
    refine ⟨413640488987981552474198801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275760325991987701649465867 413640488987981552474198801)
    ·
      refine ⟨310230366740986164355649101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413640488987981552474198801 310230366740986164355649101)
      ·
        refine ⟨116336387527869811633368413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310230366740986164355649101 116336387527869811633368413)
        ·
          refine ⟨43626145322951179362513155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116336387527869811633368413 43626145322951179362513155)
          ·
            refine ⟨65439217984426769043769733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43626145322951179362513155 65439217984426769043769733)
            ·
              refine ⟨12269853372080019195706825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65439217984426769043769733 12269853372080019195706825)
              ·
                refine ⟨9202390029060014396780119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12269853372080019195706825 9202390029060014396780119)
                ·
                  refine ⟨13803585043590021595170179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9202390029060014396780119 13803585043590021595170179)
                  ·
                    refine ⟨20705377565385032392755269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13803585043590021595170179 20705377565385032392755269)
                    ·
                      refine ⟨3882258293509693573641613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20705377565385032392755269 3882258293509693573641613)
                      ·
                        rfl

theorem cell23_7560671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_7560671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560671 prefixEnd_7560671 := by exact prefixLift 7560671
  have htrace : WordTrace (prefixWord ++ tailWord_7560671) baseStart_7560671 baseEnd_7560671 := by
    simpa [prefixWord, tailWord_7560671, baseEnd_7560671] using wordTrace_append hprefix tailTrace_7560671
  have hstable : (prefixWord ++ tailWord_7560671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560671).length < 2 ^ (prefixWord ++ tailWord_7560671).sum := by decide
  have hdescent : baseEnd_7560671 < baseStart_7560671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560682 : List Nat := [3, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_7560682 : Nat := 118140960795 + 7560682 * 2 ^ 59
def prefixEnd_7560682 : Nat := 4983230072969 + 3 ^ 40 * 7560682 * 2
def baseEnd_7560682 : Nat := 3882263941796893030604063

theorem tailTrace_7560682 : CollatzResearch.WordTrace tailWord_7560682 prefixEnd_7560682 3882263941796893030604063 := by
  unfold tailWord_7560682
  simp only [CollatzResearch.WordTrace]
  refine ⟨68940181798736962632029075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183840484796631900352077533 68940181798736962632029075)
  ·
    refine ⟨103410272698105443948043613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68940181798736962632029075 103410272698105443948043613)
    ·
      refine ⟨38778852261789541480516355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103410272698105443948043613 38778852261789541480516355)
      ·
        refine ⟨58168278392684312220774533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38778852261789541480516355 58168278392684312220774533)
        ·
          refine ⟨10906552198628308541395225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58168278392684312220774533 10906552198628308541395225)
          ·
            refine ⟨8179914148971231406046419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10906552198628308541395225 8179914148971231406046419)
            ·
              refine ⟨12269871223456847109069629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8179914148971231406046419 12269871223456847109069629)
              ·
                refine ⟨4601201708796317665901111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12269871223456847109069629 4601201708796317665901111)
                ·
                  refine ⟨6901802563194476498851667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601201708796317665901111 6901802563194476498851667)
                  ·
                    refine ⟨10352703844791714748277501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6901802563194476498851667 10352703844791714748277501)
                    ·
                      refine ⟨3882263941796893030604063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10352703844791714748277501 3882263941796893030604063)
                      ·
                        rfl

theorem cell23_7560682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_7560682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560682 prefixEnd_7560682 := by exact prefixLift 7560682
  have htrace : WordTrace (prefixWord ++ tailWord_7560682) baseStart_7560682 baseEnd_7560682 := by
    simpa [prefixWord, tailWord_7560682, baseEnd_7560682] using wordTrace_append hprefix tailTrace_7560682
  have hstable : (prefixWord ++ tailWord_7560682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560682).length < 2 ^ (prefixWord ++ tailWord_7560682).sum := by decide
  have hdescent : baseEnd_7560682 < baseStart_7560682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560694 : List Nat := [5, 1, 1, 1, 2, 2, 11]
def baseStart_7560694 : Nat := 118140960795 + 7560694 * 2 ^ 59
def prefixEnd_7560694 : Nat := 4983230072969 + 3 ^ 40 * 7560694 * 2
def baseEnd_7560694 : Nat := 47929260537836382514247

theorem tailTrace_7560694 : CollatzResearch.WordTrace tailWord_7560694 prefixEnd_7560694 47929260537836382514247 := by
  unfold tailWord_7560694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17235072804431523536097071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183840776580602917718368757 17235072804431523536097071)
  ·
    refine ⟨25852609206647285304145607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17235072804431523536097071 25852609206647285304145607)
    ·
      refine ⟨38778913809970927956218411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25852609206647285304145607 38778913809970927956218411)
      ·
        refine ⟨58168370714956391934327617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38778913809970927956218411 58168370714956391934327617)
        ·
          refine ⟨43626278036217293950745713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58168370714956391934327617 43626278036217293950745713)
          ·
            refine ⟨32719708527162970463059285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43626278036217293950745713 32719708527162970463059285)
            ·
              refine ⟨47929260537836382514247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32719708527162970463059285 47929260537836382514247)
              ·
                rfl

theorem cell23_7560694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 11].length) (baseStart_7560694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560694 prefixEnd_7560694 := by exact prefixLift 7560694
  have htrace : WordTrace (prefixWord ++ tailWord_7560694) baseStart_7560694 baseEnd_7560694 := by
    simpa [prefixWord, tailWord_7560694, baseEnd_7560694] using wordTrace_append hprefix tailTrace_7560694
  have hstable : (prefixWord ++ tailWord_7560694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560694).length < 2 ^ (prefixWord ++ tailWord_7560694).sum := by decide
  have hdescent : baseEnd_7560694 < baseStart_7560694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560715 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 2, 4]
def baseStart_7560715 : Nat := 118140960795 + 7560715 * 2 ^ 59
def prefixEnd_7560715 : Nat := 4983230072969 + 3 ^ 40 * 7560715 * 2
def baseEnd_7560715 : Nat := 1294093628886163800497137

theorem tailTrace_7560715 : CollatzResearch.WordTrace tailWord_7560715 prefixEnd_7560715 1294093628886163800497137 := by
  unfold tailWord_7560715
  simp only [CollatzResearch.WordTrace]
  refine ⟨275761930803828297164067599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183841287202552198109378399 275761930803828297164067599)
  ·
    refine ⟨413642896205742445746101399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275761930803828297164067599 413642896205742445746101399)
    ·
      refine ⟨620464344308613668619152099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413642896205742445746101399 620464344308613668619152099)
      ·
        refine ⟨930696516462920502928728149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620464344308613668619152099 930696516462920502928728149)
        ·
          refine ⟨10906599802299849643696033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 930696516462920502928728149 10906599802299849643696033)
          ·
            refine ⟨8179949851724887232772025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10906599802299849643696033 8179949851724887232772025)
            ·
              refine ⟨6134962388793665424579019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8179949851724887232772025 6134962388793665424579019)
              ·
                refine ⟨9202443583190498136868529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6134962388793665424579019 9202443583190498136868529)
                ·
                  refine ⟨6901832687392873602651397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9202443583190498136868529 6901832687392873602651397)
                  ·
                    refine ⟨1294093628886163800497137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6901832687392873602651397 1294093628886163800497137)
                    ·
                      rfl

theorem cell23_7560715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 4].length) (baseStart_7560715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560715 prefixEnd_7560715 := by exact prefixLift 7560715
  have htrace : WordTrace (prefixWord ++ tailWord_7560715) baseStart_7560715 baseEnd_7560715 := by
    simpa [prefixWord, tailWord_7560715, baseEnd_7560715] using wordTrace_append hprefix tailTrace_7560715
  have hstable : (prefixWord ++ tailWord_7560715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560715).length < 2 ^ (prefixWord ++ tailWord_7560715).sum := by decide
  have hdescent : baseEnd_7560715 < baseStart_7560715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560754 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_7560754 : Nat := 118140960795 + 7560754 * 2 ^ 59
def prefixEnd_7560754 : Nat := 4983230072969 + 3 ^ 40 * 7560754 * 2
def baseEnd_7560754 : Nat := 1294100304134672249634577

theorem tailTrace_7560754 : CollatzResearch.WordTrace tailWord_7560754 prefixEnd_7560754 1294100304134672249634577 := by
  unfold tailWord_7560754
  simp only [CollatzResearch.WordTrace]
  refine ⟨68940838312671751706184329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183842235500458004549824877 68940838312671751706184329)
  ·
    refine ⟨51705628734503813779638247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68940838312671751706184329 51705628734503813779638247)
    ·
      refine ⟨77558443101755720669457371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51705628734503813779638247 77558443101755720669457371)
      ·
        refine ⟨116337664652633581004186057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77558443101755720669457371 116337664652633581004186057)
        ·
          refine ⟨87253248489475185753139543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116337664652633581004186057 87253248489475185753139543)
          ·
            refine ⟨130879872734212778629709315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87253248489475185753139543 130879872734212778629709315)
            ·
              refine ⟨196319809101319167944563973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130879872734212778629709315 196319809101319167944563973)
              ·
                refine ⟨36809964206497343989605745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196319809101319167944563973 36809964206497343989605745)
                ·
                  refine ⟨27607473154873007992204309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36809964206497343989605745 27607473154873007992204309)
                  ·
                    refine ⟨1294100304134672249634577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27607473154873007992204309 1294100304134672249634577)
                    ·
                      rfl

theorem cell23_7560754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_7560754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560754 prefixEnd_7560754 := by exact prefixLift 7560754
  have htrace : WordTrace (prefixWord ++ tailWord_7560754) baseStart_7560754 baseEnd_7560754 := by
    simpa [prefixWord, tailWord_7560754, baseEnd_7560754] using wordTrace_append hprefix tailTrace_7560754
  have hstable : (prefixWord ++ tailWord_7560754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560754).length < 2 ^ (prefixWord ++ tailWord_7560754).sum := by decide
  have hdescent : baseEnd_7560754 < baseStart_7560754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560778 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_7560778 : Nat := 118140960795 + 7560778 * 2 ^ 59
def prefixEnd_7560778 : Nat := 4983230072969 + 3 ^ 40 * 7560778 * 2
def baseEnd_7560778 : Nat := 3882313235939724655003621

theorem tailTrace_7560778 : CollatzResearch.WordTrace tailWord_7560778 prefixEnd_7560778 3882313235939724655003621 := by
  unfold tailWord_7560778
  simp only [CollatzResearch.WordTrace]
  refine ⟨68941057150650014730902747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183842819068400039282407325 68941057150650014730902747)
  ·
    refine ⟨103411585725975022096354121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68941057150650014730902747 103411585725975022096354121)
    ·
      refine ⟨77558689294481266572265591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103411585725975022096354121 77558689294481266572265591)
      ·
        refine ⟨116338033941721899858398387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77558689294481266572265591 116338033941721899858398387)
        ·
          refine ⟨174507050912582849787597581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116338033941721899858398387 174507050912582849787597581)
          ·
            refine ⟨65440144092218568670349093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174507050912582849787597581 65440144092218568670349093)
            ·
              refine ⟨12270027017290981625690455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65440144092218568670349093 12270027017290981625690455)
              ·
                refine ⟨18405040525936472438535683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12270027017290981625690455 18405040525936472438535683)
                ·
                  refine ⟨27607560788904708657803525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18405040525936472438535683 27607560788904708657803525)
                  ·
                    refine ⟨5176417647919632873338161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27607560788904708657803525 5176417647919632873338161)
                    ·
                      refine ⟨3882313235939724655003621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5176417647919632873338161 3882313235939724655003621)
                      ·
                        rfl

theorem cell23_7560778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_7560778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560778 prefixEnd_7560778 := by exact prefixLift 7560778
  have htrace : WordTrace (prefixWord ++ tailWord_7560778) baseStart_7560778 baseEnd_7560778 := by
    simpa [prefixWord, tailWord_7560778, baseEnd_7560778] using wordTrace_append hprefix tailTrace_7560778
  have hstable : (prefixWord ++ tailWord_7560778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560778).length < 2 ^ (prefixWord ++ tailWord_7560778).sum := by decide
  have hdescent : baseEnd_7560778 < baseStart_7560778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560784 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 7]
def baseStart_7560784 : Nat := 118140960795 + 7560784 * 2 ^ 59
def prefixEnd_7560784 : Nat := 4983230072969 + 3 ^ 40 * 7560784 * 2
def baseEnd_7560784 : Nat := 431368479647072403503177

theorem tailTrace_7560784 : CollatzResearch.WordTrace tailWord_7560784 prefixEnd_7560784 431368479647072403503177 := by
  unfold tailWord_7560784
  simp only [CollatzResearch.WordTrace]
  refine ⟨137882223720289160974164703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183842964960385547965552937 137882223720289160974164703)
  ·
    refine ⟨206823335580433741461247055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137882223720289160974164703 206823335580433741461247055)
    ·
      refine ⟨310235003370650612191870583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206823335580433741461247055 310235003370650612191870583)
      ·
        refine ⟨465352505055975918287805875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310235003370650612191870583 465352505055975918287805875)
        ·
          refine ⟨698028757583963877431708813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465352505055975918287805875 698028757583963877431708813)
          ·
            refine ⟨261760784093986454036890805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 698028757583963877431708813 261760784093986454036890805)
            ·
              refine ⟨24540073508811230065958513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261760784093986454036890805 24540073508811230065958513)
              ·
                refine ⟨18405055131608422549468885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24540073508811230065958513 18405055131608422549468885)
                ·
                  refine ⟨431368479647072403503177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18405055131608422549468885 431368479647072403503177)
                  ·
                    rfl

theorem cell23_7560784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 7].length) (baseStart_7560784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560784 prefixEnd_7560784 := by exact prefixLift 7560784
  have htrace : WordTrace (prefixWord ++ tailWord_7560784) baseStart_7560784 baseEnd_7560784 := by
    simpa [prefixWord, tailWord_7560784, baseEnd_7560784] using wordTrace_append hprefix tailTrace_7560784
  have hstable : (prefixWord ++ tailWord_7560784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560784).length < 2 ^ (prefixWord ++ tailWord_7560784).sum := by decide
  have hdescent : baseEnd_7560784 < baseStart_7560784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560818 : List Nat := [3, 2, 1, 2, 3, 1, 2, 4, 5]
def baseStart_7560818 : Nat := 118140960795 + 7560818 * 2 ^ 59
def prefixEnd_7560818 : Nat := 4983230072969 + 3 ^ 40 * 7560818 * 2
def baseEnd_7560818 : Nat := 431370419462878277611493

theorem tailTrace_7560818 : CollatzResearch.WordTrace tailWord_7560818 prefixEnd_7560818 431370419462878277611493 := by
  unfold tailWord_7560818
  simp only [CollatzResearch.WordTrace]
  refine ⟨68941421880613786438766777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183843791681636763836711405 68941421880613786438766777)
  ·
    refine ⟨51706066410460339829075083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68941421880613786438766777 51706066410460339829075083)
    ·
      refine ⟨77559099615690509743612625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51706066410460339829075083 77559099615690509743612625)
      ·
        refine ⟨58169324711767882307709469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77559099615690509743612625 58169324711767882307709469)
        ·
          refine ⟨21813496766912955865391051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58169324711767882307709469 21813496766912955865391051)
          ·
            refine ⟨32720245150369433798086577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21813496766912955865391051 32720245150369433798086577)
            ·
              refine ⟨24540183862777075348564933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32720245150369433798086577 24540183862777075348564933)
              ·
                refine ⟨4601284474270701627855925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24540183862777075348564933 4601284474270701627855925)
                ·
                  refine ⟨431370419462878277611493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4601284474270701627855925 431370419462878277611493)
                  ·
                    rfl

theorem cell23_7560818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_7560818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560818 prefixEnd_7560818 := by exact prefixLift 7560818
  have htrace : WordTrace (prefixWord ++ tailWord_7560818) baseStart_7560818 baseEnd_7560818 := by
    simpa [prefixWord, tailWord_7560818, baseEnd_7560818] using wordTrace_append hprefix tailTrace_7560818
  have hstable : (prefixWord ++ tailWord_7560818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560818).length < 2 ^ (prefixWord ++ tailWord_7560818).sum := by decide
  have hdescent : baseEnd_7560818 < baseStart_7560818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560844 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_7560844 : Nat := 118140960795 + 7560844 * 2 ^ 59
def prefixEnd_7560844 : Nat := 4983230072969 + 3 ^ 40 * 7560844 * 2
def baseEnd_7560844 : Nat := 1294115708554307132259439

theorem tailTrace_7560844 : CollatzResearch.WordTrace tailWord_7560844 prefixEnd_7560844 1294115708554307132259439 := by
  unfold tailWord_7560844
  simp only [CollatzResearch.WordTrace]
  refine ⟨137883317910180476097756793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183844423880240634797009057 137883317910180476097756793)
  ·
    refine ⟨103412488432635357073317595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137883317910180476097756793 103412488432635357073317595)
    ·
      refine ⟨155118732648953035609976393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103412488432635357073317595 155118732648953035609976393)
      ·
        refine ⟨116339049486714776707482295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155118732648953035609976393 116339049486714776707482295)
        ·
          refine ⟨174508574230072165061223443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116339049486714776707482295 174508574230072165061223443)
          ·
            refine ⟨261762861345108247591835165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174508574230072165061223443 261762861345108247591835165)
            ·
              refine ⟨98161073004415592846938187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261762861345108247591835165 98161073004415592846938187)
              ·
                refine ⟨147241609506623389270407281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98161073004415592846938187 147241609506623389270407281)
                ·
                  refine ⟨110431207129967541952805461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147241609506623389270407281 110431207129967541952805461)
                  ·
                    refine ⟨1294115708554307132259439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110431207129967541952805461 1294115708554307132259439)
                    ·
                      rfl

theorem cell23_7560844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_7560844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560844 prefixEnd_7560844 := by exact prefixLift 7560844
  have htrace : WordTrace (prefixWord ++ tailWord_7560844) baseStart_7560844 baseEnd_7560844 := by
    simpa [prefixWord, tailWord_7560844, baseEnd_7560844] using wordTrace_append hprefix tailTrace_7560844
  have hstable : (prefixWord ++ tailWord_7560844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560844).length < 2 ^ (prefixWord ++ tailWord_7560844).sum := by decide
  have hdescent : baseEnd_7560844 < baseStart_7560844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560852 : List Nat := [2, 4, 2, 2, 2, 2, 1, 3, 5]
def baseStart_7560852 : Nat := 118140960795 + 7560852 * 2 ^ 59
def prefixEnd_7560852 : Nat := 4983230072969 + 3 ^ 40 * 7560852 * 2
def baseEnd_7560852 : Nat := 431372359278684151719809

theorem tailTrace_7560852 : CollatzResearch.WordTrace tailWord_7560852 prefixEnd_7560852 431372359278684151719809 := by
  unfold tailWord_7560852
  simp only [CollatzResearch.WordTrace]
  refine ⟨137883463802165984780902405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183844618402887979707869873 137883463802165984780902405)
  ·
    refine ⟨25853149462906122146419201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137883463802165984780902405 25853149462906122146419201)
    ·
      refine ⟨19389862097179591609814401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25853149462906122146419201 19389862097179591609814401)
      ·
        refine ⟨14542396572884693707360801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19389862097179591609814401 14542396572884693707360801)
        ·
          refine ⟨10906797429663520280520601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14542396572884693707360801 10906797429663520280520601)
          ·
            refine ⟨8180098072247640210390451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10906797429663520280520601 8180098072247640210390451)
            ·
              refine ⟨12270147108371460315585677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180098072247640210390451 12270147108371460315585677)
              ·
                refine ⟨4601305165639297618344629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12270147108371460315585677 4601305165639297618344629)
                ·
                  refine ⟨431372359278684151719809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4601305165639297618344629 431372359278684151719809)
                  ·
                    rfl

theorem cell23_7560852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_7560852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560852 prefixEnd_7560852 := by exact prefixLift 7560852
  have htrace : WordTrace (prefixWord ++ tailWord_7560852) baseStart_7560852 baseEnd_7560852 := by
    simpa [prefixWord, tailWord_7560852, baseEnd_7560852] using wordTrace_append hprefix tailTrace_7560852
  have hstable : (prefixWord ++ tailWord_7560852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560852).length < 2 ^ (prefixWord ++ tailWord_7560852).sum := by decide
  have hdescent : baseEnd_7560852 < baseStart_7560852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560868 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_7560868 : Nat := 118140960795 + 7560868 * 2 ^ 59
def prefixEnd_7560868 : Nat := 4983230072969 + 3 ^ 40 * 7560868 * 2
def baseEnd_7560868 : Nat := 3882359449198629302878207

theorem tailTrace_7560868 : CollatzResearch.WordTrace tailWord_7560868 prefixEnd_7560868 3882359449198629302878207 := by
  unfold tailWord_7560868
  simp only [CollatzResearch.WordTrace]
  refine ⟨137883755586137002147193629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183845007448182669529591505 137883755586137002147193629)
  ·
    refine ⟨51706408344801375805197611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137883755586137002147193629 51706408344801375805197611)
    ·
      refine ⟨77559612517202063707796417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51706408344801375805197611 77559612517202063707796417)
      ·
        refine ⟨58169709387901547780847313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77559612517202063707796417 58169709387901547780847313)
        ·
          refine ⟨43627282040926160835635485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58169709387901547780847313 43627282040926160835635485)
          ·
            refine ⟨16360230765347310313363307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43627282040926160835635485 16360230765347310313363307)
            ·
              refine ⟨24540346148020965470044961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16360230765347310313363307 24540346148020965470044961)
              ·
                refine ⟨18405259611015724102533721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24540346148020965470044961 18405259611015724102533721)
                ·
                  refine ⟨13803944708261793076900291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18405259611015724102533721 13803944708261793076900291)
                  ·
                    refine ⟨20705917062392689615350437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13803944708261793076900291 20705917062392689615350437)
                    ·
                      refine ⟨3882359449198629302878207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20705917062392689615350437 3882359449198629302878207)
                      ·
                        rfl

theorem cell23_7560868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_7560868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560868 prefixEnd_7560868 := by exact prefixLift 7560868
  have htrace : WordTrace (prefixWord ++ tailWord_7560868) baseStart_7560868 baseEnd_7560868 := by
    simpa [prefixWord, tailWord_7560868, baseEnd_7560868] using wordTrace_append hprefix tailTrace_7560868
  have hstable : (prefixWord ++ tailWord_7560868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560868).length < 2 ^ (prefixWord ++ tailWord_7560868).sum := by decide
  have hdescent : baseEnd_7560868 < baseStart_7560868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560902 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7560902 : Nat := 118140960795 + 7560902 * 2 ^ 59
def prefixEnd_7560902 : Nat := 4983230072969 + 3 ^ 40 * 7560902 * 2
def baseEnd_7560902 : Nat := 3882376907540882169853051

theorem tailTrace_7560902 : CollatzResearch.WordTrace tailWord_7560902 prefixEnd_7560902 3882376907540882169853051 := by
  unfold tailWord_7560902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8617773476692213378160155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183845834169433885400749973 8617773476692213378160155)
  ·
    refine ⟨12926660215038320067240233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8617773476692213378160155 12926660215038320067240233)
    ·
      refine ⟨9694995161278740050430175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12926660215038320067240233 9694995161278740050430175)
      ·
        refine ⟨14542492741918110075645263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9694995161278740050430175 14542492741918110075645263)
        ·
          refine ⟨21813739112877165113467895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14542492741918110075645263 21813739112877165113467895)
          ·
            refine ⟨32720608669315747670201843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21813739112877165113467895 32720608669315747670201843)
            ·
              refine ⟨49080913003973621505302765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32720608669315747670201843 49080913003973621505302765)
              ·
                refine ⟨18405342376490108064488537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49080913003973621505302765 18405342376490108064488537)
                ·
                  refine ⟨13804006782367581048366403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18405342376490108064488537 13804006782367581048366403)
                  ·
                    refine ⟨20706010173551371572549605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13804006782367581048366403 20706010173551371572549605)
                    ·
                      refine ⟨3882376907540882169853051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20706010173551371572549605 3882376907540882169853051)
                      ·
                        rfl

theorem cell23_7560902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7560902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560902 prefixEnd_7560902 := by exact prefixLift 7560902
  have htrace : WordTrace (prefixWord ++ tailWord_7560902) baseStart_7560902 baseEnd_7560902 := by
    simpa [prefixWord, tailWord_7560902, baseEnd_7560902] using wordTrace_append hprefix tailTrace_7560902
  have hstable : (prefixWord ++ tailWord_7560902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560902).length < 2 ^ (prefixWord ++ tailWord_7560902).sum := by decide
  have hdescent : baseEnd_7560902 < baseStart_7560902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560929 : List Nat := [1, 2, 3, 1, 5, 2, 2, 2, 1, 4]
def baseStart_7560929 : Nat := 118140960795 + 7560929 * 2 ^ 59
def prefixEnd_7560929 : Nat := 4983230072969 + 3 ^ 40 * 7560929 * 2
def baseEnd_7560929 : Nat := 1294130257172851188071809

theorem tailTrace_7560929 : CollatzResearch.WordTrace tailWord_7560929 prefixEnd_7560929 1294130257172851188071809 := by
  unfold tailWord_7560929
  simp only [CollatzResearch.WordTrace]
  refine ⟨275769736025053011712357841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183846490683368674474905227 275769736025053011712357841)
  ·
    refine ⟨206827302018789758784268381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275769736025053011712357841 206827302018789758784268381)
    ·
      refine ⟨77560238257046159544100643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206827302018789758784268381 77560238257046159544100643)
      ·
        refine ⟨116340357385569239316150965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77560238257046159544100643 116340357385569239316150965)
        ·
          refine ⟨10906908504897116185889153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116340357385569239316150965 10906908504897116185889153)
          ·
            refine ⟨8180181378672837139416865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10906908504897116185889153 8180181378672837139416865)
            ·
              refine ⟨6135136034004627854562649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8180181378672837139416865 6135136034004627854562649)
              ·
                refine ⟨4601352025503470890921987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6135136034004627854562649 4601352025503470890921987)
                ·
                  refine ⟨6902028038255206336382981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601352025503470890921987 6902028038255206336382981)
                  ·
                    refine ⟨1294130257172851188071809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6902028038255206336382981 1294130257172851188071809)
                    ·
                      rfl

theorem cell23_7560929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_7560929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560929 prefixEnd_7560929 := by exact prefixLift 7560929
  have htrace : WordTrace (prefixWord ++ tailWord_7560929) baseStart_7560929 baseEnd_7560929 := by
    simpa [prefixWord, tailWord_7560929, baseEnd_7560929] using wordTrace_append hprefix tailTrace_7560929
  have hstable : (prefixWord ++ tailWord_7560929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560929).length < 2 ^ (prefixWord ++ tailWord_7560929).sum := by decide
  have hdescent : baseEnd_7560929 < baseStart_7560929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560951 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 1, 6]
def baseStart_7560951 : Nat := 118140960795 + 7560951 * 2 ^ 59
def prefixEnd_7560951 : Nat := 4983230072969 + 3 ^ 40 * 7560951 * 2
def baseEnd_7560951 : Nat := 1294134022697650826046775

theorem tailTrace_7560951 : CollatzResearch.WordTrace tailWord_7560951 prefixEnd_7560951 1294134022697650826046775 := by
  unfold tailWord_7560951
  simp only [CollatzResearch.WordTrace]
  refine ⟨275770538430973309469658707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183847025620648872979772471 275770538430973309469658707)
  ·
    refine ⟨413655807646459964204488061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275770538430973309469658707 413655807646459964204488061)
    ·
      refine ⟨155120927867422486576683023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413655807646459964204488061 155120927867422486576683023)
      ·
        refine ⟨232681391801133729865024535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155120927867422486576683023 232681391801133729865024535)
        ·
          refine ⟨349022087701700594797536803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232681391801133729865024535 349022087701700594797536803)
          ·
            refine ⟨523533131552550892196305205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349022087701700594797536803 523533131552550892196305205)
            ·
              refine ⟨49081231083051646143403613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 523533131552550892196305205 49081231083051646143403613)
              ·
                refine ⟨18405461656144367303776355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49081231083051646143403613 18405461656144367303776355)
                ·
                  refine ⟨27608192484216550955664533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18405461656144367303776355 27608192484216550955664533)
                  ·
                    refine ⟨1294134022697650826046775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27608192484216550955664533 1294134022697650826046775)
                    ·
                      rfl

theorem cell23_7560951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_7560951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560951 prefixEnd_7560951 := by exact prefixLift 7560951
  have htrace : WordTrace (prefixWord ++ tailWord_7560951) baseStart_7560951 baseEnd_7560951 := by
    simpa [prefixWord, tailWord_7560951, baseEnd_7560951] using wordTrace_append hprefix tailTrace_7560951
  have hstable : (prefixWord ++ tailWord_7560951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560951).length < 2 ^ (prefixWord ++ tailWord_7560951).sum := by decide
  have hdescent : baseEnd_7560951 < baseStart_7560951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560968 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 4, 4]
def baseStart_7560968 : Nat := 118140960795 + 7560968 * 2 ^ 59
def prefixEnd_7560968 : Nat := 4983230072969 + 3 ^ 40 * 7560968 * 2
def baseEnd_7560968 : Nat := 1294136932421359637209249

theorem tailTrace_7560968 : CollatzResearch.WordTrace tailWord_7560968 prefixEnd_7560968 1294136932421359637209249 := by
  unfold tailWord_7560968
  simp only [CollatzResearch.WordTrace]
  refine ⟨137885579235955860686513779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183847438981274480915351705 137885579235955860686513779)
  ·
    refine ⟨206828368853933791029770669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137885579235955860686513779 206828368853933791029770669)
    ·
      refine ⟨77560638320225171636164001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206828368853933791029770669 77560638320225171636164001)
      ·
        refine ⟨58170478740168878727123001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77560638320225171636164001 58170478740168878727123001)
        ·
          refine ⟨43627859055126659045342251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58170478740168878727123001 43627859055126659045342251)
          ·
            refine ⟨65441788582689988568013377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43627859055126659045342251 65441788582689988568013377)
            ·
              refine ⟨49081341437017491426010033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65441788582689988568013377 49081341437017491426010033)
              ·
                refine ⟨36811006077763118569507525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49081341437017491426010033 36811006077763118569507525)
                ·
                  refine ⟨6902063639580584731782661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36811006077763118569507525 6902063639580584731782661)
                  ·
                    refine ⟨1294136932421359637209249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6902063639580584731782661 1294136932421359637209249)
                    ·
                      rfl

theorem cell23_7560968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_7560968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560968 prefixEnd_7560968 := by exact prefixLift 7560968
  have htrace : WordTrace (prefixWord ++ tailWord_7560968) baseStart_7560968 baseEnd_7560968 := by
    simpa [prefixWord, tailWord_7560968, baseEnd_7560968] using wordTrace_append hprefix tailTrace_7560968
  have hstable : (prefixWord ++ tailWord_7560968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560968).length < 2 ^ (prefixWord ++ tailWord_7560968).sum := by decide
  have hdescent : baseEnd_7560968 < baseStart_7560968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560981 : List Nat := [1, 3, 2, 1, 2, 4, 10]
def baseStart_7560981 : Nat := 118140960795 + 7560981 * 2 ^ 59
def prefixEnd_7560981 : Nat := 4983230072969 + 3 ^ 40 * 7560981 * 2
def baseEnd_7560981 : Nat := 47931079907562806923027

theorem tailTrace_7560981 : CollatzResearch.WordTrace tailWord_7560981 prefixEnd_7560981 47931079907562806923027 := by
  unfold tailWord_7560981
  simp only [CollatzResearch.WordTrace]
  refine ⟨275771632620864624593250797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183847755080576416395500531 275771632620864624593250797)
  ·
    refine ⟨103414362232824234222469049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275771632620864624593250797 103414362232824234222469049)
    ·
      refine ⟨77560771674618175666851787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103414362232824234222469049 77560771674618175666851787)
      ·
        refine ⟨116341157511927263500277681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77560771674618175666851787 116341157511927263500277681)
        ·
          refine ⟨87255868133945447625208261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116341157511927263500277681 87255868133945447625208261)
          ·
            refine ⟨16360475275114771429726549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87255868133945447625208261 16360475275114771429726549)
            ·
              refine ⟨47931079907562806923027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16360475275114771429726549 47931079907562806923027)
              ·
                rfl

theorem cell23_7560981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 10].length) (baseStart_7560981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560981 prefixEnd_7560981 := by exact prefixLift 7560981
  have htrace : WordTrace (prefixWord ++ tailWord_7560981) baseStart_7560981 baseEnd_7560981 := by
    simpa [prefixWord, tailWord_7560981, baseEnd_7560981] using wordTrace_append hprefix tailTrace_7560981
  have hstable : (prefixWord ++ tailWord_7560981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560981).length < 2 ^ (prefixWord ++ tailWord_7560981).sum := by decide
  have hdescent : baseEnd_7560981 < baseStart_7560981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7560992 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 3, 2, 2]
def baseStart_7560992 : Nat := 118140960795 + 7560992 * 2 ^ 59
def prefixEnd_7560992 : Nat := 4983230072969 + 3 ^ 40 * 7560992 * 2
def baseEnd_7560992 : Nat := 3882423120799786817727637

theorem tailTrace_7560992 : CollatzResearch.WordTrace tailWord_7560992 prefixEnd_7560992 3882423120799786817727637 := by
  unfold tailWord_7560992
  simp only [CollatzResearch.WordTrace]
  refine ⟨137886016911912386735950615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183848022549216515647934153 137886016911912386735950615)
  ·
    refine ⟨206829025367868580103925923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137886016911912386735950615 206829025367868580103925923)
    ·
      refine ⟨310243538051802870155888885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206829025367868580103925923 310243538051802870155888885)
      ·
        refine ⟨29085331692356519077114583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310243538051802870155888885 29085331692356519077114583)
        ·
          refine ⟨43627997538534778615671875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29085331692356519077114583 43627997538534778615671875)
          ·
            refine ⟨65441996307802167923507813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43627997538534778615671875 65441996307802167923507813)
            ·
              refine ⟨12270374307712906485657715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65441996307802167923507813 12270374307712906485657715)
              ·
                refine ⟨18405561461569359728486573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12270374307712906485657715 18405561461569359728486573)
                ·
                  refine ⟨6902085548088509898182465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18405561461569359728486573 6902085548088509898182465)
                  ·
                    refine ⟨5176564161066382423636849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6902085548088509898182465 5176564161066382423636849)
                    ·
                      refine ⟨3882423120799786817727637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5176564161066382423636849 3882423120799786817727637)
                      ·
                        rfl

theorem cell23_7560992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_7560992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7560992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7560992 prefixEnd_7560992 := by exact prefixLift 7560992
  have htrace : WordTrace (prefixWord ++ tailWord_7560992) baseStart_7560992 baseEnd_7560992 := by
    simpa [prefixWord, tailWord_7560992, baseEnd_7560992] using wordTrace_append hprefix tailTrace_7560992
  have hstable : (prefixWord ++ tailWord_7560992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7560992).length < 2 ^ (prefixWord ++ tailWord_7560992).sum := by decide
  have hdescent : baseEnd_7560992 < baseStart_7560992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7560992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561012 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_7561012 : Nat := 118140960795 + 7561012 * 2 ^ 59
def prefixEnd_7561012 : Nat := 4983230072969 + 3 ^ 40 * 7561012 * 2
def baseEnd_7561012 : Nat := 3882433390412876739477545

theorem tailTrace_7561012 : CollatzResearch.WordTrace tailWord_7561012 prefixEnd_7561012 3882433390412876739477545 := by
  unfold tailWord_7561012
  simp only [CollatzResearch.WordTrace]
  refine ⟨137886381641876158443814645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183848508855834877925086193 137886381641876158443814645)
  ·
    refine ⟨12926848278925889854107623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137886381641876158443814645 12926848278925889854107623)
    ·
      refine ⟨19390272418388834781161435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12926848278925889854107623 19390272418388834781161435)
      ·
        refine ⟨29085408627583252171742153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19390272418388834781161435 29085408627583252171742153)
        ·
          refine ⟨21814056470687439128806615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29085408627583252171742153 21814056470687439128806615)
          ·
            refine ⟨32721084706031158693209923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21814056470687439128806615 32721084706031158693209923)
            ·
              refine ⟨49081627059046738039814885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32721084706031158693209923 49081627059046738039814885)
              ·
                refine ⟨9202805073571263382465291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49081627059046738039814885 9202805073571263382465291)
                ·
                  refine ⟨13804207610356895073697937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9202805073571263382465291 13804207610356895073697937)
                  ·
                    refine ⟨10353155707767671305273453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13804207610356895073697937 10353155707767671305273453)
                    ·
                      refine ⟨3882433390412876739477545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10353155707767671305273453 3882433390412876739477545)
                      ·
                        rfl

theorem cell23_7561012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_7561012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561012 prefixEnd_7561012 := by exact prefixLift 7561012
  have htrace : WordTrace (prefixWord ++ tailWord_7561012) baseStart_7561012 baseEnd_7561012 := by
    simpa [prefixWord, tailWord_7561012, baseEnd_7561012] using wordTrace_append hprefix tailTrace_7561012
  have hstable : (prefixWord ++ tailWord_7561012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561012).length < 2 ^ (prefixWord ++ tailWord_7561012).sum := by decide
  have hdescent : baseEnd_7561012 < baseStart_7561012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561068 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_7561068 : Nat := 118140960795 + 7561068 * 2 ^ 59
def prefixEnd_7561068 : Nat := 4983230072969 + 3 ^ 40 * 7561068 * 2
def baseEnd_7561068 : Nat := 3882462145329528520377287

theorem tailTrace_7561068 : CollatzResearch.WordTrace tailWord_7561068 prefixEnd_7561068 3882462145329528520377287 := by
  unfold tailWord_7561068
  simp only [CollatzResearch.WordTrace]
  refine ⟨137887402885774719225833929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183849870514366292301111905 137887402885774719225833929)
  ·
    refine ⟨103415552164331039419375447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137887402885774719225833929 103415552164331039419375447)
    ·
      refine ⟨155123328246496559129063171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103415552164331039419375447 155123328246496559129063171)
      ·
        refine ⟨232684992369744838693594757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155123328246496559129063171 232684992369744838693594757)
        ·
          refine ⟨43628436069327157255049017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232684992369744838693594757 43628436069327157255049017)
          ·
            refine ⟨32721327051995367941286763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43628436069327157255049017 32721327051995367941286763)
            ·
              refine ⟨49081990577993051911930145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32721327051995367941286763 49081990577993051911930145)
              ·
                refine ⟨36811492933494788933947609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49081990577993051911930145 36811492933494788933947609)
                ·
                  refine ⟨27608619700121091700460707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36811492933494788933947609 27608619700121091700460707)
                  ·
                    refine ⟨41412929550181637550691061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27608619700121091700460707 41412929550181637550691061)
                    ·
                      refine ⟨3882462145329528520377287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41412929550181637550691061 3882462145329528520377287)
                      ·
                        rfl

theorem cell23_7561068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_7561068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561068 prefixEnd_7561068 := by exact prefixLift 7561068
  have htrace : WordTrace (prefixWord ++ tailWord_7561068) baseStart_7561068 baseEnd_7561068 := by
    simpa [prefixWord, tailWord_7561068, baseEnd_7561068] using wordTrace_append hprefix tailTrace_7561068
  have hstable : (prefixWord ++ tailWord_7561068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561068).length < 2 ^ (prefixWord ++ tailWord_7561068).sum := by decide
  have hdescent : baseEnd_7561068 < baseStart_7561068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561112 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7561112 : Nat := 118140960795 + 7561112 * 2 ^ 59
def prefixEnd_7561112 : Nat := 4983230072969 + 3 ^ 40 * 7561112 * 2
def baseEnd_7561112 : Nat := 3882484738478326348227085

theorem tailTrace_7561112 : CollatzResearch.WordTrace tailWord_7561112 prefixEnd_7561112 3882484738478326348227085 := by
  unfold tailWord_7561112
  simp only [CollatzResearch.WordTrace]
  refine ⟨137888205291695016983134795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183850940388926689310846393 137888205291695016983134795)
  ·
    refine ⟨206832307937542525474702193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137888205291695016983134795 206832307937542525474702193)
    ·
      refine ⟨155124230953156894106026645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206832307937542525474702193 155124230953156894106026645)
      ·
        refine ⟨7271448325929229411219999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155124230953156894106026645 7271448325929229411219999)
        ·
          refine ⟨10907172488893844116829999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271448325929229411219999 10907172488893844116829999)
          ·
            refine ⟨16360758733340766175244999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10907172488893844116829999 16360758733340766175244999)
            ·
              refine ⟨24541138100011149262867499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16360758733340766175244999 24541138100011149262867499)
              ·
                refine ⟨36811707150016723894301249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24541138100011149262867499 36811707150016723894301249)
                ·
                  refine ⟨27608780362512542920725937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36811707150016723894301249 27608780362512542920725937)
                  ·
                    refine ⟨20706585271884407190544453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27608780362512542920725937 20706585271884407190544453)
                    ·
                      refine ⟨3882484738478326348227085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20706585271884407190544453 3882484738478326348227085)
                      ·
                        rfl

theorem cell23_7561112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7561112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561112 prefixEnd_7561112 := by exact prefixLift 7561112
  have htrace : WordTrace (prefixWord ++ tailWord_7561112) baseStart_7561112 baseEnd_7561112 := by
    simpa [prefixWord, tailWord_7561112, baseEnd_7561112] using wordTrace_append hprefix tailTrace_7561112
  have hstable : (prefixWord ++ tailWord_7561112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561112).length < 2 ^ (prefixWord ++ tailWord_7561112).sum := by decide
  have hdescent : baseEnd_7561112 < baseStart_7561112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561172 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_7561172 : Nat := 118140960795 + 7561172 * 2 ^ 59
def prefixEnd_7561172 : Nat := 4983230072969 + 3 ^ 40 * 7561172 * 2
def baseEnd_7561172 : Nat := 3882515547317596113476809

theorem tailTrace_7561172 : CollatzResearch.WordTrace tailWord_7561172 prefixEnd_7561172 3882515547317596113476809 := by
  unfold tailWord_7561172
  simp only [CollatzResearch.WordTrace]
  refine ⟨137889299481586332106726885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183852399308781776142302513 137889299481586332106726885)
  ·
    refine ⟨25854243652797437270011291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137889299481586332106726885 25854243652797437270011291)
    ·
      refine ⟨38781365479196155905016937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25854243652797437270011291 38781365479196155905016937)
      ·
        refine ⟨29086024109397116928762703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38781365479196155905016937 29086024109397116928762703)
        ·
          refine ⟨43629036164095675393144055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29086024109397116928762703 43629036164095675393144055)
          ·
            refine ⟨65443554246143513089716083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43629036164095675393144055 65443554246143513089716083)
            ·
              refine ⟨98165331369215269634574125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65443554246143513089716083 98165331369215269634574125)
              ·
                refine ⟨36811999263455726112965297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98165331369215269634574125 36811999263455726112965297)
                ·
                  refine ⟨27608999447591794584723973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36811999263455726112965297 27608999447591794584723973)
                  ·
                    refine ⟨5176687396423461484635745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27608999447591794584723973 5176687396423461484635745)
                    ·
                      refine ⟨3882515547317596113476809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5176687396423461484635745 3882515547317596113476809)
                      ·
                        rfl

theorem cell23_7561172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_7561172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561172 prefixEnd_7561172 := by exact prefixLift 7561172
  have htrace : WordTrace (prefixWord ++ tailWord_7561172) baseStart_7561172 baseEnd_7561172 := by
    simpa [prefixWord, tailWord_7561172, baseEnd_7561172] using wordTrace_append hprefix tailTrace_7561172
  have hstable : (prefixWord ++ tailWord_7561172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561172).length < 2 ^ (prefixWord ++ tailWord_7561172).sum := by decide
  have hdescent : baseEnd_7561172 < baseStart_7561172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561242 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_7561242 : Nat := 118140960795 + 7561242 * 2 ^ 59
def prefixEnd_7561242 : Nat := 4983230072969 + 3 ^ 40 * 7561242 * 2
def baseEnd_7561242 : Nat := 1294183830321136946533829

theorem tailTrace_7561242 : CollatzResearch.WordTrace tailWord_7561242 prefixEnd_7561242 1294183830321136946533829 := by
  unfold tailWord_7561242
  simp only [CollatzResearch.WordTrace]
  refine ⟨68945288018229766542125495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183854101381946044112334653 68945288018229766542125495)
  ·
    refine ⟨103417932027344649813188243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68945288018229766542125495 103417932027344649813188243)
    ·
      refine ⟨155126898041016974719782365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103417932027344649813188243 155126898041016974719782365)
      ·
        refine ⟨58172586765381365519918387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155126898041016974719782365 58172586765381365519918387)
        ·
          refine ⟨87258880148072048279877581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58172586765381365519918387 87258880148072048279877581)
          ·
            refine ⟨32722080055527018104954093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87258880148072048279877581 32722080055527018104954093)
            ·
              refine ⟨12270780020822631789357785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32722080055527018104954093 12270780020822631789357785)
              ·
                refine ⟨9203085015616973842018339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12270780020822631789357785 9203085015616973842018339)
                ·
                  refine ⟨13804627523425460763027509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9203085015616973842018339 13804627523425460763027509)
                  ·
                    refine ⟨1294183830321136946533829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13804627523425460763027509 1294183830321136946533829)
                    ·
                      rfl

theorem cell23_7561242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_7561242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561242 prefixEnd_7561242 := by exact prefixLift 7561242
  have htrace : WordTrace (prefixWord ++ tailWord_7561242) baseStart_7561242 baseEnd_7561242 := by
    simpa [prefixWord, tailWord_7561242, baseEnd_7561242] using wordTrace_append hprefix tailTrace_7561242
  have hstable : (prefixWord ++ tailWord_7561242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561242).length < 2 ^ (prefixWord ++ tailWord_7561242).sum := by decide
  have hdescent : baseEnd_7561242 < baseStart_7561242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561295 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 3]
def baseStart_7561295 : Nat := 118140960795 + 7561295 * 2 ^ 59
def prefixEnd_7561295 : Nat := 4983230072969 + 3 ^ 40 * 7561295 * 2
def baseEnd_7561295 : Nat := 3882578705438099132238743

theorem tailTrace_7561295 : CollatzResearch.WordTrace tailWord_7561295 prefixEnd_7561295 3882578705438099132238743 := by
  unfold tailWord_7561295
  simp only [CollatzResearch.WordTrace]
  refine ⟨275783085141727056220181339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183855390094484704146787559 275783085141727056220181339)
  ·
    refine ⟨413674627712590584330272009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275783085141727056220181339 413674627712590584330272009)
    ·
      refine ⟨310255970784442938247704007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413674627712590584330272009 310255970784442938247704007)
      ·
        refine ⟨465383956176664407371556011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310255970784442938247704007 465383956176664407371556011)
        ·
          refine ⟨698075934264996611057334017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465383956176664407371556011 698075934264996611057334017)
          ·
            refine ⟨523556950698747458293000513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698075934264996611057334017 523556950698747458293000513)
            ·
              refine ⟨392667713024060593719750385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523556950698747458293000513 392667713024060593719750385)
              ·
                refine ⟨294500784768045445289812789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392667713024060593719750385 294500784768045445289812789)
                ·
                  refine ⟨27609448572004260495919949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294500784768045445289812789 27609448572004260495919949)
                  ·
                    refine ⟨10353543214501597685969981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27609448572004260495919949 10353543214501597685969981)
                    ·
                      refine ⟨3882578705438099132238743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10353543214501597685969981 3882578705438099132238743)
                      ·
                        rfl

theorem cell23_7561295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_7561295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561295 prefixEnd_7561295 := by exact prefixLift 7561295
  have htrace : WordTrace (prefixWord ++ tailWord_7561295) baseStart_7561295 baseEnd_7561295 := by
    simpa [prefixWord, tailWord_7561295, baseEnd_7561295] using wordTrace_append hprefix tailTrace_7561295
  have hstable : (prefixWord ++ tailWord_7561295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561295).length < 2 ^ (prefixWord ++ tailWord_7561295).sum := by decide
  have hdescent : baseEnd_7561295 < baseStart_7561295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561309 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7561309 : Nat := 118140960795 + 7561309 * 2 ^ 59
def prefixEnd_7561309 : Nat := 4983230072969 + 3 ^ 40 * 7561309 * 2
def baseEnd_7561309 : Nat := 3882585894167262077463679

theorem tailTrace_7561309 : CollatzResearch.WordTrace tailWord_7561309 prefixEnd_7561309 3882585894167262077463679 := by
  unfold tailWord_7561309
  simp only [CollatzResearch.WordTrace]
  refine ⟨275783595763676336611190981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183855730509117557740793987 275783595763676336611190981)
  ·
    refine ⟨51709424205689313114598309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275783595763676336611190981 51709424205689313114598309)
    ·
      refine ⟨9695517038566746208987183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51709424205689313114598309 9695517038566746208987183)
      ·
        refine ⟨14543275557850119313480775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9695517038566746208987183 14543275557850119313480775)
        ·
          refine ⟨21814913336775178970221163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14543275557850119313480775 21814913336775178970221163)
          ·
            refine ⟨32722370005162768455331745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21814913336775178970221163 32722370005162768455331745)
            ·
              refine ⟨24541777503872076341498809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32722370005162768455331745 24541777503872076341498809)
              ·
                refine ⟨18406333127904057256124107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24541777503872076341498809 18406333127904057256124107)
                ·
                  refine ⟨27609499691856085884186161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18406333127904057256124107 27609499691856085884186161)
                  ·
                    refine ⟨20707124768892064413139621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27609499691856085884186161 20707124768892064413139621)
                    ·
                      refine ⟨3882585894167262077463679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20707124768892064413139621 3882585894167262077463679)
                      ·
                        rfl

theorem cell23_7561309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7561309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561309 prefixEnd_7561309 := by exact prefixLift 7561309
  have htrace : WordTrace (prefixWord ++ tailWord_7561309) baseStart_7561309 baseEnd_7561309 := by
    simpa [prefixWord, tailWord_7561309, baseEnd_7561309] using wordTrace_append hprefix tailTrace_7561309
  have hstable : (prefixWord ++ tailWord_7561309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561309).length < 2 ^ (prefixWord ++ tailWord_7561309).sum := by decide
  have hdescent : baseEnd_7561309 < baseStart_7561309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561310 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7561310 : Nat := 118140960795 + 7561310 * 2 ^ 59
def prefixEnd_7561310 : Nat := 4983230072969 + 3 ^ 40 * 7561310 * 2
def baseEnd_7561310 : Nat := 1294195469215972191183725

theorem tailTrace_7561310 : CollatzResearch.WordTrace tailWord_7561310 prefixEnd_7561310 1294195469215972191183725 := by
  unfold tailWord_7561310
  simp only [CollatzResearch.WordTrace]
  refine ⟨34472954029584089222747173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183855754824448475854651589 34472954029584089222747173)
  ·
    refine ⟨6463678880547016729265095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34472954029584089222747173 6463678880547016729265095)
    ·
      refine ⟨9695518320820525093897643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6463678880547016729265095 9695518320820525093897643)
      ·
        refine ⟨14543277481230787640846465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9695518320820525093897643 14543277481230787640846465)
        ·
          refine ⟨10907458110923090730634849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14543277481230787640846465 10907458110923090730634849)
          ·
            refine ⟨8180593583192318047976137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10907458110923090730634849 8180593583192318047976137)
            ·
              refine ⟨6135445187394238535982103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8180593583192318047976137 6135445187394238535982103)
              ·
                refine ⟨9203167781091357803973155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6135445187394238535982103 9203167781091357803973155)
                ·
                  refine ⟨13804751671637036705959733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9203167781091357803973155 13804751671637036705959733)
                  ·
                    refine ⟨1294195469215972191183725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13804751671637036705959733 1294195469215972191183725)
                    ·
                      rfl

theorem cell23_7561310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7561310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561310 prefixEnd_7561310 := by exact prefixLift 7561310
  have htrace : WordTrace (prefixWord ++ tailWord_7561310) baseStart_7561310 baseEnd_7561310 := by
    simpa [prefixWord, tailWord_7561310, baseEnd_7561310] using wordTrace_append hprefix tailTrace_7561310
  have hstable : (prefixWord ++ tailWord_7561310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561310).length < 2 ^ (prefixWord ++ tailWord_7561310).sum := by decide
  have hdescent : baseEnd_7561310 < baseStart_7561310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561312 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 3]
def baseStart_7561312 : Nat := 118140960795 + 7561312 * 2 ^ 59
def prefixEnd_7561312 : Nat := 4983230072969 + 3 ^ 40 * 7561312 * 2
def baseEnd_7561312 : Nat := 3882587434609225565726165

theorem tailTrace_7561312 : CollatzResearch.WordTrace tailWord_7561312 prefixEnd_7561312 3882587434609225565726165 := by
  unfold tailWord_7561312
  simp only [CollatzResearch.WordTrace]
  refine ⟨137891852591332734061775095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183855803455110312082366793 137891852591332734061775095)
  ·
    refine ⟨206837778886999101092662643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137891852591332734061775095 206837778886999101092662643)
    ·
      refine ⟨310256668330498651638993965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206837778886999101092662643 310256668330498651638993965)
      ·
        refine ⟨116346250623936994364622737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310256668330498651638993965 116346250623936994364622737)
        ·
          refine ⟨87259687967952745773467053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116346250623936994364622737 87259687967952745773467053)
          ·
            refine ⟨32722382987982279665050145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87259687967952745773467053 32722382987982279665050145)
            ·
              refine ⟨24541787240986709748787609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32722382987982279665050145 24541787240986709748787609)
              ·
                refine ⟨18406340430740032311590707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24541787240986709748787609 18406340430740032311590707)
                ·
                  refine ⟨27609510646110048467386061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18406340430740032311590707 27609510646110048467386061)
                  ·
                    refine ⟨10353566492291268175269773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27609510646110048467386061 10353566492291268175269773)
                    ·
                      refine ⟨3882587434609225565726165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10353566492291268175269773 3882587434609225565726165)
                      ·
                        rfl

theorem cell23_7561312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_7561312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561312 prefixEnd_7561312 := by exact prefixLift 7561312
  have htrace : WordTrace (prefixWord ++ tailWord_7561312) baseStart_7561312 baseEnd_7561312 := by
    simpa [prefixWord, tailWord_7561312, baseEnd_7561312] using wordTrace_append hprefix tailTrace_7561312
  have hstable : (prefixWord ++ tailWord_7561312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561312).length < 2 ^ (prefixWord ++ tailWord_7561312).sum := by decide
  have hdescent : baseEnd_7561312 < baseStart_7561312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561364 : List Nat := [2, 4, 2, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7561364 : Nat := 118140960795 + 7561364 * 2 ^ 59
def prefixEnd_7561364 : Nat := 4983230072969 + 3 ^ 40 * 7561364 * 2
def baseEnd_7561364 : Nat := 3882614135603259362275927

theorem tailTrace_7561364 : CollatzResearch.WordTrace tailWord_7561364 prefixEnd_7561364 3882614135603259362275927 := by
  unfold tailWord_7561364
  simp only [CollatzResearch.WordTrace]
  refine ⟨137892800889238540502221573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183857067852318054002962097 137892800889238540502221573)
  ·
    refine ⟨25854900166732226344166545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137892800889238540502221573 25854900166732226344166545)
    ·
      refine ⟨19391175125049169758124909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25854900166732226344166545 19391175125049169758124909)
      ·
        refine ⟨7271690671893438659296841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19391175125049169758124909 7271690671893438659296841)
        ·
          refine ⟨5453768003920078994472631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7271690671893438659296841 5453768003920078994472631)
          ·
            refine ⟨8180652005880118491708947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453768003920078994472631 8180652005880118491708947)
            ·
              refine ⟨12270978008820177737563421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180652005880118491708947 12270978008820177737563421)
              ·
                refine ⟨4601616753307566651586283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12270978008820177737563421 4601616753307566651586283)
                ·
                  refine ⟨6902425129961349977379425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601616753307566651586283 6902425129961349977379425)
                  ·
                    refine ⟨5176818847471012483034569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6902425129961349977379425 5176818847471012483034569)
                    ·
                      refine ⟨3882614135603259362275927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5176818847471012483034569 3882614135603259362275927)
                      ·
                        rfl

theorem cell23_7561364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7561364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561364 prefixEnd_7561364 := by exact prefixLift 7561364
  have htrace : WordTrace (prefixWord ++ tailWord_7561364) baseStart_7561364 baseEnd_7561364 := by
    simpa [prefixWord, tailWord_7561364, baseEnd_7561364] using wordTrace_append hprefix tailTrace_7561364
  have hstable : (prefixWord ++ tailWord_7561364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561364).length < 2 ^ (prefixWord ++ tailWord_7561364).sum := by decide
  have hdescent : baseEnd_7561364 < baseStart_7561364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561372 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7561372 : Nat := 118140960795 + 7561372 * 2 ^ 59
def prefixEnd_7561372 : Nat := 4983230072969 + 3 ^ 40 * 7561372 * 2
def baseEnd_7561372 : Nat := 3882618243448495330975889

theorem tailTrace_7561372 : CollatzResearch.WordTrace tailWord_7561372 prefixEnd_7561372 3882618243448495330975889 := by
  unfold tailWord_7561372
  simp only [CollatzResearch.WordTrace]
  refine ⟨137892946781224049185367185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183857262374965398913822913 137892946781224049185367185)
  ·
    refine ⟨103419710085918036889025389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137892946781224049185367185 103419710085918036889025389)
    ·
      refine ⟨38782391282219263833384521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103419710085918036889025389 38782391282219263833384521)
      ·
        refine ⟨29086793461664447875038391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38782391282219263833384521 29086793461664447875038391)
        ·
          refine ⟨43630190192496671812557587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29086793461664447875038391 43630190192496671812557587)
          ·
            refine ⟨65445285288745007718836381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43630190192496671812557587 65445285288745007718836381)
            ·
              refine ⟨24541981983279377894563643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65445285288745007718836381 24541981983279377894563643)
              ·
                refine ⟨36812972974919066841845465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24541981983279377894563643 36812972974919066841845465)
                ·
                  refine ⟨27609729731189300131384099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36812972974919066841845465 27609729731189300131384099)
                  ·
                    refine ⟨41414594596783950197076149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27609729731189300131384099 41414594596783950197076149)
                    ·
                      refine ⟨3882618243448495330975889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41414594596783950197076149 3882618243448495330975889)
                      ·
                        rfl

theorem cell23_7561372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7561372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561372 prefixEnd_7561372 := by exact prefixLift 7561372
  have htrace : WordTrace (prefixWord ++ tailWord_7561372) baseStart_7561372 baseEnd_7561372 := by
    simpa [prefixWord, tailWord_7561372, baseEnd_7561372] using wordTrace_append hprefix tailTrace_7561372
  have hstable : (prefixWord ++ tailWord_7561372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561372).length < 2 ^ (prefixWord ++ tailWord_7561372).sum := by decide
  have hdescent : baseEnd_7561372 < baseStart_7561372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561397 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7561397 : Nat := 118140960795 + 7561397 * 2 ^ 59
def prefixEnd_7561397 : Nat := 4983230072969 + 3 ^ 40 * 7561397 * 2
def baseEnd_7561397 : Nat := 3882631080464857733163275

theorem tailTrace_7561397 : CollatzResearch.WordTrace tailWord_7561397 prefixEnd_7561397 3882631080464857733163275 := by
  unfold tailWord_7561397
  simp only [CollatzResearch.WordTrace]
  refine ⟨275786805387357527640394445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183857870258238351760262963 275786805387357527640394445)
  ·
    refine ⟨103420052020259072865147917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275786805387357527640394445 103420052020259072865147917)
    ·
      refine ⟨38782519507597152324430469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103420052020259072865147917 38782519507597152324430469)
      ·
        refine ⟨7271722407674466060830713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38782519507597152324430469 7271722407674466060830713)
        ·
          refine ⟨5453791805755849545623035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7271722407674466060830713 5453791805755849545623035)
          ·
            refine ⟨8180687708633774318434553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453791805755849545623035 8180687708633774318434553)
            ·
              refine ⟨6135515781475330738825915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8180687708633774318434553 6135515781475330738825915)
              ·
                refine ⟨9203273672212996108238873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6135515781475330738825915 9203273672212996108238873)
                ·
                  refine ⟨6902455254159747081179155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9203273672212996108238873 6902455254159747081179155)
                  ·
                    refine ⟨10353682881239620621768733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6902455254159747081179155 10353682881239620621768733)
                    ·
                      refine ⟨3882631080464857733163275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10353682881239620621768733 3882631080464857733163275)
                      ·
                        rfl

theorem cell23_7561397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7561397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561397 prefixEnd_7561397 := by exact prefixLift 7561397
  have htrace : WordTrace (prefixWord ++ tailWord_7561397) baseStart_7561397 baseEnd_7561397 := by
    simpa [prefixWord, tailWord_7561397, baseEnd_7561397] using wordTrace_append hprefix tailTrace_7561397
  have hstable : (prefixWord ++ tailWord_7561397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561397).length < 2 ^ (prefixWord ++ tailWord_7561397).sum := by decide
  have hdescent : baseEnd_7561397 < baseStart_7561397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561402 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_7561402 : Nat := 118140960795 + 7561402 * 2 ^ 59
def prefixEnd_7561402 : Nat := 4983230072969 + 3 ^ 40 * 7561402 * 2
def baseEnd_7561402 : Nat := 3882633647868130213600751

theorem tailTrace_7561402 : CollatzResearch.WordTrace tailWord_7561402 prefixEnd_7561402 3882633647868130213600751 := by
  unfold tailWord_7561402
  simp only [CollatzResearch.WordTrace]
  refine ⟨68946746938084853373581615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183857991834892942329550973 68946746938084853373581615)
  ·
    refine ⟨103420120407127280060372423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68946746938084853373581615 103420120407127280060372423)
    ·
      refine ⟨155130180610690920090558635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103420120407127280060372423 155130180610690920090558635)
      ·
        refine ⟨232695270916036380135837953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155130180610690920090558635 232695270916036380135837953)
        ·
          refine ⟨174521453187027285101878465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232695270916036380135837953 174521453187027285101878465)
          ·
            refine ⟨130891089890270463826408849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174521453187027285101878465 130891089890270463826408849)
            ·
              refine ⟨98168317417702847869806637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130891089890270463826408849 98168317417702847869806637)
              ·
                refine ⟨36813119031638567951177489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98168317417702847869806637 36813119031638567951177489)
                ·
                  refine ⟨27609839273728925963383117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36813119031638567951177489 27609839273728925963383117)
                  ·
                    refine ⟨10353689727648347236268669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27609839273728925963383117 10353689727648347236268669)
                    ·
                      refine ⟨3882633647868130213600751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10353689727648347236268669 3882633647868130213600751)
                      ·
                        rfl

theorem cell23_7561402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_7561402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561402 prefixEnd_7561402 := by exact prefixLift 7561402
  have htrace : WordTrace (prefixWord ++ tailWord_7561402) baseStart_7561402 baseEnd_7561402 := by
    simpa [prefixWord, tailWord_7561402, baseEnd_7561402] using wordTrace_append hprefix tailTrace_7561402
  have hstable : (prefixWord ++ tailWord_7561402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561402).length < 2 ^ (prefixWord ++ tailWord_7561402).sum := by decide
  have hdescent : baseEnd_7561402 < baseStart_7561402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561432 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_7561432 : Nat := 118140960795 + 7561432 * 2 ^ 59
def prefixEnd_7561432 : Nat := 4983230072969 + 3 ^ 40 * 7561432 * 2
def baseEnd_7561432 : Nat := 3882649052287765096225613

theorem tailTrace_7561432 : CollatzResearch.WordTrace tailWord_7561432 prefixEnd_7561432 3882649052287765096225613 := by
  unfold tailWord_7561432
  simp only [CollatzResearch.WordTrace]
  refine ⟨137894040971115364308959275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183858721294820485745279033 137894040971115364308959275)
  ·
    refine ⟨206841061456673046463438913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137894040971115364308959275 206841061456673046463438913)
    ·
      refine ⟨155130796092504784847579185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206841061456673046463438913 155130796092504784847579185)
      ·
        refine ⟨116348097069378588635684389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155130796092504784847579185 116348097069378588635684389)
        ·
          refine ⟨21815268200508485369190823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116348097069378588635684389 21815268200508485369190823)
          ·
            refine ⟨32722902300762728053786235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21815268200508485369190823 32722902300762728053786235)
            ·
              refine ⟨49084353451144092080679353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32722902300762728053786235 49084353451144092080679353)
              ·
                refine ⟨36813265088358069060509515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49084353451144092080679353 36813265088358069060509515)
                ·
                  refine ⟨55219897632537103590764273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36813265088358069060509515 55219897632537103590764273)
                  ·
                    refine ⟨41414923224402827693073205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55219897632537103590764273 41414923224402827693073205)
                    ·
                      refine ⟨3882649052287765096225613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41414923224402827693073205 3882649052287765096225613)
                      ·
                        rfl

theorem cell23_7561432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_7561432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561432 prefixEnd_7561432 := by exact prefixLift 7561432
  have htrace : WordTrace (prefixWord ++ tailWord_7561432) baseStart_7561432 baseEnd_7561432 := by
    simpa [prefixWord, tailWord_7561432, baseEnd_7561432] using wordTrace_append hprefix tailTrace_7561432
  have hstable : (prefixWord ++ tailWord_7561432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561432).length < 2 ^ (prefixWord ++ tailWord_7561432).sum := by decide
  have hdescent : baseEnd_7561432 < baseStart_7561432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561459 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 2, 4, 2]
def baseStart_7561459 : Nat := 118140960795 + 7561459 * 2 ^ 59
def prefixEnd_7561459 : Nat := 4983230072969 + 3 ^ 40 * 7561459 * 2
def baseEnd_7561459 : Nat := 3882662916265436490587989

theorem tailTrace_7561459 : CollatzResearch.WordTrace tailWord_7561459 prefixEnd_7561459 3882662916265436490587989 := by
  unfold tailWord_7561459
  simp only [CollatzResearch.WordTrace]
  refine ⟨275789066713132912229151431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183859377808755274819434287 275789066713132912229151431)
  ·
    refine ⟨413683600069699368343727147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275789066713132912229151431 413683600069699368343727147)
    ·
      refine ⟨620525400104549052515590721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413683600069699368343727147 620525400104549052515590721)
      ·
        refine ⟨465394050078411789386693041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620525400104549052515590721 465394050078411789386693041)
        ·
          refine ⟨349045537558808842040019781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465394050078411789386693041 349045537558808842040019781)
          ·
            refine ⟨65446038292276657882503709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349045537558808842040019781 65446038292276657882503709)
            ·
              refine ⟨24542264359603746705938891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65446038292276657882503709 24542264359603746705938891)
              ·
                refine ⟨36813396539405620058908337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24542264359603746705938891 36813396539405620058908337)
                ·
                  refine ⟨27610047404554215044181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36813396539405620058908337 27610047404554215044181253)
                  ·
                    refine ⟨5176883888353915320783985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27610047404554215044181253 5176883888353915320783985)
                    ·
                      refine ⟨3882662916265436490587989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5176883888353915320783985 3882662916265436490587989)
                      ·
                        rfl

theorem cell23_7561459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 4, 2].length) (baseStart_7561459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561459 prefixEnd_7561459 := by exact prefixLift 7561459
  have htrace : WordTrace (prefixWord ++ tailWord_7561459) baseStart_7561459 baseEnd_7561459 := by
    simpa [prefixWord, tailWord_7561459, baseEnd_7561459] using wordTrace_append hprefix tailTrace_7561459
  have hstable : (prefixWord ++ tailWord_7561459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561459).length < 2 ^ (prefixWord ++ tailWord_7561459).sum := by decide
  have hdescent : baseEnd_7561459 < baseStart_7561459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561519 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 1, 5, 2]
def baseStart_7561519 : Nat := 118140960795 + 7561519 * 2 ^ 59
def prefixEnd_7561519 : Nat := 4983230072969 + 3 ^ 40 * 7561519 * 2
def baseEnd_7561519 : Nat := 3882693725104706255837713

theorem tailTrace_7561519 : CollatzResearch.WordTrace tailWord_7561519 prefixEnd_7561519 3882693725104706255837713 := by
  unfold tailWord_7561519
  simp only [CollatzResearch.WordTrace]
  refine ⟨275791255092915542476335611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183860836728610361650890407 275791255092915542476335611)
  ·
    refine ⟨413686882639373313714503417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275791255092915542476335611 413686882639373313714503417)
    ·
      refine ⟨310265161979529985285877563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413686882639373313714503417 310265161979529985285877563)
      ·
        refine ⟨465397742969294977928816345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310265161979529985285877563 465397742969294977928816345)
        ·
          refine ⟨349048307226971233446612259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465397742969294977928816345 349048307226971233446612259)
          ·
            refine ⟨523572460840456850169918389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349048307226971233446612259 523572460840456850169918389)
            ·
              refine ⟨49084918203792829703429849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 523572460840456850169918389 49084918203792829703429849)
              ·
                refine ⟨36813688652844622277572387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49084918203792829703429849 36813688652844622277572387)
                ·
                  refine ⟨55220532979266933416358581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36813688652844622277572387 55220532979266933416358581)
                  ·
                    refine ⟨5176924966806275007783617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55220532979266933416358581 5176924966806275007783617)
                    ·
                      refine ⟨3882693725104706255837713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5176924966806275007783617 3882693725104706255837713)
                      ·
                        rfl

theorem cell23_7561519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 5, 2].length) (baseStart_7561519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561519 prefixEnd_7561519 := by exact prefixLift 7561519
  have htrace : WordTrace (prefixWord ++ tailWord_7561519) baseStart_7561519 baseEnd_7561519 := by
    simpa [prefixWord, tailWord_7561519, baseEnd_7561519] using wordTrace_append hprefix tailTrace_7561519
  have hstable : (prefixWord ++ tailWord_7561519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561519).length < 2 ^ (prefixWord ++ tailWord_7561519).sum := by decide
  have hdescent : baseEnd_7561519 < baseStart_7561519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561537 : List Nat := [1, 2, 5, 2, 3, 1, 1, 3, 1, 4]
def baseStart_7561537 : Nat := 118140960795 + 7561537 * 2 ^ 59
def prefixEnd_7561537 : Nat := 4983230072969 + 3 ^ 40 * 7561537 * 2
def baseEnd_7561537 : Nat := 1294234322585495728470877

theorem tailTrace_7561537 : CollatzResearch.WordTrace tailWord_7561537 prefixEnd_7561537 1294234322585495728470877 := by
  unfold tailWord_7561537
  simp only [CollatzResearch.WordTrace]
  refine ⟨275791911606850331550490865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183861274404566887700327243 275791911606850331550490865)
  ·
    refine ⟨206843933705137748662868149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275791911606850331550490865 206843933705137748662868149)
    ·
      refine ⟨19391618784856663937143889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206843933705137748662868149 19391618784856663937143889)
      ·
        refine ⟨14543714088642497952857917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19391618784856663937143889 14543714088642497952857917)
        ·
          refine ⟨5453892783240936732321719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14543714088642497952857917 5453892783240936732321719)
          ·
            refine ⟨8180839174861405098482579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453892783240936732321719 8180839174861405098482579)
            ·
              refine ⟨12271258762292107647723869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180839174861405098482579 12271258762292107647723869)
              ·
                refine ⟨4601722035859540367896451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12271258762292107647723869 4601722035859540367896451)
                ·
                  refine ⟨6902583053789310551844677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601722035859540367896451 6902583053789310551844677)
                  ·
                    refine ⟨1294234322585495728470877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6902583053789310551844677 1294234322585495728470877)
                    ·
                      rfl

theorem cell23_7561537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_7561537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561537 prefixEnd_7561537 := by exact prefixLift 7561537
  have htrace : WordTrace (prefixWord ++ tailWord_7561537) baseStart_7561537 baseEnd_7561537 := by
    simpa [prefixWord, tailWord_7561537, baseEnd_7561537] using wordTrace_append hprefix tailTrace_7561537
  have hstable : (prefixWord ++ tailWord_7561537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561537).length < 2 ^ (prefixWord ++ tailWord_7561537).sum := by decide
  have hdescent : baseEnd_7561537 < baseStart_7561537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561559 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 4, 4]
def baseStart_7561559 : Nat := 118140960795 + 7561559 * 2 ^ 59
def prefixEnd_7561559 : Nat := 4983230072969 + 3 ^ 40 * 7561559 * 2
def baseEnd_7561559 : Nat := 1294238088110295366445843

theorem tailTrace_7561559 : CollatzResearch.WordTrace tailWord_7561559 prefixEnd_7561559 1294238088110295366445843 := by
  unfold tailWord_7561559
  simp only [CollatzResearch.WordTrace]
  refine ⟨275792714012770629307791731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183861809341847086205194487 275792714012770629307791731)
  ·
    refine ⟨413689071019155943961687597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275792714012770629307791731 413689071019155943961687597)
    ·
      refine ⟨155133401632183478985632849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413689071019155943961687597 155133401632183478985632849)
      ·
        refine ⟨116350051224137609239224637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155133401632183478985632849 116350051224137609239224637)
        ·
          refine ⟨43631269209051603464709239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116350051224137609239224637 43631269209051603464709239)
          ·
            refine ⟨65446903813577405197063859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43631269209051603464709239 65446903813577405197063859)
            ·
              refine ⟨98170355720366107795595789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65446903813577405197063859 98170355720366107795595789)
              ·
                refine ⟨36813883395137290423348421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98170355720366107795595789 36813883395137290423348421)
                ·
                  refine ⟨6902603136588241954377829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36813883395137290423348421 6902603136588241954377829)
                  ·
                    refine ⟨1294238088110295366445843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6902603136588241954377829 1294238088110295366445843)
                    ·
                      rfl

theorem cell23_7561559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_7561559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561559 prefixEnd_7561559 := by exact prefixLift 7561559
  have htrace : WordTrace (prefixWord ++ tailWord_7561559) baseStart_7561559 baseEnd_7561559 := by
    simpa [prefixWord, tailWord_7561559, baseEnd_7561559] using wordTrace_append hprefix tailTrace_7561559
  have hstable : (prefixWord ++ tailWord_7561559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561559).length < 2 ^ (prefixWord ++ tailWord_7561559).sum := by decide
  have hdescent : baseEnd_7561559 < baseStart_7561559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561586 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_7561586 : Nat := 118140960795 + 7561586 * 2 ^ 59
def prefixEnd_7561586 : Nat := 4983230072969 + 3 ^ 40 * 7561586 * 2
def baseEnd_7561586 : Nat := 3882728128308557493699905

theorem tailTrace_7561586 : CollatzResearch.WordTrace tailWord_7561586 prefixEnd_7561586 3882728128308557493699905 := by
  unfold tailWord_7561586
  simp only [CollatzResearch.WordTrace]
  refine ⟨68948424695918203229756153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183862465855781875279349741 68948424695918203229756153)
  ·
    refine ⟨51711318521938652422317115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68948424695918203229756153 51711318521938652422317115)
    ·
      refine ⟨77566977782907978633475673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51711318521938652422317115 77566977782907978633475673)
      ·
        refine ⟨58175233337180983975106755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77566977782907978633475673 58175233337180983975106755)
        ·
          refine ⟨87262850005771475962660133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58175233337180983975106755 87262850005771475962660133)
          ·
            refine ⟨16361784376082151742998775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87262850005771475962660133 16361784376082151742998775)
            ·
              refine ⟨24542676564123227614498163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16361784376082151742998775 24542676564123227614498163)
              ·
                refine ⟨36814014846184841421747245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24542676564123227614498163 36814014846184841421747245)
                ·
                  refine ⟨13805255567319315533155217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36814014846184841421747245 13805255567319315533155217)
                  ·
                    refine ⟨10353941675489486649866413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13805255567319315533155217 10353941675489486649866413)
                    ·
                      refine ⟨3882728128308557493699905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10353941675489486649866413 3882728128308557493699905)
                      ·
                        rfl

theorem cell23_7561586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_7561586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561586 prefixEnd_7561586 := by exact prefixLift 7561586
  have htrace : WordTrace (prefixWord ++ tailWord_7561586) baseStart_7561586 baseEnd_7561586 := by
    simpa [prefixWord, tailWord_7561586, baseEnd_7561586] using wordTrace_append hprefix tailTrace_7561586
  have hstable : (prefixWord ++ tailWord_7561586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561586).length < 2 ^ (prefixWord ++ tailWord_7561586).sum := by decide
  have hdescent : baseEnd_7561586 < baseStart_7561586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561589 : List Nat := [1, 3, 4, 1, 2, 1, 2, 9]
def baseStart_7561589 : Nat := 118140960795 + 7561589 * 2 ^ 59
def prefixEnd_7561589 : Nat := 4983230072969 + 3 ^ 40 * 7561589 * 2
def baseEnd_7561589 : Nat := 143804802546315591924533

theorem tailTrace_7561589 : CollatzResearch.WordTrace tailWord_7561589 prefixEnd_7561589 143804802546315591924533 := by
  unfold tailWord_7561589
  simp only [CollatzResearch.WordTrace]
  refine ⟨275793808202661944431383821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183862538801774629620922547 275793808202661944431383821)
  ·
    refine ⟨103422678075998229161768933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275793808202661944431383821 103422678075998229161768933)
    ·
      refine ⟨19391752139249667967831675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103422678075998229161768933 19391752139249667967831675)
      ·
        refine ⟨29087628208874501951747513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19391752139249667967831675 29087628208874501951747513)
        ·
          refine ⟨21815721156655876463810635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29087628208874501951747513 21815721156655876463810635)
          ·
            refine ⟨32723581734983814695715953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21815721156655876463810635 32723581734983814695715953)
            ·
              refine ⟨24542686301237861021786965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32723581734983814695715953 24542686301237861021786965)
              ·
                refine ⟨143804802546315591924533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24542686301237861021786965 143804802546315591924533)
                ·
                  rfl

theorem cell23_7561589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 9].length) (baseStart_7561589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561589 prefixEnd_7561589 := by exact prefixLift 7561589
  have htrace : WordTrace (prefixWord ++ tailWord_7561589) baseStart_7561589 baseEnd_7561589 := by
    simpa [prefixWord, tailWord_7561589, baseEnd_7561589] using wordTrace_append hprefix tailTrace_7561589
  have hstable : (prefixWord ++ tailWord_7561589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561589).length < 2 ^ (prefixWord ++ tailWord_7561589).sum := by decide
  have hdescent : baseEnd_7561589 < baseStart_7561589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561599 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 3]
def baseStart_7561599 : Nat := 118140960795 + 7561599 * 2 ^ 59
def prefixEnd_7561599 : Nat := 4983230072969 + 3 ^ 40 * 7561599 * 2
def baseEnd_7561599 : Nat := 3882734803557065942837345

theorem tailTrace_7561599 : CollatzResearch.WordTrace tailWord_7561599 prefixEnd_7561599 3882734803557065942837345 := by
  unfold tailWord_7561599
  simp only [CollatzResearch.WordTrace]
  refine ⟨275794172932625716139247851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183862781955083810759498567 275794172932625716139247851)
  ·
    refine ⟨413691259398938574208871777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275794172932625716139247851 413691259398938574208871777)
    ·
      refine ⟨310268444549203930656653833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413691259398938574208871777 310268444549203930656653833)
      ·
        refine ⟨232701333411902947992490375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310268444549203930656653833 232701333411902947992490375)
        ·
          refine ⟨349052000117854421988735563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232701333411902947992490375 349052000117854421988735563)
          ·
            refine ⟨523578000176781632983103345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349052000117854421988735563 523578000176781632983103345)
            ·
              refine ⟨392683500132586224737327509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523578000176781632983103345 392683500132586224737327509)
              ·
                refine ⟨18407039068714979284562227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 392683500132586224737327509 18407039068714979284562227)
                ·
                  refine ⟨27610558603072468926843341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18407039068714979284562227 27610558603072468926843341)
                  ·
                    refine ⟨10353959476152175847566253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27610558603072468926843341 10353959476152175847566253)
                    ·
                      refine ⟨3882734803557065942837345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10353959476152175847566253 3882734803557065942837345)
                      ·
                        rfl

theorem cell23_7561599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_7561599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561599 prefixEnd_7561599 := by exact prefixLift 7561599
  have htrace : WordTrace (prefixWord ++ tailWord_7561599) baseStart_7561599 baseEnd_7561599 := by
    simpa [prefixWord, tailWord_7561599, baseEnd_7561599] using wordTrace_append hprefix tailTrace_7561599
  have hstable : (prefixWord ++ tailWord_7561599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561599).length < 2 ^ (prefixWord ++ tailWord_7561599).sum := by decide
  have hdescent : baseEnd_7561599 < baseStart_7561599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561603 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 1, 1, 5]
def baseStart_7561603 : Nat := 118140960795 + 7561603 * 2 ^ 59
def prefixEnd_7561603 : Nat := 4983230072969 + 3 ^ 40 * 7561603 * 2
def baseEnd_7561603 : Nat := 3882736857479683927187327

theorem tailTrace_7561603 : CollatzResearch.WordTrace tailWord_7561603 prefixEnd_7561603 3882736857479683927187327 := by
  unfold tailWord_7561603
  simp only [CollatzResearch.WordTrace]
  refine ⟨275794318824611224822393463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183862879216407483214928975 275794318824611224822393463)
  ·
    refine ⟨413691478236916837233590195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275794318824611224822393463 413691478236916837233590195)
    ·
      refine ⟨620537217355375255850385293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413691478236916837233590195 620537217355375255850385293)
      ·
        refine ⟨232701456508265720943894485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620537217355375255850385293 232701456508265720943894485)
        ·
          refine ⟨5453940386912477834622527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 232701456508265720943894485 5453940386912477834622527)
          ·
            refine ⟨8180910580368716751933791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453940386912477834622527 8180910580368716751933791)
            ·
              refine ⟨12271365870553075127900687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180910580368716751933791 12271365870553075127900687)
              ·
                refine ⟨18407048805829612691851031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12271365870553075127900687 18407048805829612691851031)
                ·
                  refine ⟨27610573208744419037776547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18407048805829612691851031 27610573208744419037776547)
                  ·
                    refine ⟨41415859813116628556664821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27610573208744419037776547 41415859813116628556664821)
                    ·
                      refine ⟨3882736857479683927187327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41415859813116628556664821 3882736857479683927187327)
                      ·
                        rfl

theorem cell23_7561603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_7561603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561603 prefixEnd_7561603 := by exact prefixLift 7561603
  have htrace : WordTrace (prefixWord ++ tailWord_7561603) baseStart_7561603 baseEnd_7561603 := by
    simpa [prefixWord, tailWord_7561603, baseEnd_7561603] using wordTrace_append hprefix tailTrace_7561603
  have hstable : (prefixWord ++ tailWord_7561603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561603).length < 2 ^ (prefixWord ++ tailWord_7561603).sum := by decide
  have hdescent : baseEnd_7561603 < baseStart_7561603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561610 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_7561610 : Nat := 118140960795 + 7561610 * 2 ^ 59
def prefixEnd_7561610 : Nat := 4983230072969 + 3 ^ 40 * 7561610 * 2
def baseEnd_7561610 : Nat := 1294246817281421799933265

theorem tailTrace_7561610 : CollatzResearch.WordTrace tailWord_7561610 prefixEnd_7561610 1294246817281421799933265 := by
  unfold tailWord_7561610
  simp only [CollatzResearch.WordTrace]
  refine ⟨68948643533896466254474571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183863049423723910011932189 68948643533896466254474571)
  ·
    refine ⟨103422965300844699381711857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68948643533896466254474571 103422965300844699381711857)
    ·
      refine ⟨77567223975633524536283893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103422965300844699381711857 77567223975633524536283893)
      ·
        refine ⟨7271927247715642925276615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77567223975633524536283893 7271927247715642925276615)
        ·
          refine ⟨10907890871573464387914923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271927247715642925276615 10907890871573464387914923)
          ·
            refine ⟨16361836307360196581872385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10907890871573464387914923 16361836307360196581872385)
            ·
              refine ⟨12271377230520147436404289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16361836307360196581872385 12271377230520147436404289)
              ·
                refine ⟨9203532922890110577303217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12271377230520147436404289 9203532922890110577303217)
                ·
                  refine ⟨6902649692167582932977413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9203532922890110577303217 6902649692167582932977413)
                  ·
                    refine ⟨1294246817281421799933265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6902649692167582932977413 1294246817281421799933265)
                    ·
                      rfl

theorem cell23_7561610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_7561610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561610 prefixEnd_7561610 := by exact prefixLift 7561610
  have htrace : WordTrace (prefixWord ++ tailWord_7561610) baseStart_7561610 baseEnd_7561610 := by
    simpa [prefixWord, tailWord_7561610, baseEnd_7561610] using wordTrace_append hprefix tailTrace_7561610
  have hstable : (prefixWord ++ tailWord_7561610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561610).length < 2 ^ (prefixWord ++ tailWord_7561610).sum := by decide
  have hdescent : baseEnd_7561610 < baseStart_7561610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561660 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_7561660 : Nat := 118140960795 + 7561660 * 2 ^ 59
def prefixEnd_7561660 : Nat := 4983230072969 + 3 ^ 40 * 7561660 * 2
def baseEnd_7561660 : Nat := 3882766125876990204174565

theorem tailTrace_7561660 : CollatzResearch.WordTrace tailWord_7561660 prefixEnd_7561660 3882766125876990204174565 := by
  unfold tailWord_7561660
  simp only [CollatzResearch.WordTrace]
  refine ⟨137898198892702361778609217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183864265190269815704812289 137898198892702361778609217)
  ·
    refine ⟨103423649169526771333956913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137898198892702361778609217 103423649169526771333956913)
    ·
      refine ⟨77567736877145078500467685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103423649169526771333956913 77567736877145078500467685)
      ·
        refine ⟨14543950664464702218837691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77567736877145078500467685 14543950664464702218837691)
        ·
          refine ⟨21815925996697053328256537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14543950664464702218837691 21815925996697053328256537)
          ·
            refine ⟨16361944497522789996192403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21815925996697053328256537 16361944497522789996192403)
            ·
              refine ⟨24542916746284184994288605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16361944497522789996192403 24542916746284184994288605)
              ·
                refine ⟨9203593779856569372858227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24542916746284184994288605 9203593779856569372858227)
                ·
                  refine ⟨13805390669784854059287341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9203593779856569372858227 13805390669784854059287341)
                  ·
                    refine ⟨5177021501169320272232753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13805390669784854059287341 5177021501169320272232753)
                    ·
                      refine ⟨3882766125876990204174565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177021501169320272232753 3882766125876990204174565)
                      ·
                        rfl

theorem cell23_7561660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_7561660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561660 prefixEnd_7561660 := by exact prefixLift 7561660
  have htrace : WordTrace (prefixWord ++ tailWord_7561660) baseStart_7561660 baseEnd_7561660 := by
    simpa [prefixWord, tailWord_7561660, baseEnd_7561660] using wordTrace_append hprefix tailTrace_7561660
  have hstable : (prefixWord ++ tailWord_7561660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561660).length < 2 ^ (prefixWord ++ tailWord_7561660).sum := by decide
  have hdescent : baseEnd_7561660 < baseStart_7561660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561730 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 7]
def baseStart_7561730 : Nat := 118140960795 + 7561730 * 2 ^ 59
def prefixEnd_7561730 : Nat := 4983230072969 + 3 ^ 40 * 7561730 * 2
def baseEnd_7561730 : Nat := 431422452169200547811027

theorem tailTrace_7561730 : CollatzResearch.WordTrace tailWord_7561730 prefixEnd_7561730 431422452169200547811027 := by
  unfold tailWord_7561730
  simp only [CollatzResearch.WordTrace]
  refine ⟨68949737723787781378066661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183865967263434083674844429 68949737723787781378066661)
  ·
    refine ⟨12928075823210209008387499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68949737723787781378066661 12928075823210209008387499)
    ·
      refine ⟨19392113734815313512581249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12928075823210209008387499 19392113734815313512581249)
      ·
        refine ⟨14544085301111485134435937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19392113734815313512581249 14544085301111485134435937)
        ·
          refine ⟨10908063975833613850826953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14544085301111485134435937 10908063975833613850826953)
          ·
            refine ⟨8181047981875210388120215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10908063975833613850826953 8181047981875210388120215)
            ·
              refine ⟨12271571972812815582180323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181047981875210388120215 12271571972812815582180323)
              ·
                refine ⟨18407357959219223373270485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12271571972812815582180323 18407357959219223373270485)
                ·
                  refine ⟨431422452169200547811027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18407357959219223373270485 431422452169200547811027)
                  ·
                    rfl

theorem cell23_7561730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_7561730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561730 prefixEnd_7561730 := by exact prefixLift 7561730
  have htrace : WordTrace (prefixWord ++ tailWord_7561730) baseStart_7561730 baseEnd_7561730 := by
    simpa [prefixWord, tailWord_7561730, baseEnd_7561730] using wordTrace_append hprefix tailTrace_7561730
  have hstable : (prefixWord ++ tailWord_7561730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561730).length < 2 ^ (prefixWord ++ tailWord_7561730).sum := by decide
  have hdescent : baseEnd_7561730 < baseStart_7561730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561741 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7561741 : Nat := 118140960795 + 7561741 * 2 ^ 59
def prefixEnd_7561741 : Nat := 4983230072969 + 3 ^ 40 * 7561741 * 2
def baseEnd_7561741 : Nat := 3882807717810004387261693

theorem tailTrace_7561741 : CollatzResearch.WordTrace tailWord_7561741 prefixEnd_7561741 3882807717810004387261693 := by
  unfold tailWord_7561741
  simp only [CollatzResearch.WordTrace]
  refine ⟨275799352098111274390917077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183866234732074182927278051 275799352098111274390917077)
  ·
    refine ⟨6464047314799482993537119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 275799352098111274390917077 6464047314799482993537119)
    ·
      refine ⟨9696070972199224490305679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6464047314799482993537119 9696070972199224490305679)
      ·
        refine ⟨14544106458298836735458519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9696070972199224490305679 14544106458298836735458519)
        ·
          refine ⟨21816159687448255103187779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14544106458298836735458519 21816159687448255103187779)
          ·
            refine ⟨32724239531172382654781669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21816159687448255103187779 32724239531172382654781669)
            ·
              refine ⟨6135794912094821747771563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32724239531172382654781669 6135794912094821747771563)
              ·
                refine ⟨9203692368142232621657345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6135794912094821747771563 9203692368142232621657345)
                ·
                  refine ⟨6902769276106674466243009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9203692368142232621657345 6902769276106674466243009)
                  ·
                    refine ⟨5177076957080005849682257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6902769276106674466243009 5177076957080005849682257)
                    ·
                      refine ⟨3882807717810004387261693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177076957080005849682257 3882807717810004387261693)
                      ·
                        rfl

theorem cell23_7561741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7561741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561741 prefixEnd_7561741 := by exact prefixLift 7561741
  have htrace : WordTrace (prefixWord ++ tailWord_7561741) baseStart_7561741 baseEnd_7561741 := by
    simpa [prefixWord, tailWord_7561741, baseEnd_7561741] using wordTrace_append hprefix tailTrace_7561741
  have hstable : (prefixWord ++ tailWord_7561741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561741).length < 2 ^ (prefixWord ++ tailWord_7561741).sum := by decide
  have hdescent : baseEnd_7561741 < baseStart_7561741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561759 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_7561759 : Nat := 118140960795 + 7561759 * 2 ^ 59
def prefixEnd_7561759 : Nat := 4983230072969 + 3 ^ 40 * 7561759 * 2
def baseEnd_7561759 : Nat := 3882816960461785316836609

theorem tailTrace_7561759 : CollatzResearch.WordTrace tailWord_7561759 prefixEnd_7561759 3882816960461785316836609 := by
  unfold tailWord_7561759
  simp only [CollatzResearch.WordTrace]
  refine ⟨275800008612046063465072331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183866672408030708976714887 275800008612046063465072331)
  ·
    refine ⟨413700012918069095197608497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275800008612046063465072331 413700012918069095197608497)
    ·
      refine ⟨310275009688551821398206373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413700012918069095197608497 310275009688551821398206373)
      ·
        refine ⟨58176564316603466512163695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310275009688551821398206373 58176564316603466512163695)
        ·
          refine ⟨87264846474905199768245543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58176564316603466512163695 87264846474905199768245543)
          ·
            refine ⟨130897269712357799652368315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87264846474905199768245543 130897269712357799652368315)
            ·
              refine ⟨196345904568536699478552473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130897269712357799652368315 196345904568536699478552473)
              ·
                refine ⟨147259428426402524608914355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196345904568536699478552473 147259428426402524608914355)
                ·
                  refine ⟨220889142639603786913371533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147259428426402524608914355 220889142639603786913371533)
                  ·
                    refine ⟨82833428489851420092514325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220889142639603786913371533 82833428489851420092514325)
                    ·
                      refine ⟨3882816960461785316836609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82833428489851420092514325 3882816960461785316836609)
                      ·
                        rfl

theorem cell23_7561759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_7561759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561759 prefixEnd_7561759 := by exact prefixLift 7561759
  have htrace : WordTrace (prefixWord ++ tailWord_7561759) baseStart_7561759 baseEnd_7561759 := by
    simpa [prefixWord, tailWord_7561759, baseEnd_7561759] using wordTrace_append hprefix tailTrace_7561759
  have hstable : (prefixWord ++ tailWord_7561759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561759).length < 2 ^ (prefixWord ++ tailWord_7561759).sum := by decide
  have hdescent : baseEnd_7561759 < baseStart_7561759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561763 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 4]
def baseStart_7561763 : Nat := 118140960795 + 7561763 * 2 ^ 59
def prefixEnd_7561763 : Nat := 4983230072969 + 3 ^ 40 * 7561763 * 2
def baseEnd_7561763 : Nat := 3882819014384403301186591

theorem tailTrace_7561763 : CollatzResearch.WordTrace tailWord_7561763 prefixEnd_7561763 3882819014384403301186591 := by
  unfold tailWord_7561763
  simp only [CollatzResearch.WordTrace]
  refine ⟨275800154504031572148217943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183866769669354381432145295 275800154504031572148217943)
  ·
    refine ⟨413700231756047358222326915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275800154504031572148217943 413700231756047358222326915)
    ·
      refine ⟨620550347634071037333490373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413700231756047358222326915 620550347634071037333490373)
      ·
        refine ⟨116353190181388319500029445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 620550347634071037333490373 116353190181388319500029445)
        ·
          refine ⟨21816223159010309906255521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116353190181388319500029445 21816223159010309906255521)
          ·
            refine ⟨16362167369257732429691641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21816223159010309906255521 16362167369257732429691641)
            ·
              refine ⟨12271625526943299322268731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16362167369257732429691641 12271625526943299322268731)
              ·
                refine ⟨18407438290414948983403097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12271625526943299322268731 18407438290414948983403097)
                ·
                  refine ⟨13805578717811211737552323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18407438290414948983403097 13805578717811211737552323)
                  ·
                    refine ⟨20708368076716817606328485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13805578717811211737552323 20708368076716817606328485)
                    ·
                      refine ⟨3882819014384403301186591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20708368076716817606328485 3882819014384403301186591)
                      ·
                        rfl

theorem cell23_7561763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_7561763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561763 prefixEnd_7561763 := by exact prefixLift 7561763
  have htrace : WordTrace (prefixWord ++ tailWord_7561763) baseStart_7561763 baseEnd_7561763 := by
    simpa [prefixWord, tailWord_7561763, baseEnd_7561763] using wordTrace_append hprefix tailTrace_7561763
  have hstable : (prefixWord ++ tailWord_7561763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561763).length < 2 ^ (prefixWord ++ tailWord_7561763).sum := by decide
  have hdescent : baseEnd_7561763 < baseStart_7561763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561786 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 6]
def baseStart_7561786 : Nat := 118140960795 + 7561786 * 2 ^ 59
def prefixEnd_7561786 : Nat := 4983230072969 + 3 ^ 40 * 7561786 * 2
def baseEnd_7561786 : Nat := 431425647159939634577665

theorem tailTrace_7561786 : CollatzResearch.WordTrace tailWord_7561786 prefixEnd_7561786 431425647159939634577665 := by
  unfold tailWord_7561786
  simp only [CollatzResearch.WordTrace]
  refine ⟨68950248345737061769076303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183867328921965498050870141 68950248345737061769076303)
  ·
    refine ⟨103425372518605592653614455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68950248345737061769076303 103425372518605592653614455)
    ·
      refine ⟨155138058777908388980421683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103425372518605592653614455 155138058777908388980421683)
      ·
        refine ⟨232707088166862583470632525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155138058777908388980421683 232707088166862583470632525)
        ·
          refine ⟨87265158062573468801487197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232707088166862583470632525 87265158062573468801487197)
          ·
            refine ⟨32724434273465050800557699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87265158062573468801487197 32724434273465050800557699)
            ·
              refine ⟨49086651410197576200836549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32724434273465050800557699 49086651410197576200836549)
              ·
                refine ⟨9203747139412045537656853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49086651410197576200836549 9203747139412045537656853)
                ·
                  refine ⟨431425647159939634577665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9203747139412045537656853 431425647159939634577665)
                  ·
                    rfl

theorem cell23_7561786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_7561786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561786 prefixEnd_7561786 := by exact prefixLift 7561786
  have htrace : WordTrace (prefixWord ++ tailWord_7561786) baseStart_7561786 baseEnd_7561786 := by
    simpa [prefixWord, tailWord_7561786, baseEnd_7561786] using wordTrace_append hprefix tailTrace_7561786
  have hstable : (prefixWord ++ tailWord_7561786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561786).length < 2 ^ (prefixWord ++ tailWord_7561786).sum := by decide
  have hdescent : baseEnd_7561786 < baseStart_7561786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561813 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_7561813 : Nat := 118140960795 + 7561813 * 2 ^ 59
def prefixEnd_7561813 : Nat := 4983230072969 + 3 ^ 40 * 7561813 * 2
def baseEnd_7561813 : Nat := 3882844688417128105561361

theorem tailTrace_7561813 : CollatzResearch.WordTrace tailWord_7561813 prefixEnd_7561813 3882844688417128105561361 := by
  unfold tailWord_7561813
  simp only [CollatzResearch.WordTrace]
  refine ⟨275801978153850430687538093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183867985435900287125025395 275801978153850430687538093)
  ·
    refine ⟨103425741807693911507826785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275801978153850430687538093 103425741807693911507826785)
    ·
      refine ⟨77569306355770433630870089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103425741807693911507826785 77569306355770433630870089)
      ·
        refine ⟨58176979766827825223152567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77569306355770433630870089 58176979766827825223152567)
        ·
          refine ⟨87265469650241737834728851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58176979766827825223152567 87265469650241737834728851)
          ·
            refine ⟨130898204475362606752093277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87265469650241737834728851 130898204475362606752093277)
            ·
              refine ⟨49086826678260977532034979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130898204475362606752093277 49086826678260977532034979)
              ·
                refine ⟨73630240017391466298052469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49086826678260977532034979 73630240017391466298052469)
                ·
                  refine ⟨6902835001630449965442419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73630240017391466298052469 6902835001630449965442419)
                  ·
                    refine ⟨10354252502445674948163629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6902835001630449965442419 10354252502445674948163629)
                    ·
                      refine ⟨3882844688417128105561361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10354252502445674948163629 3882844688417128105561361)
                      ·
                        rfl

theorem cell23_7561813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_7561813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561813 prefixEnd_7561813 := by exact prefixLift 7561813
  have htrace : WordTrace (prefixWord ++ tailWord_7561813) baseStart_7561813 baseEnd_7561813 := by
    simpa [prefixWord, tailWord_7561813, baseEnd_7561813] using wordTrace_append hprefix tailTrace_7561813
  have hstable : (prefixWord ++ tailWord_7561813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561813).length < 2 ^ (prefixWord ++ tailWord_7561813).sum := by decide
  have hdescent : baseEnd_7561813 < baseStart_7561813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561816 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 3, 5]
def baseStart_7561816 : Nat := 118140960795 + 7561816 * 2 ^ 59
def prefixEnd_7561816 : Nat := 4983230072969 + 3 ^ 40 * 7561816 * 2
def baseEnd_7561816 : Nat := 1294282076286363864607949

theorem tailTrace_7561816 : CollatzResearch.WordTrace tailWord_7561816 prefixEnd_7561816 1294282076286363864607949 := by
  unfold tailWord_7561816
  simp only [CollatzResearch.WordTrace]
  refine ⟨137901043786419781099948651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183868058381893041466598201 137901043786419781099948651)
  ·
    refine ⟨206851565679629671649922977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137901043786419781099948651 206851565679629671649922977)
    ·
      refine ⟨155138674259722253737442233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206851565679629671649922977 155138674259722253737442233)
      ·
        refine ⟨116354005694791690303081675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155138674259722253737442233 116354005694791690303081675)
        ·
          refine ⟨174531008542187535454622513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116354005694791690303081675 174531008542187535454622513)
          ·
            refine ⟨130898256406640651590966885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174531008542187535454622513 130898256406640651590966885)
            ·
              refine ⟨24543423076245122173306291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130898256406640651590966885 24543423076245122173306291)
              ·
                refine ⟨36815134614367683259959437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24543423076245122173306291 36815134614367683259959437)
                ·
                  refine ⟨13805675480387881222484789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36815134614367683259959437 13805675480387881222484789)
                  ·
                    refine ⟨1294282076286363864607949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13805675480387881222484789 1294282076286363864607949)
                    ·
                      rfl

theorem cell23_7561816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_7561816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561816 prefixEnd_7561816 := by exact prefixLift 7561816
  have htrace : WordTrace (prefixWord ++ tailWord_7561816) baseStart_7561816 baseEnd_7561816 := by
    simpa [prefixWord, tailWord_7561816, baseEnd_7561816] using wordTrace_append hprefix tailTrace_7561816
  have hstable : (prefixWord ++ tailWord_7561816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561816).length < 2 ^ (prefixWord ++ tailWord_7561816).sum := by decide
  have hdescent : baseEnd_7561816 < baseStart_7561816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561856 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_7561856 : Nat := 118140960795 + 7561856 * 2 ^ 59
def prefixEnd_7561856 : Nat := 4983230072969 + 3 ^ 40 * 7561856 * 2
def baseEnd_7561856 : Nat := 3882866768085271437323663

theorem tailTrace_7561856 : CollatzResearch.WordTrace tailWord_7561856 prefixEnd_7561856 3882866768085271437323663 := by
  unfold tailWord_7561856
  simp only [CollatzResearch.WordTrace]
  refine ⟨137901773246347324515676711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183869030995129766020902281 137901773246347324515676711)
  ·
    refine ⟨206852659869520986773515067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137901773246347324515676711 206852659869520986773515067)
    ·
      refine ⟨310278989804281480160272601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206852659869520986773515067 310278989804281480160272601)
      ·
        refine ⟨232709242353211110120204451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310278989804281480160272601 232709242353211110120204451)
        ·
          refine ⟨349063863529816665180306677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232709242353211110120204451 349063863529816665180306677)
          ·
            refine ⟨32724737205920312360653751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349063863529816665180306677 32724737205920312360653751)
            ·
              refine ⟨49087105808880468540980627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32724737205920312360653751 49087105808880468540980627)
              ·
                refine ⟨73630658713320702811470941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49087105808880468540980627 73630658713320702811470941)
                ·
                  refine ⟨27611497017495263554301603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73630658713320702811470941 27611497017495263554301603)
                  ·
                    refine ⟨41417245526242895331452405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27611497017495263554301603 41417245526242895331452405)
                    ·
                      refine ⟨3882866768085271437323663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41417245526242895331452405 3882866768085271437323663)
                      ·
                        rfl

theorem cell23_7561856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_7561856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561856 prefixEnd_7561856 := by exact prefixLift 7561856
  have htrace : WordTrace (prefixWord ++ tailWord_7561856) baseStart_7561856 baseEnd_7561856 := by
    simpa [prefixWord, tailWord_7561856, baseEnd_7561856] using wordTrace_append hprefix tailTrace_7561856
  have hstable : (prefixWord ++ tailWord_7561856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561856).length < 2 ^ (prefixWord ++ tailWord_7561856).sum := by decide
  have hdescent : baseEnd_7561856 < baseStart_7561856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561870 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_7561870 : Nat := 118140960795 + 7561870 * 2 ^ 59
def prefixEnd_7561870 : Nat := 4983230072969 + 3 ^ 40 * 7561870 * 2
def baseEnd_7561870 : Nat := 3882873956814434382548599

theorem tailTrace_7561870 : CollatzResearch.WordTrace tailWord_7561870 prefixEnd_7561870 3882873956814434382548599 := by
  unfold tailWord_7561870
  simp only [CollatzResearch.WordTrace]
  refine ⟨34475507139330491177795383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183869371409762619614908709 34475507139330491177795383)
  ·
    refine ⟨51713260708995736766693075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34475507139330491177795383 51713260708995736766693075)
    ·
      refine ⟨77569891063493605150039613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51713260708995736766693075 77569891063493605150039613)
      ·
        refine ⟨29088709148810101931264855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77569891063493605150039613 29088709148810101931264855)
        ·
          refine ⟨43633063723215152896897283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29088709148810101931264855 43633063723215152896897283)
          ·
            refine ⟨65449595584822729345345925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43633063723215152896897283 65449595584822729345345925)
            ·
              refine ⟨12271799172154261752252361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65449595584822729345345925 12271799172154261752252361)
              ·
                refine ⟨9203849379115696314189271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12271799172154261752252361 9203849379115696314189271)
                ·
                  refine ⟨13805774068673544471283907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9203849379115696314189271 13805774068673544471283907)
                  ·
                    refine ⟨20708661103010316706925861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13805774068673544471283907 20708661103010316706925861)
                    ·
                      refine ⟨3882873956814434382548599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20708661103010316706925861 3882873956814434382548599)
                      ·
                        rfl

theorem cell23_7561870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_7561870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561870 prefixEnd_7561870 := by exact prefixLift 7561870
  have htrace : WordTrace (prefixWord ++ tailWord_7561870) baseStart_7561870 baseEnd_7561870 := by
    simpa [prefixWord, tailWord_7561870, baseEnd_7561870] using wordTrace_append hprefix tailTrace_7561870
  have hstable : (prefixWord ++ tailWord_7561870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561870).length < 2 ^ (prefixWord ++ tailWord_7561870).sum := by decide
  have hdescent : baseEnd_7561870 < baseStart_7561870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561898 : List Nat := [3, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7561898 : Nat := 118140960795 + 7561898 * 2 ^ 59
def prefixEnd_7561898 : Nat := 4983230072969 + 3 ^ 40 * 7561898 * 2
def baseEnd_7561898 : Nat := 3882888334272760272998471

theorem tailTrace_7561898 : CollatzResearch.WordTrace tailWord_7561898 prefixEnd_7561898 3882888334272760272998471 := by
  unfold tailWord_7561898
  simp only [CollatzResearch.WordTrace]
  refine ⟨68951269589635622551095587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183870052239028326802921565 68951269589635622551095587)
  ·
    refine ⟨103426904384453433826643381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68951269589635622551095587 103426904384453433826643381)
    ·
      refine ⟨9696272286042509421247817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103426904384453433826643381 9696272286042509421247817)
      ·
        refine ⟨7272204214531882065935863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9696272286042509421247817 7272204214531882065935863)
        ·
          refine ⟨10908306321797823098903795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7272204214531882065935863 10908306321797823098903795)
          ·
            refine ⟨16362459482696734648355693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10908306321797823098903795 16362459482696734648355693)
            ·
              refine ⟨6135922306011275493133385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16362459482696734648355693 6135922306011275493133385)
              ·
                refine ⟨4601941729508456619850039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6135922306011275493133385 4601941729508456619850039)
                ·
                  refine ⟨6902912594262684929775059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601941729508456619850039 6902912594262684929775059)
                  ·
                    refine ⟨10354368891394027394662589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6902912594262684929775059 10354368891394027394662589)
                    ·
                      refine ⟨3882888334272760272998471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10354368891394027394662589 3882888334272760272998471)
                      ·
                        rfl

theorem cell23_7561898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7561898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561898 prefixEnd_7561898 := by exact prefixLift 7561898
  have htrace : WordTrace (prefixWord ++ tailWord_7561898) baseStart_7561898 baseEnd_7561898 := by
    simpa [prefixWord, tailWord_7561898, baseEnd_7561898] using wordTrace_append hprefix tailTrace_7561898
  have hstable : (prefixWord ++ tailWord_7561898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561898).length < 2 ^ (prefixWord ++ tailWord_7561898).sum := by decide
  have hdescent : baseEnd_7561898 < baseStart_7561898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561906 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_7561906 : Nat := 118140960795 + 7561906 * 2 ^ 59
def prefixEnd_7561906 : Nat := 4983230072969 + 3 ^ 40 * 7561906 * 2
def baseEnd_7561906 : Nat := 1294297480705998747232811

theorem tailTrace_7561906 : CollatzResearch.WordTrace tailWord_7561906 prefixEnd_7561906 1294297480705998747232811 := by
  unfold tailWord_7561906
  simp only [CollatzResearch.WordTrace]
  refine ⟨68951342535628376892668393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183870246761675671713782381 68951342535628376892668393)
  ·
    refine ⟨51713506901721282669501295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68951342535628376892668393 51713506901721282669501295)
    ·
      refine ⟨77570260352581924004251943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51713506901721282669501295 77570260352581924004251943)
      ·
        refine ⟨116355390528872886006377915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77570260352581924004251943 116355390528872886006377915)
        ·
          refine ⟨174533085793309329009566873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116355390528872886006377915 174533085793309329009566873)
          ·
            refine ⟨130899814344981996757175155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174533085793309329009566873 130899814344981996757175155)
            ·
              refine ⟨196349721517472995135762733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130899814344981996757175155 196349721517472995135762733)
              ·
                refine ⟨73631145569052373175911025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196349721517472995135762733 73631145569052373175911025)
                ·
                  refine ⟨55223359176789279881933269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73631145569052373175911025 55223359176789279881933269)
                  ·
                    refine ⟨1294297480705998747232811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55223359176789279881933269 1294297480705998747232811)
                    ·
                      rfl

theorem cell23_7561906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_7561906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561906 prefixEnd_7561906 := by exact prefixLift 7561906
  have htrace : WordTrace (prefixWord ++ tailWord_7561906) baseStart_7561906 baseEnd_7561906 := by
    simpa [prefixWord, tailWord_7561906, baseEnd_7561906] using wordTrace_append hprefix tailTrace_7561906
  have hstable : (prefixWord ++ tailWord_7561906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561906).length < 2 ^ (prefixWord ++ tailWord_7561906).sum := by decide
  have hdescent : baseEnd_7561906 < baseStart_7561906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561913 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 2, 7, 2]
def baseStart_7561913 : Nat := 118140960795 + 7561913 * 2 ^ 59
def prefixEnd_7561913 : Nat := 4983230072969 + 3 ^ 40 * 7561913 * 2
def baseEnd_7561913 : Nat := 3882896036482577714310901

theorem tailTrace_7561913 : CollatzResearch.WordTrace tailWord_7561913 prefixEnd_7561913 3882896036482577714310901 := by
  unfold tailWord_7561913
  simp only [CollatzResearch.WordTrace]
  refine ⟨275805625453488147766178393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183870416968992098510785595 275805625453488147766178393)
  ·
    refine ⟨206854219090116110824633795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275805625453488147766178393 206854219090116110824633795)
    ·
      refine ⟨310281328635174166236950693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206854219090116110824633795 310281328635174166236950693)
      ·
        refine ⟨58177749119095156169428255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310281328635174166236950693 58177749119095156169428255)
        ·
          refine ⟨87266623678642734254142383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58177749119095156169428255 87266623678642734254142383)
          ·
            refine ⟨130899935517964101381213575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87266623678642734254142383 130899935517964101381213575)
            ·
              refine ⟨196349903276946152071820363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130899935517964101381213575 196349903276946152071820363)
              ·
                refine ⟨294524854915419228107730545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196349903276946152071820363 294524854915419228107730545)
                ·
                  refine ⟨220893641186564421080797909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294524854915419228107730545 220893641186564421080797909)
                  ·
                    refine ⟨5177194715310103619081201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 220893641186564421080797909 5177194715310103619081201)
                    ·
                      refine ⟨3882896036482577714310901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177194715310103619081201 3882896036482577714310901)
                      ·
                        rfl

theorem cell23_7561913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_7561913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561913 prefixEnd_7561913 := by exact prefixLift 7561913
  have htrace : WordTrace (prefixWord ++ tailWord_7561913) baseStart_7561913 baseEnd_7561913 := by
    simpa [prefixWord, tailWord_7561913, baseEnd_7561913] using wordTrace_append hprefix tailTrace_7561913
  have hstable : (prefixWord ++ tailWord_7561913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561913).length < 2 ^ (prefixWord ++ tailWord_7561913).sum := by decide
  have hdescent : baseEnd_7561913 < baseStart_7561913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561921 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7561921 : Nat := 118140960795 + 7561921 * 2 ^ 59
def prefixEnd_7561921 : Nat := 4983230072969 + 3 ^ 40 * 7561921 * 2
def baseEnd_7561921 : Nat := 3882900144327813683010865

theorem tailTrace_7561921 : CollatzResearch.WordTrace tailWord_7561921 prefixEnd_7561921 3882900144327813683010865 := by
  unfold tailWord_7561921
  simp only [CollatzResearch.WordTrace]
  refine ⟨275805917237459165132469617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183870611491639443421646411 275805917237459165132469617)
  ·
    refine ⟨206854437928094373849352213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275805917237459165132469617 206854437928094373849352213)
    ·
      refine ⟨9696301777879423774188385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206854437928094373849352213 9696301777879423774188385)
      ·
        refine ⟨7272226333409567830641289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9696301777879423774188385 7272226333409567830641289)
        ·
          refine ⟨5454169750057175872980967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7272226333409567830641289 5454169750057175872980967)
          ·
            refine ⟨8181254625085763809471451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454169750057175872980967 8181254625085763809471451)
            ·
              refine ⟨12271881937628645714207177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181254625085763809471451 12271881937628645714207177)
              ·
                refine ⟨9203911453221484285655383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12271881937628645714207177 9203911453221484285655383)
                ·
                  refine ⟨13805867179832226428483075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9203911453221484285655383 13805867179832226428483075)
                  ·
                    refine ⟨20708800769748339642724613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13805867179832226428483075 20708800769748339642724613)
                    ·
                      refine ⟨3882900144327813683010865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20708800769748339642724613 3882900144327813683010865)
                      ·
                        rfl

theorem cell23_7561921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7561921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7561921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7561921 prefixEnd_7561921 := by exact prefixLift 7561921
  have htrace : WordTrace (prefixWord ++ tailWord_7561921) baseStart_7561921 baseEnd_7561921 := by
    simpa [prefixWord, tailWord_7561921, baseEnd_7561921] using wordTrace_append hprefix tailTrace_7561921
  have hstable : (prefixWord ++ tailWord_7561921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561921).length < 2 ^ (prefixWord ++ tailWord_7561921).sum := by decide
  have hdescent : baseEnd_7561921 < baseStart_7561921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562030 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_7562030 : Nat := 118140960795 + 7562030 * 2 ^ 59
def prefixEnd_7562030 : Nat := 4983230072969 + 3 ^ 40 * 7562030 * 2
def baseEnd_7562030 : Nat := 1294318704573051252182621

theorem tailTrace_7562030 : CollatzResearch.WordTrace tailWord_7562030 prefixEnd_7562030 1294318704573051252182621 := by
  unfold tailWord_7562030
  simp only [CollatzResearch.WordTrace]
  refine ⟨34476236599258034593523443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183873261862709517832125029 34476236599258034593523443)
  ·
    refine ⟨51714354898887051890285165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34476236599258034593523443 51714354898887051890285165)
    ·
      refine ⟨19392883087082644458856937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51714354898887051890285165 19392883087082644458856937)
      ·
        refine ⟨14544662315311983344142703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19392883087082644458856937 14544662315311983344142703)
        ·
          refine ⟨21816993472967975016214055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14544662315311983344142703 21816993472967975016214055)
          ·
            refine ⟨32725490209451962524321083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21816993472967975016214055 32725490209451962524321083)
            ·
              refine ⟨49088235314177943786481625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32725490209451962524321083 49088235314177943786481625)
              ·
                refine ⟨36816176485633457839861219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49088235314177943786481625 36816176485633457839861219)
                ·
                  refine ⟨55224264728450186759791829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36816176485633457839861219 55224264728450186759791829)
                  ·
                    refine ⟨1294318704573051252182621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55224264728450186759791829 1294318704573051252182621)
                    ·
                      rfl

theorem cell23_7562030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_7562030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562030 prefixEnd_7562030 := by exact prefixLift 7562030
  have htrace : WordTrace (prefixWord ++ tailWord_7562030) baseStart_7562030 baseEnd_7562030 := by
    simpa [prefixWord, tailWord_7562030, baseEnd_7562030] using wordTrace_append hprefix tailTrace_7562030
  have hstable : (prefixWord ++ tailWord_7562030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562030).length < 2 ^ (prefixWord ++ tailWord_7562030).sum := by decide
  have hdescent : baseEnd_7562030 < baseStart_7562030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562033 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_7562033 : Nat := 118140960795 + 7562033 * 2 ^ 59
def prefixEnd_7562033 : Nat := 4983230072969 + 3 ^ 40 * 7562033 * 2
def baseEnd_7562033 : Nat := 3882957654161117244810349

theorem tailTrace_7562033 : CollatzResearch.WordTrace tailWord_7562033 prefixEnd_7562033 3882957654161117244810349 := by
  unfold tailWord_7562033
  simp only [CollatzResearch.WordTrace]
  refine ⟨275810002213053408260546753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183873334808702272173697835 275810002213053408260546753)
  ·
    refine ⟨206857501659790056195410065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275810002213053408260546753 206857501659790056195410065)
    ·
      refine ⟨155143126244842542146557549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206857501659790056195410065 155143126244842542146557549)
      ·
        refine ⟨58178672341815953304959081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155143126244842542146557549 58178672341815953304959081)
        ·
          refine ⟨43634004256361964978719311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58178672341815953304959081 43634004256361964978719311)
          ·
            refine ⟨65451006384542947468078967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43634004256361964978719311 65451006384542947468078967)
            ·
              refine ⟨98176509576814421202118451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65451006384542947468078967 98176509576814421202118451)
              ·
                refine ⟨147264764365221631803177677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98176509576814421202118451 147264764365221631803177677)
                ·
                  refine ⟨55224286636958111926191629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147264764365221631803177677 55224286636958111926191629)
                  ·
                    refine ⟨20709107488859291972321861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55224286636958111926191629 20709107488859291972321861)
                    ·
                      refine ⟨3882957654161117244810349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20709107488859291972321861 3882957654161117244810349)
                      ·
                        rfl

theorem cell23_7562033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_7562033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562033 prefixEnd_7562033 := by exact prefixLift 7562033
  have htrace : WordTrace (prefixWord ++ tailWord_7562033) baseStart_7562033 baseEnd_7562033 := by
    simpa [prefixWord, tailWord_7562033, baseEnd_7562033] using wordTrace_append hprefix tailTrace_7562033
  have hstable : (prefixWord ++ tailWord_7562033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562033).length < 2 ^ (prefixWord ++ tailWord_7562033).sum := by decide
  have hdescent : baseEnd_7562033 < baseStart_7562033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562073 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 8]
def baseStart_7562073 : Nat := 118140960795 + 7562073 * 2 ^ 59
def prefixEnd_7562073 : Nat := 4983230072969 + 3 ^ 40 * 7562073 * 2
def baseEnd_7562073 : Nat := 431442021487477454256685

theorem tailTrace_7562073 : CollatzResearch.WordTrace tailWord_7562073 prefixEnd_7562073 431442021487477454256685 := by
  unfold tailWord_7562073
  simp only [CollatzResearch.WordTrace]
  refine ⟨275811461132908495092002873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183874307421938996728001915 275811461132908495092002873)
  ·
    refine ⟨206858595849681371319002155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275811461132908495092002873 206858595849681371319002155)
    ·
      refine ⟨310287893774522056978503233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206858595849681371319002155 310287893774522056978503233)
      ·
        refine ⟨232715920330891542733877425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310287893774522056978503233 232715920330891542733877425)
        ·
          refine ⟨174536940248168657050408069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232715920330891542733877425 174536940248168657050408069)
          ·
            refine ⟨32725676296531623196951513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174536940248168657050408069 32725676296531623196951513)
            ·
              refine ⟨24544257222398717397713635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32725676296531623196951513 24544257222398717397713635)
              ·
                refine ⟨36816385833598076096570453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24544257222398717397713635 36816385833598076096570453)
                ·
                  refine ⟨431442021487477454256685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36816385833598076096570453 431442021487477454256685)
                  ·
                    rfl

theorem cell23_7562073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 8].length) (baseStart_7562073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562073 prefixEnd_7562073 := by exact prefixLift 7562073
  have htrace : WordTrace (prefixWord ++ tailWord_7562073) baseStart_7562073 baseEnd_7562073 := by
    simpa [prefixWord, tailWord_7562073, baseEnd_7562073] using wordTrace_append hprefix tailTrace_7562073
  have hstable : (prefixWord ++ tailWord_7562073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562073).length < 2 ^ (prefixWord ++ tailWord_7562073).sum := by decide
  have hdescent : baseEnd_7562073 < baseStart_7562073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562161 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 2, 3, 2]
def baseStart_7562161 : Nat := 118140960795 + 7562161 * 2 ^ 59
def prefixEnd_7562161 : Nat := 4983230072969 + 3 ^ 40 * 7562161 * 2
def baseEnd_7562161 : Nat := 3883023379684892744009761

theorem tailTrace_7562161 : CollatzResearch.WordTrace tailWord_7562161 prefixEnd_7562161 3883023379684892744009761 := by
  unfold tailWord_7562161
  simp only [CollatzResearch.WordTrace]
  refine ⟨275814670756589686121206337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183876447171059790747470891 275814670756589686121206337)
  ·
    refine ⟨206861003067442264590904753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275814670756589686121206337 206861003067442264590904753)
    ·
      refine ⟨155145752300581698443178565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206861003067442264590904753 155145752300581698443178565)
      ·
        refine ⟨29089828556359068458095981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155145752300581698443178565 29089828556359068458095981)
        ·
          refine ⟨10908685708634650671785993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29089828556359068458095981 10908685708634650671785993)
          ·
            refine ⟨8181514281475988003839495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10908685708634650671785993 8181514281475988003839495)
            ·
              refine ⟨12272271422213982005759243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181514281475988003839495 12272271422213982005759243)
              ·
                refine ⟨18408407133320973008638865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12272271422213982005759243 18408407133320973008638865)
                ·
                  refine ⟨13806305349990729756479149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18408407133320973008638865 13806305349990729756479149)
                  ·
                    refine ⟨5177364506246523658679681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13806305349990729756479149 5177364506246523658679681)
                    ·
                      refine ⟨3883023379684892744009761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177364506246523658679681 3883023379684892744009761)
                      ·
                        rfl

theorem cell23_7562161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_7562161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562161 prefixEnd_7562161 := by exact prefixLift 7562161
  have htrace : WordTrace (prefixWord ++ tailWord_7562161) baseStart_7562161 baseEnd_7562161 := by
    simpa [prefixWord, tailWord_7562161, baseEnd_7562161] using wordTrace_append hprefix tailTrace_7562161
  have hstable : (prefixWord ++ tailWord_7562161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562161).length < 2 ^ (prefixWord ++ tailWord_7562161).sum := by decide
  have hdescent : baseEnd_7562161 < baseStart_7562161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562170 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_7562170 : Nat := 118140960795 + 7562170 * 2 ^ 59
def prefixEnd_7562170 : Nat := 4983230072969 + 3 ^ 40 * 7562170 * 2
def baseEnd_7562170 : Nat := 3883028001010783208797219

theorem tailTrace_7562170 : CollatzResearch.WordTrace tailWord_7562170 prefixEnd_7562170 3883028001010783208797219 := by
  unfold tailWord_7562170
  simp only [CollatzResearch.WordTrace]
  refine ⟨68953749753389270164570991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183876666009038053772189309 68953749753389270164570991)
  ·
    refine ⟨103430624630083905246856487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68953749753389270164570991 103430624630083905246856487)
    ·
      refine ⟨155145936945125857870284731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103430624630083905246856487 155145936945125857870284731)
      ·
        refine ⟨232718905417688786805427097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155145936945125857870284731 232718905417688786805427097)
        ·
          refine ⟨174539179063266590104070323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232718905417688786805427097 174539179063266590104070323)
          ·
            refine ⟨261808768594899885156105485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174539179063266590104070323 261808768594899885156105485)
            ·
              refine ⟨98178288223087456933539557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261808768594899885156105485 98178288223087456933539557)
              ·
                refine ⟨18408429041828898175038667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98178288223087456933539557 18408429041828898175038667)
                ·
                  refine ⟨27612643562743347262558001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18408429041828898175038667 27612643562743347262558001)
                  ·
                    refine ⟨20709482672057510446918501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27612643562743347262558001 20709482672057510446918501)
                    ·
                      refine ⟨3883028001010783208797219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20709482672057510446918501 3883028001010783208797219)
                      ·
                        rfl

theorem cell23_7562170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_7562170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562170 prefixEnd_7562170 := by exact prefixLift 7562170
  have htrace : WordTrace (prefixWord ++ tailWord_7562170) baseStart_7562170 baseEnd_7562170 := by
    simpa [prefixWord, tailWord_7562170, baseEnd_7562170] using wordTrace_append hprefix tailTrace_7562170
  have hstable : (prefixWord ++ tailWord_7562170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562170).length < 2 ^ (prefixWord ++ tailWord_7562170).sum := by decide
  have hdescent : baseEnd_7562170 < baseStart_7562170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562174 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_7562174 : Nat := 118140960795 + 7562174 * 2 ^ 59
def prefixEnd_7562174 : Nat := 4983230072969 + 3 ^ 40 * 7562174 * 2
def baseEnd_7562174 : Nat := 3883030054933401193147201

theorem tailTrace_7562174 : CollatzResearch.WordTrace tailWord_7562174 prefixEnd_7562174 3883030054933401193147201 := by
  unfold tailWord_7562174
  simp only [CollatzResearch.WordTrace]
  refine ⟨34476893113192823667678697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183876763270361726227619717 34476893113192823667678697)
  ·
    refine ⟨25857669834894617750759023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34476893113192823667678697 25857669834894617750759023)
    ·
      refine ⟨38786504752341926626138535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25857669834894617750759023 38786504752341926626138535)
      ·
        refine ⟨58179757128512889939207803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38786504752341926626138535 58179757128512889939207803)
        ·
          refine ⟨87269635692769334908811705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58179757128512889939207803 87269635692769334908811705)
          ·
            refine ⟨65452226769577001181608779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87269635692769334908811705 65452226769577001181608779)
            ·
              refine ⟨98178340154365501772413169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65452226769577001181608779 98178340154365501772413169)
              ·
                refine ⟨73633755115774126329309877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98178340154365501772413169 73633755115774126329309877)
                ·
                  refine ⟨6903164542103824343372801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73633755115774126329309877 6903164542103824343372801)
                  ·
                    refine ⟨5177373406577868257529601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6903164542103824343372801 5177373406577868257529601)
                    ·
                      refine ⟨3883030054933401193147201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177373406577868257529601 3883030054933401193147201)
                      ·
                        rfl

theorem cell23_7562174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_7562174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562174 prefixEnd_7562174 := by exact prefixLift 7562174
  have htrace : WordTrace (prefixWord ++ tailWord_7562174) baseStart_7562174 baseEnd_7562174 := by
    simpa [prefixWord, tailWord_7562174, baseEnd_7562174] using wordTrace_append hprefix tailTrace_7562174
  have hstable : (prefixWord ++ tailWord_7562174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562174).length < 2 ^ (prefixWord ++ tailWord_7562174).sum := by decide
  have hdescent : baseEnd_7562174 < baseStart_7562174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562191 : List Nat := [1, 1, 2, 1, 1, 6, 2, 4, 1, 2, 2]
def baseStart_7562191 : Nat := 118140960795 + 7562191 * 2 ^ 59
def prefixEnd_7562191 : Nat := 4983230072969 + 3 ^ 40 * 7562191 * 2
def baseEnd_7562191 : Nat := 3883038784104527626634623

theorem tailTrace_7562191 : CollatzResearch.WordTrace tailWord_7562191 prefixEnd_7562191 3883038784104527626634623 := by
  unfold tailWord_7562191
  simp only [CollatzResearch.WordTrace]
  refine ⟨275815764946481001244798427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183877176630987334163198951 275815764946481001244798427)
  ·
    refine ⟨413723647419721501867197641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275815764946481001244798427 413723647419721501867197641)
    ·
      refine ⟨310292735564791126400398231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413723647419721501867197641 310292735564791126400398231)
      ·
        refine ⟨465439103347186689600597347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310292735564791126400398231 465439103347186689600597347)
        ·
          refine ⟨698158655020780034400896021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465439103347186689600597347 698158655020780034400896021)
          ·
            refine ⟨32726186954099064112542001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 698158655020780034400896021 32726186954099064112542001)
            ·
              refine ⟨24544640215574298084406501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32726186954099064112542001 24544640215574298084406501)
              ·
                refine ⟨4602120040420180890826219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24544640215574298084406501 4602120040420180890826219)
                ·
                  refine ⟨6903180060630271336239329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602120040420180890826219 6903180060630271336239329)
                  ·
                    refine ⟨5177385045472703502179497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6903180060630271336239329 5177385045472703502179497)
                    ·
                      refine ⟨3883038784104527626634623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177385045472703502179497 3883038784104527626634623)
                      ·
                        rfl

theorem cell23_7562191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 2, 2].length) (baseStart_7562191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562191 prefixEnd_7562191 := by exact prefixLift 7562191
  have htrace : WordTrace (prefixWord ++ tailWord_7562191) baseStart_7562191 baseEnd_7562191 := by
    simpa [prefixWord, tailWord_7562191, baseEnd_7562191] using wordTrace_append hprefix tailTrace_7562191
  have hstable : (prefixWord ++ tailWord_7562191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562191).length < 2 ^ (prefixWord ++ tailWord_7562191).sum := by decide
  have hdescent : baseEnd_7562191 < baseStart_7562191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562203 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 11]
def baseStart_7562203 : Nat := 118140960795 + 7562203 * 2 ^ 59
def prefixEnd_7562203 : Nat := 4983230072969 + 3 ^ 40 * 7562203 * 2
def baseEnd_7562203 : Nat := 3883044945872381579684567

theorem tailTrace_7562203 : CollatzResearch.WordTrace tailWord_7562203 prefixEnd_7562203 3883044945872381579684567 := by
  unfold tailWord_7562203
  simp only [CollatzResearch.WordTrace]
  refine ⟨275816202622437527294235263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183877468414958351529490175 275816202622437527294235263)
  ·
    refine ⟨413724303933656290941352895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275816202622437527294235263 413724303933656290941352895)
    ·
      refine ⟨620586455900484436412029343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413724303933656290941352895 620586455900484436412029343)
      ·
        refine ⟨930879683850726654618044015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620586455900484436412029343 930879683850726654618044015)
        ·
          refine ⟨1396319525776089981927066023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930879683850726654618044015 1396319525776089981927066023)
          ·
            refine ⟨2094479288664134972890599035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396319525776089981927066023 2094479288664134972890599035)
            ·
              refine ⟨3141718932996202459335898553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094479288664134972890599035 3141718932996202459335898553)
              ·
                refine ⟨2356289199747151844501923915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141718932996202459335898553 2356289199747151844501923915)
                ·
                  refine ⟨3534433799620727766752885873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356289199747151844501923915 3534433799620727766752885873)
                  ·
                    refine ⟨2650825349715545825064664405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3534433799620727766752885873 2650825349715545825064664405)
                    ·
                      refine ⟨3883044945872381579684567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2650825349715545825064664405 3883044945872381579684567)
                      ·
                        rfl

theorem cell23_7562203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_7562203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562203 prefixEnd_7562203 := by exact prefixLift 7562203
  have htrace : WordTrace (prefixWord ++ tailWord_7562203) baseStart_7562203 baseEnd_7562203 := by
    simpa [prefixWord, tailWord_7562203, baseEnd_7562203] using wordTrace_append hprefix tailTrace_7562203
  have hstable : (prefixWord ++ tailWord_7562203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562203).length < 2 ^ (prefixWord ++ tailWord_7562203).sum := by decide
  have hdescent : baseEnd_7562203 < baseStart_7562203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562242 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7562242 : Nat := 118140960795 + 7562242 * 2 ^ 59
def prefixEnd_7562242 : Nat := 4983230072969 + 3 ^ 40 * 7562242 * 2
def baseEnd_7562242 : Nat := 3883064971617906927096889

theorem tailTrace_7562242 : CollatzResearch.WordTrace tailWord_7562242 prefixEnd_7562242 3883064971617906927096889 := by
  unfold tailWord_7562242
  simp only [CollatzResearch.WordTrace]
  refine ⟨68954406267324059238726245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183878416712864157969936653 68954406267324059238726245)
  ·
    refine ⟨12928951175123261107261171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68954406267324059238726245 12928951175123261107261171)
    ·
      refine ⟨19393426762684891660891757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12928951175123261107261171 19393426762684891660891757)
      ·
        refine ⟨7272535036006834372834409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19393426762684891660891757 7272535036006834372834409)
        ·
          refine ⟨5454401277005125779625807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7272535036006834372834409 5454401277005125779625807)
          ·
            refine ⟨8181601915507688669438711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454401277005125779625807 8181601915507688669438711)
            ·
              refine ⟨12272402873261533004158067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181601915507688669438711 12272402873261533004158067)
              ·
                refine ⟨18408604309892299506237101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12272402873261533004158067 18408604309892299506237101)
                ·
                  refine ⟨6903226616209612314838913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18408604309892299506237101 6903226616209612314838913)
                  ·
                    refine ⟨5177419962157209236129185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6903226616209612314838913 5177419962157209236129185)
                    ·
                      refine ⟨3883064971617906927096889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177419962157209236129185 3883064971617906927096889)
                      ·
                        rfl

theorem cell23_7562242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7562242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562242 prefixEnd_7562242 := by exact prefixLift 7562242
  have htrace : WordTrace (prefixWord ++ tailWord_7562242) baseStart_7562242 baseEnd_7562242 := by
    simpa [prefixWord, tailWord_7562242, baseEnd_7562242] using wordTrace_append hprefix tailTrace_7562242
  have hstable : (prefixWord ++ tailWord_7562242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562242).length < 2 ^ (prefixWord ++ tailWord_7562242).sum := by decide
  have hdescent : baseEnd_7562242 < baseStart_7562242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562268 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_7562268 : Nat := 118140960795 + 7562268 * 2 ^ 59
def prefixEnd_7562268 : Nat := 4983230072969 + 3 ^ 40 * 7562268 * 2
def baseEnd_7562268 : Nat := 3883078322114923825371769

theorem tailTrace_7562268 : CollatzResearch.WordTrace tailWord_7562268 prefixEnd_7562268 3883078322114923825371769 := by
  unfold tailWord_7562268
  simp only [CollatzResearch.WordTrace]
  refine ⟨137909286683601021697675729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183879048911468028930234305 137909286683601021697675729)
  ·
    refine ⟨103431965012700766273256797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137909286683601021697675729 103431965012700766273256797)
    ·
      refine ⟨38786986879762787352471299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103431965012700766273256797 38786986879762787352471299)
      ·
        refine ⟨58180480319644181028706949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38786986879762787352471299 58180480319644181028706949)
        ·
          refine ⟨10908840059933283942882553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58180480319644181028706949 10908840059933283942882553)
          ·
            refine ⟨8181630044949962957161915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10908840059933283942882553 8181630044949962957161915)
            ·
              refine ⟨12272445067424944435742873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181630044949962957161915 12272445067424944435742873)
              ·
                refine ⟨9204333800568708326807155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12272445067424944435742873 9204333800568708326807155)
                ·
                  refine ⟨13806500700853062490210733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9204333800568708326807155 13806500700853062490210733)
                  ·
                    refine ⟨5177437762819898433829025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13806500700853062490210733 5177437762819898433829025)
                    ·
                      refine ⟨3883078322114923825371769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177437762819898433829025 3883078322114923825371769)
                      ·
                        rfl

theorem cell23_7562268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_7562268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562268 prefixEnd_7562268 := by exact prefixLift 7562268
  have htrace : WordTrace (prefixWord ++ tailWord_7562268) baseStart_7562268 baseEnd_7562268 := by
    simpa [prefixWord, tailWord_7562268, baseEnd_7562268] using wordTrace_append hprefix tailTrace_7562268
  have hstable : (prefixWord ++ tailWord_7562268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562268).length < 2 ^ (prefixWord ++ tailWord_7562268).sum := by decide
  have hdescent : baseEnd_7562268 < baseStart_7562268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562307 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 1, 7, 2]
def baseStart_7562307 : Nat := 118140960795 + 7562307 * 2 ^ 59
def prefixEnd_7562307 : Nat := 4983230072969 + 3 ^ 40 * 7562307 * 2
def baseEnd_7562307 : Nat := 3883098347860449172784089

theorem tailTrace_7562307 : CollatzResearch.WordTrace tailWord_7562307 prefixEnd_7562307 3883098347860449172784089 := by
  unfold tailWord_7562307
  simp only [CollatzResearch.WordTrace]
  refine ⟨275819995814060753056021175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183879997209373835370680783 275819995814060753056021175)
  ·
    refine ⟨413729993721091129584031763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275819995814060753056021175 413729993721091129584031763)
    ·
      refine ⟨620594990581636694376047645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413729993721091129584031763 620594990581636694376047645)
      ·
        refine ⟨232723121468113760391017867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620594990581636694376047645 232723121468113760391017867)
        ·
          refine ⟨349084682202170640586526801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232723121468113760391017867 349084682202170640586526801)
          ·
            refine ⟨261813511651627980439895101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349084682202170640586526801 261813511651627980439895101)
            ·
              refine ⟨98180066869360492664960663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261813511651627980439895101 98180066869360492664960663)
              ·
                refine ⟨147270100304040738997440995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98180066869360492664960663 147270100304040738997440995)
                ·
                  refine ⟨220905150456061108496161493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147270100304040738997440995 220905150456061108496161493)
                  ·
                    refine ⟨5177464463813932230378785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 220905150456061108496161493 5177464463813932230378785)
                    ·
                      refine ⟨3883098347860449172784089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177464463813932230378785 3883098347860449172784089)
                      ·
                        rfl

theorem cell23_7562307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_7562307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562307 prefixEnd_7562307 := by exact prefixLift 7562307
  have htrace : WordTrace (prefixWord ++ tailWord_7562307) baseStart_7562307 baseEnd_7562307 := by
    simpa [prefixWord, tailWord_7562307, baseEnd_7562307] using wordTrace_append hprefix tailTrace_7562307
  have hstable : (prefixWord ++ tailWord_7562307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562307).length < 2 ^ (prefixWord ++ tailWord_7562307).sum := by decide
  have hdescent : baseEnd_7562307 < baseStart_7562307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562330 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_7562330 : Nat := 118140960795 + 7562330 * 2 ^ 59
def prefixEnd_7562330 : Nat := 4983230072969 + 3 ^ 40 * 7562330 * 2
def baseEnd_7562330 : Nat := 1294370052638500860932161

theorem tailTrace_7562330 : CollatzResearch.WordTrace tailWord_7562330 prefixEnd_7562330 1294370052638500860932161 := by
  unfold tailWord_7562330
  simp only [CollatzResearch.WordTrace]
  refine ⟨68955208673244356996027111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183880556461984951989405629 68955208673244356996027111)
  ·
    refine ⟨103432813009866535494040667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68955208673244356996027111 103432813009866535494040667)
    ·
      refine ⟨155149219514799803241061001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103432813009866535494040667 155149219514799803241061001)
      ·
        refine ⟨116361914636099852430795751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155149219514799803241061001 116361914636099852430795751)
        ·
          refine ⟨174542871954149778646193627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116361914636099852430795751 174542871954149778646193627)
          ·
            refine ⟨261814307931224667969290441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174542871954149778646193627 261814307931224667969290441)
            ·
              refine ⟨196360730948418500976967831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261814307931224667969290441 196360730948418500976967831)
              ·
                refine ⟨294541096422627751465451747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196360730948418500976967831 294541096422627751465451747)
                ·
                  refine ⟨441811644633941627198177621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294541096422627751465451747 441811644633941627198177621)
                  ·
                    refine ⟨1294370052638500860932161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 441811644633941627198177621 1294370052638500860932161)
                    ·
                      rfl

theorem cell23_7562330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_7562330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562330 prefixEnd_7562330 := by exact prefixLift 7562330
  have htrace : WordTrace (prefixWord ++ tailWord_7562330) baseStart_7562330 baseEnd_7562330 := by
    simpa [prefixWord, tailWord_7562330, baseEnd_7562330] using wordTrace_append hprefix tailTrace_7562330
  have hstable : (prefixWord ++ tailWord_7562330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562330).length < 2 ^ (prefixWord ++ tailWord_7562330).sum := by decide
  have hdescent : baseEnd_7562330 < baseStart_7562330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562354 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_7562354 : Nat := 118140960795 + 7562354 * 2 ^ 59
def prefixEnd_7562354 : Nat := 4983230072969 + 3 ^ 40 * 7562354 * 2
def baseEnd_7562354 : Nat := 3883122481451210488896373

theorem tailTrace_7562354 : CollatzResearch.WordTrace tailWord_7562354 prefixEnd_7562354 3883122481451210488896373 := by
  unfold tailWord_7562354
  simp only [CollatzResearch.WordTrace]
  refine ⟨68955427511222620020745529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183881140029926986721988077 68955427511222620020745529)
  ·
    refine ⟨51716570633416965015559147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68955427511222620020745529 51716570633416965015559147)
    ·
      refine ⟨77574855950125447523338721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51716570633416965015559147 77574855950125447523338721)
      ·
        refine ⟨58181141962594085642504041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77574855950125447523338721 58181141962594085642504041)
        ·
          refine ⟨43635856471945564231878031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58181141962594085642504041 43635856471945564231878031)
          ·
            refine ⟨65453784707918346347817047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43635856471945564231878031 65453784707918346347817047)
            ·
              refine ⟨98180677061877519521725571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65453784707918346347817047 98180677061877519521725571)
              ·
                refine ⟨147271015592816279282588357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98180677061877519521725571 147271015592816279282588357)
                ·
                  refine ⟨27613315423653052365485317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147271015592816279282588357 27613315423653052365485317)
                  ·
                    refine ⟨5177496641934947318528497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27613315423653052365485317 5177496641934947318528497)
                    ·
                      refine ⟨3883122481451210488896373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177496641934947318528497 3883122481451210488896373)
                      ·
                        rfl

theorem cell23_7562354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_7562354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562354 prefixEnd_7562354 := by exact prefixLift 7562354
  have htrace : WordTrace (prefixWord ++ tailWord_7562354) baseStart_7562354 baseEnd_7562354 := by
    simpa [prefixWord, tailWord_7562354, baseEnd_7562354] using wordTrace_append hprefix tailTrace_7562354
  have hstable : (prefixWord ++ tailWord_7562354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562354).length < 2 ^ (prefixWord ++ tailWord_7562354).sum := by decide
  have hdescent : baseEnd_7562354 < baseStart_7562354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562364 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_7562364 : Nat := 118140960795 + 7562364 * 2 ^ 59
def prefixEnd_7562364 : Nat := 4983230072969 + 3 ^ 40 * 7562364 * 2
def baseEnd_7562364 : Nat := 1294375872085918483257109

theorem tailTrace_7562364 : CollatzResearch.WordTrace tailWord_7562364 prefixEnd_7562364 1294375872085918483257109 := by
  unfold tailWord_7562364
  simp only [CollatzResearch.WordTrace]
  refine ⟨137911037387427125895423073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183881383183236167860564097 137911037387427125895423073)
  ·
    refine ⟨103433278040570344421567305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137911037387427125895423073 103433278040570344421567305)
    ·
      refine ⟨77574958530427758316175479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103433278040570344421567305 77574958530427758316175479)
      ·
        refine ⟨116362437795641637474263219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77574958530427758316175479 116362437795641637474263219)
        ·
          refine ⟨174543656693462456211394829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116362437795641637474263219 174543656693462456211394829)
          ·
            refine ⟨65453871260048421079273061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174543656693462456211394829 65453871260048421079273061)
            ·
              refine ⟨12272600861259078952363699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65453871260048421079273061 12272600861259078952363699)
              ·
                refine ⟨18408901291888618428545549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12272600861259078952363699 18408901291888618428545549)
                ·
                  refine ⟨6903337984458231910704581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18408901291888618428545549 6903337984458231910704581)
                  ·
                    refine ⟨1294375872085918483257109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6903337984458231910704581 1294375872085918483257109)
                    ·
                      rfl

theorem cell23_7562364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_7562364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562364 prefixEnd_7562364 := by exact prefixLift 7562364
  have htrace : WordTrace (prefixWord ++ tailWord_7562364) baseStart_7562364 baseEnd_7562364 := by
    simpa [prefixWord, tailWord_7562364, baseEnd_7562364] using wordTrace_append hprefix tailTrace_7562364
  have hstable : (prefixWord ++ tailWord_7562364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562364).length < 2 ^ (prefixWord ++ tailWord_7562364).sum := by decide
  have hdescent : baseEnd_7562364 < baseStart_7562364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562437 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_7562437 : Nat := 118140960795 + 7562437 * 2 ^ 59
def prefixEnd_7562437 : Nat := 4983230072969 + 3 ^ 40 * 7562437 * 2
def baseEnd_7562437 : Nat := 1294388366781844554719497

theorem tailTrace_7562437 : CollatzResearch.WordTrace tailWord_7562437 prefixEnd_7562437 1294388366781844554719497 := by
  unfold tailWord_7562437
  simp only [CollatzResearch.WordTrace]
  refine ⟨275824737303589785258253565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183883158202393190172169043 275824737303589785258253565)
  ·
    refine ⟨103434276488846169471845087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275824737303589785258253565 103434276488846169471845087)
    ·
      refine ⟨155151414733269254207767631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103434276488846169471845087 155151414733269254207767631)
      ·
        refine ⟨232727122099903881311651447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155151414733269254207767631 232727122099903881311651447)
        ·
          refine ⟨349090683149855821967477171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232727122099903881311651447 349090683149855821967477171)
          ·
            refine ⟨523636024724783732951215757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349090683149855821967477171 523636024724783732951215757)
            ·
              refine ⟨196363509271793899856705909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523636024724783732951215757 196363509271793899856705909)
              ·
                refine ⟨18409078994230678111566179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196363509271793899856705909 18409078994230678111566179)
                ·
                  refine ⟨27613618491346017167349269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18409078994230678111566179 27613618491346017167349269)
                  ·
                    refine ⟨1294388366781844554719497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27613618491346017167349269 1294388366781844554719497)
                    ·
                      rfl

theorem cell23_7562437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_7562437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562437 prefixEnd_7562437 := by exact prefixLift 7562437
  have htrace : WordTrace (prefixWord ++ tailWord_7562437) baseStart_7562437 baseEnd_7562437 := by
    simpa [prefixWord, tailWord_7562437, baseEnd_7562437] using wordTrace_append hprefix tailTrace_7562437
  have hstable : (prefixWord ++ tailWord_7562437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562437).length < 2 ^ (prefixWord ++ tailWord_7562437).sum := by decide
  have hdescent : baseEnd_7562437 < baseStart_7562437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562464 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 5]
def baseStart_7562464 : Nat := 118140960795 + 7562464 * 2 ^ 59
def prefixEnd_7562464 : Nat := 4983230072969 + 3 ^ 40 * 7562464 * 2
def baseEnd_7562464 : Nat := 3883178964323205058520867

theorem tailTrace_7562464 : CollatzResearch.WordTrace tailWord_7562464 prefixEnd_7562464 3883178964323205058520867 := by
  unfold tailWord_7562464
  simp only [CollatzResearch.WordTrace]
  refine ⟨137912861037245984434743223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183883814716327979246324297 137912861037245984434743223)
  ·
    refine ⟨206869291555868976652114835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137912861037245984434743223 206869291555868976652114835)
    ·
      refine ⟨310303937333803464978172253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206869291555868976652114835 310303937333803464978172253)
      ·
        refine ⟨116363976500176299366814595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310303937333803464978172253 116363976500176299366814595)
        ·
          refine ⟨174545964750264449050221893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116363976500176299366814595 174545964750264449050221893)
          ·
            refine ⟨32727368390674584196916605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174545964750264449050221893 32727368390674584196916605)
            ·
              refine ⟨12272763146502969073843727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32727368390674584196916605 12272763146502969073843727)
              ·
                refine ⟨18409144719754453610765591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12272763146502969073843727 18409144719754453610765591)
                ·
                  refine ⟨27613717079631680416148387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18409144719754453610765591 27613717079631680416148387)
                  ·
                    refine ⟨41420575619447520624222581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27613717079631680416148387 41420575619447520624222581)
                    ·
                      refine ⟨3883178964323205058520867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41420575619447520624222581 3883178964323205058520867)
                      ·
                        rfl

theorem cell23_7562464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_7562464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562464 prefixEnd_7562464 := by exact prefixLift 7562464
  have htrace : WordTrace (prefixWord ++ tailWord_7562464) baseStart_7562464 baseEnd_7562464 := by
    simpa [prefixWord, tailWord_7562464, baseEnd_7562464] using wordTrace_append hprefix tailTrace_7562464
  have hstable : (prefixWord ++ tailWord_7562464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562464).length < 2 ^ (prefixWord ++ tailWord_7562464).sum := by decide
  have hdescent : baseEnd_7562464 < baseStart_7562464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562528 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 4, 1, 3]
def baseStart_7562528 : Nat := 118140960795 + 7562528 * 2 ^ 59
def prefixEnd_7562528 : Nat := 4983230072969 + 3 ^ 40 * 7562528 * 2
def baseEnd_7562528 : Nat := 3883211827085092808120573

theorem tailTrace_7562528 : CollatzResearch.WordTrace tailWord_7562528 prefixEnd_7562528 3883211827085092808120573 := by
  unfold tailWord_7562528
  simp only [CollatzResearch.WordTrace]
  refine ⟨137914028173130053899908119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183885370897506738533210825 137914028173130053899908119)
  ·
    refine ⟨206871042259695080849862179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137914028173130053899908119 206871042259695080849862179)
    ·
      refine ⟨310306563389542621274793269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206871042259695080849862179 310306563389542621274793269)
      ·
        refine ⟨29091240317769620744511869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310306563389542621274793269 29091240317769620744511869)
        ·
          refine ⟨10909215119163607779191951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29091240317769620744511869 10909215119163607779191951)
          ·
            refine ⟨16363822678745411668787927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10909215119163607779191951 16363822678745411668787927)
            ·
              refine ⟨24545734018118117503181891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16363822678745411668787927 24545734018118117503181891)
              ·
                refine ⟨36818601027177176254772837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24545734018118117503181891 36818601027177176254772837)
                ·
                  refine ⟨6903487692595720547769907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36818601027177176254772837 6903487692595720547769907)
                  ·
                    refine ⟨10355231538893580821654861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6903487692595720547769907 10355231538893580821654861)
                    ·
                      refine ⟨3883211827085092808120573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10355231538893580821654861 3883211827085092808120573)
                      ·
                        rfl

theorem cell23_7562528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_7562528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562528 prefixEnd_7562528 := by exact prefixLift 7562528
  have htrace : WordTrace (prefixWord ++ tailWord_7562528) baseStart_7562528 baseEnd_7562528 := by
    simpa [prefixWord, tailWord_7562528, baseEnd_7562528] using wordTrace_append hprefix tailTrace_7562528
  have hstable : (prefixWord ++ tailWord_7562528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562528).length < 2 ^ (prefixWord ++ tailWord_7562528).sum := by decide
  have hdescent : baseEnd_7562528 < baseStart_7562528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562545 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 2, 1, 3]
def baseStart_7562545 : Nat := 118140960795 + 7562545 * 2 ^ 59
def prefixEnd_7562545 : Nat := 4983230072969 + 3 ^ 40 * 7562545 * 2
def baseEnd_7562545 : Nat := 3883220556256219241607995

theorem tailTrace_7562545 : CollatzResearch.WordTrace tailWord_7562545 prefixEnd_7562545 3883220556256219241607995 := by
  unfold tailWord_7562545
  simp only [CollatzResearch.WordTrace]
  refine ⟨275828676387198519703185089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183885784258132346468790059 275828676387198519703185089)
  ·
    refine ⟨206871507290398889777388817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275828676387198519703185089 206871507290398889777388817)
    ·
      refine ⟨155153630467799167333041613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206871507290398889777388817 155153630467799167333041613)
      ·
        refine ⟨58182611425424687749890605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155153630467799167333041613 58182611425424687749890605)
        ·
          refine ⟨21818479284534257906208977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58182611425424687749890605 21818479284534257906208977)
          ·
            refine ⟨16363859463400693429656733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21818479284534257906208977 16363859463400693429656733)
            ·
              refine ⟨6136447298775260036121275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16363859463400693429656733 6136447298775260036121275)
              ·
                refine ⟨9204670948162890054181913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136447298775260036121275 9204670948162890054181913)
                ·
                  refine ⟨6903503211122167540636435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9204670948162890054181913 6903503211122167540636435)
                  ·
                    refine ⟨10355254816683251310954653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6903503211122167540636435 10355254816683251310954653)
                    ·
                      refine ⟨3883220556256219241607995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10355254816683251310954653 3883220556256219241607995)
                      ·
                        rfl

theorem cell23_7562545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_7562545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562545 prefixEnd_7562545 := by exact prefixLift 7562545
  have htrace : WordTrace (prefixWord ++ tailWord_7562545) baseStart_7562545 baseEnd_7562545 := by
    simpa [prefixWord, tailWord_7562545, baseEnd_7562545] using wordTrace_append hprefix tailTrace_7562545
  have hstable : (prefixWord ++ tailWord_7562545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562545).length < 2 ^ (prefixWord ++ tailWord_7562545).sum := by decide
  have hdescent : baseEnd_7562545 < baseStart_7562545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562554 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_7562554 : Nat := 118140960795 + 7562554 * 2 ^ 59
def prefixEnd_7562554 : Nat := 4983230072969 + 3 ^ 40 * 7562554 * 2
def baseEnd_7562554 : Nat := 3883225177582109706395453

theorem tailTrace_7562554 : CollatzResearch.WordTrace tailWord_7562554 prefixEnd_7562554 3883225177582109706395453 := by
  unfold tailWord_7562554
  simp only [CollatzResearch.WordTrace]
  refine ⟨68957251161041478560065679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183886003096110609493508477 68957251161041478560065679)
  ·
    refine ⟨103435876741562217840098519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68957251161041478560065679 103435876741562217840098519)
    ·
      refine ⟨155153815112343326760147779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103435876741562217840098519 155153815112343326760147779)
      ·
        refine ⟨232730722668514990140221669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155153815112343326760147779 232730722668514990140221669)
        ·
          refine ⟨43637010500346560651291563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232730722668514990140221669 43637010500346560651291563)
          ·
            refine ⟨65455515750519840976937345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43637010500346560651291563 65455515750519840976937345)
            ·
              refine ⟨49091636812889880732703009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65455515750519840976937345 49091636812889880732703009)
              ·
                refine ⟨36818727609667410549527257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49091636812889880732703009 36818727609667410549527257)
                ·
                  refine ⟨27614045707250557912145443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36818727609667410549527257 27614045707250557912145443)
                  ·
                    refine ⟨41421068560875836868218165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27614045707250557912145443 41421068560875836868218165)
                    ·
                      refine ⟨3883225177582109706395453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41421068560875836868218165 3883225177582109706395453)
                      ·
                        rfl

theorem cell23_7562554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_7562554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562554 prefixEnd_7562554 := by exact prefixLift 7562554
  have htrace : WordTrace (prefixWord ++ tailWord_7562554) baseStart_7562554 baseEnd_7562554 := by
    simpa [prefixWord, tailWord_7562554, baseEnd_7562554] using wordTrace_append hprefix tailTrace_7562554
  have hstable : (prefixWord ++ tailWord_7562554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562554).length < 2 ^ (prefixWord ++ tailWord_7562554).sum := by decide
  have hdescent : baseEnd_7562554 < baseStart_7562554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562602 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_7562602 : Nat := 118140960795 + 7562602 * 2 ^ 59
def prefixEnd_7562602 : Nat := 4983230072969 + 3 ^ 40 * 7562602 * 2
def baseEnd_7562602 : Nat := 3883249824653525518595233

theorem tailTrace_7562602 : CollatzResearch.WordTrace tailWord_7562602 prefixEnd_7562602 3883249824653525518595233 := by
  unfold tailWord_7562602
  simp only [CollatzResearch.WordTrace]
  refine ⟨68957688836998004609502515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183887170231994678958673373 68957688836998004609502515)
  ·
    refine ⟨103436533255497006914253773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68957688836998004609502515 103436533255497006914253773)
    ·
      refine ⟨38788699970811377592845165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103436533255497006914253773 38788699970811377592845165)
      ·
        refine ⟨14545762489054266597316937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38788699970811377592845165 14545762489054266597316937)
        ·
          refine ⟨10909321866790699947987703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14545762489054266597316937 10909321866790699947987703)
          ·
            refine ⟨16363982800186049921981555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10909321866790699947987703 16363982800186049921981555)
            ·
              refine ⟨24545974200279074882972333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16363982800186049921981555 24545974200279074882972333)
              ·
                refine ⟨9204740325104653081114625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24545974200279074882972333 9204740325104653081114625)
                ·
                  refine ⟨6903555243828489810835969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9204740325104653081114625 6903555243828489810835969)
                  ·
                    refine ⟨5177666432871367358126977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6903555243828489810835969 5177666432871367358126977)
                    ·
                      refine ⟨3883249824653525518595233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177666432871367358126977 3883249824653525518595233)
                      ·
                        rfl

theorem cell23_7562602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_7562602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562602 prefixEnd_7562602 := by exact prefixLift 7562602
  have htrace : WordTrace (prefixWord ++ tailWord_7562602) baseStart_7562602 baseEnd_7562602 := by
    simpa [prefixWord, tailWord_7562602, baseEnd_7562602] using wordTrace_append hprefix tailTrace_7562602
  have hstable : (prefixWord ++ tailWord_7562602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562602).length < 2 ^ (prefixWord ++ tailWord_7562602).sum := by decide
  have hdescent : baseEnd_7562602 < baseStart_7562602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562621 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_7562621 : Nat := 118140960795 + 7562621 * 2 ^ 59
def prefixEnd_7562621 : Nat := 4983230072969 + 3 ^ 40 * 7562621 * 2
def baseEnd_7562621 : Nat := 1294419860261986981419215

theorem tailTrace_7562621 : CollatzResearch.WordTrace tailWord_7562621 prefixEnd_7562621 1294419860261986981419215 := by
  unfold tailWord_7562621
  simp only [CollatzResearch.WordTrace]
  refine ⟨275831448334923184682951717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183887632223282123121967811 275831448334923184682951717)
  ·
    refine ⟨51718396562798097128053447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275831448334923184682951717 51718396562798097128053447)
    ·
      refine ⟨77577594844197145692080171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51718396562798097128053447 77577594844197145692080171)
      ·
        refine ⟨116366392266295718538120257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77577594844197145692080171 116366392266295718538120257)
        ·
          refine ⟨87274794199721788903590193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116366392266295718538120257 87274794199721788903590193)
          ·
            refine ⟨65456095649791341677692645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87274794199721788903590193 65456095649791341677692645)
            ·
              refine ⟨12273017934335876564567371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65456095649791341677692645 12273017934335876564567371)
              ·
                refine ⟨18409526901503814846851057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12273017934335876564567371 18409526901503814846851057)
                ·
                  refine ⟨13807145176127861135138293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18409526901503814846851057 13807145176127861135138293)
                  ·
                    refine ⟨1294419860261986981419215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13807145176127861135138293 1294419860261986981419215)
                    ·
                      rfl

theorem cell23_7562621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_7562621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562621 prefixEnd_7562621 := by exact prefixLift 7562621
  have htrace : WordTrace (prefixWord ++ tailWord_7562621) baseStart_7562621 baseEnd_7562621 := by
    simpa [prefixWord, tailWord_7562621, baseEnd_7562621] using wordTrace_append hprefix tailTrace_7562621
  have hstable : (prefixWord ++ tailWord_7562621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562621).length < 2 ^ (prefixWord ++ tailWord_7562621).sum := by decide
  have hdescent : baseEnd_7562621 < baseStart_7562621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562624 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_7562624 : Nat := 118140960795 + 7562624 * 2 ^ 59
def prefixEnd_7562624 : Nat := 4983230072969 + 3 ^ 40 * 7562624 * 2
def baseEnd_7562624 : Nat := 3883261121227924432520131

theorem tailTrace_7562624 : CollatzResearch.WordTrace tailWord_7562624 prefixEnd_7562624 3883261121227924432520131 := by
  unfold tailWord_7562624
  simp only [CollatzResearch.WordTrace]
  refine ⟨137915778876956158097655463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183887705169274877463540617 137915778876956158097655463)
  ·
    refine ⟨206873668315434237146483195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137915778876956158097655463 206873668315434237146483195)
    ·
      refine ⟨310310502473151355719724793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206873668315434237146483195 310310502473151355719724793)
      ·
        refine ⟨232732876854863516789793595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310310502473151355719724793 232732876854863516789793595)
        ·
          refine ⟨349099315282295275184690393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232732876854863516789793595 349099315282295275184690393)
          ·
            refine ⟨261824486461721456388517795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349099315282295275184690393 261824486461721456388517795)
            ·
              refine ⟨392736729692582184582776693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261824486461721456388517795 392736729692582184582776693)
              ·
                refine ⟨36819068408679579804635315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392736729692582184582776693 36819068408679579804635315)
                ·
                  refine ⟨55228602613019369706952973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36819068408679579804635315 55228602613019369706952973)
                  ·
                    refine ⟨20710725979882263640107365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55228602613019369706952973 20710725979882263640107365)
                    ·
                      refine ⟨3883261121227924432520131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20710725979882263640107365 3883261121227924432520131)
                      ·
                        rfl

theorem cell23_7562624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_7562624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562624 prefixEnd_7562624 := by exact prefixLift 7562624
  have htrace : WordTrace (prefixWord ++ tailWord_7562624) baseStart_7562624 baseEnd_7562624 := by
    simpa [prefixWord, tailWord_7562624, baseEnd_7562624] using wordTrace_append hprefix tailTrace_7562624
  have hstable : (prefixWord ++ tailWord_7562624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562624).length < 2 ^ (prefixWord ++ tailWord_7562624).sum := by decide
  have hdescent : baseEnd_7562624 < baseStart_7562624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562641 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 4, 4, 2]
def baseStart_7562641 : Nat := 118140960795 + 7562641 * 2 ^ 59
def prefixEnd_7562641 : Nat := 4983230072969 + 3 ^ 40 * 7562641 * 2
def baseEnd_7562641 : Nat := 3883269850399050866007553

theorem tailTrace_7562641 : CollatzResearch.WordTrace tailWord_7562641 prefixEnd_7562641 3883269850399050866007553 := by
  unfold tailWord_7562641
  simp only [CollatzResearch.WordTrace]
  refine ⟨275832177794850728098679777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183888118529900485399119851 275832177794850728098679777)
  ·
    refine ⟨206874133346138046074009833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275832177794850728098679777 206874133346138046074009833)
    ·
      refine ⟨155155600009603534555507375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206874133346138046074009833 155155600009603534555507375)
      ·
        refine ⟨232733400014405301833261063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155155600009603534555507375 232733400014405301833261063)
        ·
          refine ⟨349100100021607952749891595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232733400014405301833261063 349100100021607952749891595)
          ·
            refine ⟨523650150032411929124837393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349100100021607952749891595 523650150032411929124837393)
            ·
              refine ⟨392737612524308946843628045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523650150032411929124837393 392737612524308946843628045)
              ·
                refine ⟨147276604696615855066360517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392737612524308946843628045 147276604696615855066360517)
                ·
                  refine ⟨27614363380615472824942597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147276604696615855066360517 27614363380615472824942597)
                  ·
                    refine ⟨5177693133865401154676737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27614363380615472824942597 5177693133865401154676737)
                    ·
                      refine ⟨3883269850399050866007553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177693133865401154676737 3883269850399050866007553)
                      ·
                        rfl

theorem cell23_7562641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_7562641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562641 prefixEnd_7562641 := by exact prefixLift 7562641
  have htrace : WordTrace (prefixWord ++ tailWord_7562641) baseStart_7562641 baseEnd_7562641 := by
    simpa [prefixWord, tailWord_7562641, baseEnd_7562641] using wordTrace_append hprefix tailTrace_7562641
  have hstable : (prefixWord ++ tailWord_7562641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562641).length < 2 ^ (prefixWord ++ tailWord_7562641).sum := by decide
  have hdescent : baseEnd_7562641 < baseStart_7562641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562658 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_7562658 : Nat := 118140960795 + 7562658 * 2 ^ 59
def prefixEnd_7562658 : Nat := 4983230072969 + 3 ^ 40 * 7562658 * 2
def baseEnd_7562658 : Nat := 3883278579570177299494975

theorem tailTrace_7562658 : CollatzResearch.WordTrace tailWord_7562658 prefixEnd_7562658 3883278579570177299494975 := by
  unfold tailWord_7562658
  simp only [CollatzResearch.WordTrace]
  refine ⟨68958199458947285000512157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183888531890526093334699085 68958199458947285000512157)
  ·
    refine ⟨25859324797105231875192059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68958199458947285000512157 25859324797105231875192059)
    ·
      refine ⟨38788987195657847812788089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25859324797105231875192059 38788987195657847812788089)
      ·
        refine ⟨29091740396743385859591067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38788987195657847812788089 29091740396743385859591067)
        ·
          refine ⟨43637610595115078789386601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29091740396743385859591067 43637610595115078789386601)
          ·
            refine ⟨32728207946336309092039951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43637610595115078789386601 32728207946336309092039951)
            ·
              refine ⟨49092311919504463638059927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32728207946336309092039951 49092311919504463638059927)
              ·
                refine ⟨73638467879256695457089891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49092311919504463638059927 73638467879256695457089891)
                ·
                  refine ⟨110457701818885043185634837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73638467879256695457089891 110457701818885043185634837)
                  ·
                    refine ⟨5177704772760236399326633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110457701818885043185634837 5177704772760236399326633)
                    ·
                      refine ⟨3883278579570177299494975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177704772760236399326633 3883278579570177299494975)
                      ·
                        rfl

theorem cell23_7562658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_7562658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562658 prefixEnd_7562658 := by exact prefixLift 7562658
  have htrace : WordTrace (prefixWord ++ tailWord_7562658) baseStart_7562658 baseEnd_7562658 := by
    simpa [prefixWord, tailWord_7562658, baseEnd_7562658] using wordTrace_append hprefix tailTrace_7562658
  have hstable : (prefixWord ++ tailWord_7562658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562658).length < 2 ^ (prefixWord ++ tailWord_7562658).sum := by decide
  have hdescent : baseEnd_7562658 < baseStart_7562658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562685 : List Nat := [1, 4, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_7562685 : Nat := 118140960795 + 7562685 * 2 ^ 59
def prefixEnd_7562685 : Nat := 4983230072969 + 3 ^ 40 * 7562685 * 2
def baseEnd_7562685 : Nat := 1294430814515949564619117

theorem tailTrace_7562685 : CollatzResearch.WordTrace tailWord_7562685 prefixEnd_7562685 1294430814515949564619117 := by
  unfold tailWord_7562685
  simp only [CollatzResearch.WordTrace]
  refine ⟨275833782606691323613281509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183889188404460882408854339 275833782606691323613281509)
  ·
    refine ⟨51718834238754623177490283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275833782606691323613281509 51718834238754623177490283)
    ·
      refine ⟨77578251358131934766235425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51718834238754623177490283 77578251358131934766235425)
      ·
        refine ⟨58183688518598951074676569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77578251358131934766235425 58183688518598951074676569)
        ·
          refine ⟨43637766388949213306007427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58183688518598951074676569 43637766388949213306007427)
          ·
            refine ⟨65456649583423819959011141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43637766388949213306007427 65456649583423819959011141)
            ·
              refine ⟨12273121796891966242314589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65456649583423819959011141 12273121796891966242314589)
              ·
                refine ⟨4602420673834487340867971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12273121796891966242314589 4602420673834487340867971)
                ·
                  refine ⟨6903631010751731011301957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602420673834487340867971 6903631010751731011301957)
                  ·
                    refine ⟨1294430814515949564619117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6903631010751731011301957 1294430814515949564619117)
                    ·
                      rfl

theorem cell23_7562685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_7562685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562685 prefixEnd_7562685 := by exact prefixLift 7562685
  have htrace : WordTrace (prefixWord ++ tailWord_7562685) baseStart_7562685 baseEnd_7562685 := by
    simpa [prefixWord, tailWord_7562685, baseEnd_7562685] using wordTrace_append hprefix tailTrace_7562685
  have hstable : (prefixWord ++ tailWord_7562685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562685).length < 2 ^ (prefixWord ++ tailWord_7562685).sum := by decide
  have hdescent : baseEnd_7562685 < baseStart_7562685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562698 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 6]
def baseStart_7562698 : Nat := 118140960795 + 7562698 * 2 ^ 59
def prefixEnd_7562698 : Nat := 4983230072969 + 3 ^ 40 * 7562698 * 2
def baseEnd_7562698 : Nat := 431477679866261904777199

theorem tailTrace_7562698 : CollatzResearch.WordTrace tailWord_7562698 prefixEnd_7562698 431477679866261904777199 := by
  unfold tailWord_7562698
  simp only [CollatzResearch.WordTrace]
  refine ⟨68958564188911056708376187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183889504503762817889003165 68958564188911056708376187)
  ·
    refine ⟨103437846283366585062564281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68958564188911056708376187 103437846283366585062564281)
    ·
      refine ⟨77578384712524938796923211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103437846283366585062564281 77578384712524938796923211)
      ·
        refine ⟨116367577068787408195384817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77578384712524938796923211 116367577068787408195384817)
        ·
          refine ⟨87275682801590556146538613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116367577068787408195384817 87275682801590556146538613)
          ·
            refine ⟨8182095262649114638737995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87275682801590556146538613 8182095262649114638737995)
            ·
              refine ⟨12273142893973671958106993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8182095262649114638737995 12273142893973671958106993)
              ·
                refine ⟨9204857170480253968580245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12273142893973671958106993 9204857170480253968580245)
                ·
                  refine ⟨431477679866261904777199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9204857170480253968580245 431477679866261904777199)
                  ·
                    rfl

theorem cell23_7562698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_7562698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562698 prefixEnd_7562698 := by exact prefixLift 7562698
  have htrace : WordTrace (prefixWord ++ tailWord_7562698) baseStart_7562698 baseEnd_7562698 := by
    simpa [prefixWord, tailWord_7562698, baseEnd_7562698] using wordTrace_append hprefix tailTrace_7562698
  have hstable : (prefixWord ++ tailWord_7562698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562698).length < 2 ^ (prefixWord ++ tailWord_7562698).sum := by decide
  have hdescent : baseEnd_7562698 < baseStart_7562698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562704 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_7562704 : Nat := 118140960795 + 7562704 * 2 ^ 59
def prefixEnd_7562704 : Nat := 4983230072969 + 3 ^ 40 * 7562704 * 2
def baseEnd_7562704 : Nat := 3883302199680284119519763

theorem tailTrace_7562704 : CollatzResearch.WordTrace tailWord_7562704 prefixEnd_7562704 3883302199680284119519763 := by
  unfold tailWord_7562704
  simp only [CollatzResearch.WordTrace]
  refine ⟨137917237796811244929111583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183889650395748326572148777 137917237796811244929111583)
  ·
    refine ⟨206875856695216867393667375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137917237796811244929111583 206875856695216867393667375)
    ·
      refine ⟨310313785042825301090501063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206875856695216867393667375 310313785042825301090501063)
      ·
        refine ⟨465470677564237951635751595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310313785042825301090501063 465470677564237951635751595)
        ·
          refine ⟨698206016346356927453627393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465470677564237951635751595 698206016346356927453627393)
          ·
            refine ⟨523654512259767695590220545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698206016346356927453627393 523654512259767695590220545)
            ·
              refine ⟨392740884194825771692665409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523654512259767695590220545 392740884194825771692665409)
              ·
                refine ⟨294555663146119328769499057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392740884194825771692665409 294555663146119328769499057)
                ·
                  refine ⟨220916747359589496577124293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294555663146119328769499057 220916747359589496577124293)
                  ·
                    refine ⟨41421890129923030608210805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220916747359589496577124293 41421890129923030608210805)
                    ·
                      refine ⟨3883302199680284119519763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41421890129923030608210805 3883302199680284119519763)
                      ·
                        rfl

theorem cell23_7562704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_7562704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562704 prefixEnd_7562704 := by exact prefixLift 7562704
  have htrace : WordTrace (prefixWord ++ tailWord_7562704) baseStart_7562704 baseEnd_7562704 := by
    simpa [prefixWord, tailWord_7562704, baseEnd_7562704] using wordTrace_append hprefix tailTrace_7562704
  have hstable : (prefixWord ++ tailWord_7562704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562704).length < 2 ^ (prefixWord ++ tailWord_7562704).sum := by decide
  have hdescent : baseEnd_7562704 < baseStart_7562704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562725 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7562725 : Nat := 118140960795 + 7562725 * 2 ^ 59
def prefixEnd_7562725 : Nat := 4983230072969 + 3 ^ 40 * 7562725 * 2
def baseEnd_7562725 : Nat := 3883312982774028537357167

theorem tailTrace_7562725 : CollatzResearch.WordTrace tailWord_7562725 prefixEnd_7562725 3883312982774028537357167 := by
  unfold tailWord_7562725
  simp only [CollatzResearch.WordTrace]
  refine ⟨275835241526546410444737629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183890161017697606963158419 275835241526546410444737629)
  ·
    refine ⟨103438215572454903916776611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275835241526546410444737629 103438215572454903916776611)
    ·
      refine ⟨155157323358682355875164917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103438215572454903916776611 155157323358682355875164917)
      ·
        refine ⟨14545999064876470863296711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155157323358682355875164917 14545999064876470863296711)
        ·
          refine ⟨21818998597314706294945067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14545999064876470863296711 21818998597314706294945067)
          ·
            refine ⟨32728497895972059442417601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21818998597314706294945067 32728497895972059442417601)
            ·
              refine ⟨24546373421979044581813201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32728497895972059442417601 24546373421979044581813201)
              ·
                refine ⟨18409780066484283436359901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24546373421979044581813201 18409780066484283436359901)
                ·
                  refine ⟨6903667524931606288634963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18409780066484283436359901 6903667524931606288634963)
                  ·
                    refine ⟨10355501287397409432952445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6903667524931606288634963 10355501287397409432952445)
                    ·
                      refine ⟨3883312982774028537357167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10355501287397409432952445 3883312982774028537357167)
                      ·
                        rfl

theorem cell23_7562725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7562725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562725 prefixEnd_7562725 := by exact prefixLift 7562725
  have htrace : WordTrace (prefixWord ++ tailWord_7562725) baseStart_7562725 baseEnd_7562725 := by
    simpa [prefixWord, tailWord_7562725, baseEnd_7562725] using wordTrace_append hprefix tailTrace_7562725
  have hstable : (prefixWord ++ tailWord_7562725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562725).length < 2 ^ (prefixWord ++ tailWord_7562725).sum := by decide
  have hdescent : baseEnd_7562725 < baseStart_7562725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562728 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 1, 5]
def baseStart_7562728 : Nat := 118140960795 + 7562728 * 2 ^ 59
def prefixEnd_7562728 : Nat := 4983230072969 + 3 ^ 40 * 7562728 * 2
def baseEnd_7562728 : Nat := 1294438174405330675206551

theorem tailTrace_7562728 : CollatzResearch.WordTrace tailWord_7562728 prefixEnd_7562728 1294438174405330675206551 := by
  unfold tailWord_7562728
  simp only [CollatzResearch.WordTrace]
  refine ⟨137917675472767770978548419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183890233963690361304731225 137917675472767770978548419)
  ·
    refine ⟨206876513209151656467822629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137917675472767770978548419 206876513209151656467822629)
    ·
      refine ⟨38789346226715935587716743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206876513209151656467822629 38789346226715935587716743)
      ·
        refine ⟨58184019340073903381575115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38789346226715935587716743 58184019340073903381575115)
        ·
          refine ⟨87276029010110855072362673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58184019340073903381575115 87276029010110855072362673)
          ·
            refine ⟨65457021757583141304272005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87276029010110855072362673 65457021757583141304272005)
            ·
              refine ⟨12273191579546838994551001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65457021757583141304272005 12273191579546838994551001)
              ·
                refine ⟨9204893684660129245913251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12273191579546838994551001 9204893684660129245913251)
                ·
                  refine ⟨13807340526990193868869877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9204893684660129245913251 13807340526990193868869877)
                  ·
                    refine ⟨1294438174405330675206551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13807340526990193868869877 1294438174405330675206551)
                    ·
                      rfl

theorem cell23_7562728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_7562728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562728 prefixEnd_7562728 := by exact prefixLift 7562728
  have htrace : WordTrace (prefixWord ++ tailWord_7562728) baseStart_7562728 baseEnd_7562728 := by
    simpa [prefixWord, tailWord_7562728, baseEnd_7562728] using wordTrace_append hprefix tailTrace_7562728
  have hstable : (prefixWord ++ tailWord_7562728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562728).length < 2 ^ (prefixWord ++ tailWord_7562728).sum := by decide
  have hdescent : baseEnd_7562728 < baseStart_7562728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562748 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_7562748 : Nat := 118140960795 + 7562748 * 2 ^ 59
def prefixEnd_7562748 : Nat := 4983230072969 + 3 ^ 40 * 7562748 * 2
def baseEnd_7562748 : Nat := 3883324792829081947369561

theorem tailTrace_7562748 : CollatzResearch.WordTrace tailWord_7562748 prefixEnd_7562748 3883324792829081947369561 := by
  unfold tailWord_7562748
  simp only [CollatzResearch.WordTrace]
  refine ⟨137918040202731542686412449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183890720270308723581883265 137918040202731542686412449)
  ·
    refine ⟨103438530152048657014809337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137918040202731542686412449 103438530152048657014809337)
    ·
      refine ⟨77578897614036492761107003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103438530152048657014809337 77578897614036492761107003)
      ·
        refine ⟨116368346421054739141660505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77578897614036492761107003 116368346421054739141660505)
        ·
          refine ⟨87276259815791054356245379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116368346421054739141660505 87276259815791054356245379)
          ·
            refine ⟨130914389723686581534368069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87276259815791054356245379 130914389723686581534368069)
            ·
              refine ⟨24546448073191234037694013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130914389723686581534368069 24546448073191234037694013)
              ·
                refine ⟨9204918027446712764135255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24546448073191234037694013 9204918027446712764135255)
                ·
                  refine ⟨13807377041170069146202883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9204918027446712764135255 13807377041170069146202883)
                  ·
                    refine ⟨20711065561755103719304325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13807377041170069146202883 20711065561755103719304325)
                    ·
                      refine ⟨3883324792829081947369561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20711065561755103719304325 3883324792829081947369561)
                      ·
                        rfl

theorem cell23_7562748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_7562748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562748 prefixEnd_7562748 := by exact prefixLift 7562748
  have htrace : WordTrace (prefixWord ++ tailWord_7562748) baseStart_7562748 baseEnd_7562748 := by
    simpa [prefixWord, tailWord_7562748, baseEnd_7562748] using wordTrace_append hprefix tailTrace_7562748
  have hstable : (prefixWord ++ tailWord_7562748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562748).length < 2 ^ (prefixWord ++ tailWord_7562748).sum := by decide
  have hdescent : baseEnd_7562748 < baseStart_7562748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562759 : List Nat := [1, 1, 4, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_7562759 : Nat := 118140960795 + 7562759 * 2 ^ 59
def prefixEnd_7562759 : Nat := 4983230072969 + 3 ^ 40 * 7562759 * 2
def baseEnd_7562759 : Nat := 3883330441116281404332011

theorem tailTrace_7562759 : CollatzResearch.WordTrace tailWord_7562759 prefixEnd_7562759 3883330441116281404332011 := by
  unfold tailWord_7562759
  simp only [CollatzResearch.WordTrace]
  refine ⟨275836481608423234251475331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183890987738948822834316887 275836481608423234251475331)
  ·
    refine ⟨413754722412634851377212997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275836481608423234251475331 413754722412634851377212997)
    ·
      refine ⟨77579010452369034633227437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413754722412634851377212997 77579010452369034633227437)
      ·
        refine ⟨29092128919638387987460289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77579010452369034633227437 29092128919638387987460289)
        ·
          refine ⟨21819096689728790990595217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29092128919638387987460289 21819096689728790990595217)
          ·
            refine ⟨16364322517296593242946413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21819096689728790990595217 16364322517296593242946413)
            ·
              refine ⟨6136620943986222466104905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16364322517296593242946413 6136620943986222466104905)
              ·
                refine ⟨4602465707989666849578679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6136620943986222466104905 4602465707989666849578679)
                ·
                  refine ⟨6903698561984500274368019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602465707989666849578679 6903698561984500274368019)
                  ·
                    refine ⟨10355547842976750411552029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6903698561984500274368019 10355547842976750411552029)
                    ·
                      refine ⟨3883330441116281404332011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10355547842976750411552029 3883330441116281404332011)
                      ·
                        rfl

theorem cell23_7562759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_7562759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562759 prefixEnd_7562759 := by exact prefixLift 7562759
  have htrace : WordTrace (prefixWord ++ tailWord_7562759) baseStart_7562759 baseEnd_7562759 := by
    simpa [prefixWord, tailWord_7562759, baseEnd_7562759] using wordTrace_append hprefix tailTrace_7562759
  have hstable : (prefixWord ++ tailWord_7562759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562759).length < 2 ^ (prefixWord ++ tailWord_7562759).sum := by decide
  have hdescent : baseEnd_7562759 < baseStart_7562759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562771 : List Nat := [1, 1, 1, 2, 1, 7, 2, 8]
def baseStart_7562771 : Nat := 118140960795 + 7562771 * 2 ^ 59
def prefixEnd_7562771 : Nat := 4983230072969 + 3 ^ 40 * 7562771 * 2
def baseEnd_7562771 : Nat := 143827281588301309532665

theorem tailTrace_7562771 : CollatzResearch.WordTrace tailWord_7562771 prefixEnd_7562771 143827281588301309532665 := by
  unfold tailWord_7562771
  simp only [CollatzResearch.WordTrace]
  refine ⟨275836919284379760300912167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183891279522919840200608111 275836919284379760300912167)
  ·
    refine ⟨413755378926569640451368251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275836919284379760300912167 413755378926569640451368251)
    ·
      refine ⟨620633068389854460677052377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413755378926569640451368251 620633068389854460677052377)
      ·
        refine ⟨465474801292390845507789283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620633068389854460677052377 465474801292390845507789283)
        ·
          refine ⟨698212201938586268261683925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465474801292390845507789283 698212201938586268261683925)
          ·
            refine ⟨16364348482935615662383217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 698212201938586268261683925 16364348482935615662383217)
            ·
              refine ⟨12273261362201711746787413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16364348482935615662383217 12273261362201711746787413)
              ·
                refine ⟨143827281588301309532665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12273261362201711746787413 143827281588301309532665)
                ·
                  rfl

theorem cell23_7562771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 8].length) (baseStart_7562771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562771 prefixEnd_7562771 := by exact prefixLift 7562771
  have htrace : WordTrace (prefixWord ++ tailWord_7562771) baseStart_7562771 baseEnd_7562771 := by
    simpa [prefixWord, tailWord_7562771, baseEnd_7562771] using wordTrace_append hprefix tailTrace_7562771
  have hstable : (prefixWord ++ tailWord_7562771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562771).length < 2 ^ (prefixWord ++ tailWord_7562771).sum := by decide
  have hdescent : baseEnd_7562771 < baseStart_7562771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562785 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_7562785 : Nat := 118140960795 + 7562785 * 2 ^ 59
def prefixEnd_7562785 : Nat := 4983230072969 + 3 ^ 40 * 7562785 * 2
def baseEnd_7562785 : Nat := 3883343791613298302606891

theorem tailTrace_7562785 : CollatzResearch.WordTrace tailWord_7562785 prefixEnd_7562785 3883343791613298302606891 := by
  unfold tailWord_7562785
  simp only [CollatzResearch.WordTrace]
  refine ⟨275837429906329040691921809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183891619937552693794614539 275837429906329040691921809)
  ·
    refine ⟨206878072429746780518941357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275837429906329040691921809 206878072429746780518941357)
    ·
      refine ⟨77579277161155042694603009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206878072429746780518941357 77579277161155042694603009)
      ·
        refine ⟨58184457870866282020952257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77579277161155042694603009 58184457870866282020952257)
        ·
          refine ⟨43638343403149711515714193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58184457870866282020952257 43638343403149711515714193)
          ·
            refine ⟨32728757552362283636785645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43638343403149711515714193 32728757552362283636785645)
            ·
              refine ⟨12273284082135856363794617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32728757552362283636785645 12273284082135856363794617)
              ·
                refine ⟨9204963061601892272845963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12273284082135856363794617 9204963061601892272845963)
                ·
                  refine ⟨13807444592402838409268945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9204963061601892272845963 13807444592402838409268945)
                  ·
                    refine ⟨10355583444302128806951709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13807444592402838409268945 10355583444302128806951709)
                    ·
                      refine ⟨3883343791613298302606891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10355583444302128806951709 3883343791613298302606891)
                      ·
                        rfl

theorem cell23_7562785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_7562785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562785 prefixEnd_7562785 := by exact prefixLift 7562785
  have htrace : WordTrace (prefixWord ++ tailWord_7562785) baseStart_7562785 baseEnd_7562785 := by
    simpa [prefixWord, tailWord_7562785, baseEnd_7562785] using wordTrace_append hprefix tailTrace_7562785
  have hstable : (prefixWord ++ tailWord_7562785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562785).length < 2 ^ (prefixWord ++ tailWord_7562785).sum := by decide
  have hdescent : baseEnd_7562785 < baseStart_7562785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562815 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 3]
def baseStart_7562815 : Nat := 118140960795 + 7562815 * 2 ^ 59
def prefixEnd_7562815 : Nat := 4983230072969 + 3 ^ 40 * 7562815 * 2
def baseEnd_7562815 : Nat := 3883359196032933185231753

theorem tailTrace_7562815 : CollatzResearch.WordTrace tailWord_7562815 prefixEnd_7562815 3883359196032933185231753 := by
  unfold tailWord_7562815
  simp only [CollatzResearch.WordTrace]
  refine ⟨275838524096220355815513899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183892349397480237210342599 275838524096220355815513899)
  ·
    refine ⟨413757786144330533723270849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275838524096220355815513899 413757786144330533723270849)
    ·
      refine ⟨310318339608247900292453137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413757786144330533723270849 310318339608247900292453137)
      ·
        refine ⟨232738754706185925219339853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310318339608247900292453137 232738754706185925219339853)
        ·
          refine ⟨87277033014819721957252445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232738754706185925219339853 87277033014819721957252445)
          ·
            refine ⟨32728887380557395733969667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87277033014819721957252445 32728887380557395733969667)
            ·
              refine ⟨49093331070836093600954501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32728887380557395733969667 49093331070836093600954501)
              ·
                refine ⟨9204999575781767550178969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49093331070836093600954501 9204999575781767550178969)
                ·
                  refine ⟨6903749681836325662634227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9204999575781767550178969 6903749681836325662634227)
                  ·
                    refine ⟨10355624522754488493951341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6903749681836325662634227 10355624522754488493951341)
                    ·
                      refine ⟨3883359196032933185231753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10355624522754488493951341 3883359196032933185231753)
                      ·
                        rfl

theorem cell23_7562815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_7562815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562815 prefixEnd_7562815 := by exact prefixLift 7562815
  have htrace : WordTrace (prefixWord ++ tailWord_7562815) baseStart_7562815 baseEnd_7562815 := by
    simpa [prefixWord, tailWord_7562815, baseEnd_7562815] using wordTrace_append hprefix tailTrace_7562815
  have hstable : (prefixWord ++ tailWord_7562815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562815).length < 2 ^ (prefixWord ++ tailWord_7562815).sum := by decide
  have hdescent : baseEnd_7562815 < baseStart_7562815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562821 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_7562821 : Nat := 118140960795 + 7562821 * 2 ^ 59
def prefixEnd_7562821 : Nat := 4983230072969 + 3 ^ 40 * 7562821 * 2
def baseEnd_7562821 : Nat := 3883362276916860161756725

theorem tailTrace_7562821 : CollatzResearch.WordTrace tailWord_7562821 prefixEnd_7562821 3883362276916860161756725 := by
  unfold tailWord_7562821
  simp only [CollatzResearch.WordTrace]
  refine ⟨275838742934198618840232317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183892495289465745893488211 275838742934198618840232317)
  ·
    refine ⟨103439528600324482065087119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275838742934198618840232317 103439528600324482065087119)
    ·
      refine ⟨155159292900486723097630679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103439528600324482065087119 155159292900486723097630679)
      ·
        refine ⟨232738939350730084646446019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155159292900486723097630679 232738939350730084646446019)
        ·
          refine ⟨349108409026095126969669029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232738939350730084646446019 349108409026095126969669029)
          ·
            refine ⟨65457826692392836306812943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349108409026095126969669029 65457826692392836306812943)
            ·
              refine ⟨98186740038589254460219415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65457826692392836306812943 98186740038589254460219415)
              ·
                refine ⟨147280110057883881690329123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98186740038589254460219415 147280110057883881690329123)
                ·
                  refine ⟨220920165086825822535493685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147280110057883881690329123 220920165086825822535493685)
                  ·
                    refine ⟨20711265476889920862702533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220920165086825822535493685 20711265476889920862702533)
                    ·
                      refine ⟨3883362276916860161756725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20711265476889920862702533 3883362276916860161756725)
                      ·
                        rfl

theorem cell23_7562821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_7562821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562821 prefixEnd_7562821 := by exact prefixLift 7562821
  have htrace : WordTrace (prefixWord ++ tailWord_7562821) baseStart_7562821 baseEnd_7562821 := by
    simpa [prefixWord, tailWord_7562821, baseEnd_7562821] using wordTrace_append hprefix tailTrace_7562821
  have hstable : (prefixWord ++ tailWord_7562821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562821).length < 2 ^ (prefixWord ++ tailWord_7562821).sum := by decide
  have hdescent : baseEnd_7562821 < baseStart_7562821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562822 : List Nat := [6, 1, 1, 1, 3, 2, 1, 8]
def baseStart_7562822 : Nat := 118140960795 + 7562822 * 2 ^ 59
def prefixEnd_7562822 : Nat := 4983230072969 + 3 ^ 40 * 7562822 * 2
def baseEnd_7562822 : Nat := 143828251496204246586823

theorem tailTrace_7562822 : CollatzResearch.WordTrace tailWord_7562822 prefixEnd_7562822 143828251496204246586823 := by
  unfold tailWord_7562822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619961856474843625344335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183892519604796664007345813 8619961856474843625344335)
  ·
    refine ⟨12929942784712265438016503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8619961856474843625344335 12929942784712265438016503)
    ·
      refine ⟨19394914177068398157024755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12929942784712265438016503 19394914177068398157024755)
      ·
        refine ⟨29092371265602597235537133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19394914177068398157024755 29092371265602597235537133)
        ·
          refine ⟨10909639224600973963326425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29092371265602597235537133 10909639224600973963326425)
          ·
            refine ⟨8182229418450730472494819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10909639224600973963326425 8182229418450730472494819)
            ·
              refine ⟨12273344127676095708742229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8182229418450730472494819 12273344127676095708742229)
              ·
                refine ⟨143828251496204246586823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12273344127676095708742229 143828251496204246586823)
                ·
                  rfl

theorem cell23_7562822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_7562822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562822 prefixEnd_7562822 := by exact prefixLift 7562822
  have htrace : WordTrace (prefixWord ++ tailWord_7562822) baseStart_7562822 baseEnd_7562822 := by
    simpa [prefixWord, tailWord_7562822, baseEnd_7562822] using wordTrace_append hprefix tailTrace_7562822
  have hstable : (prefixWord ++ tailWord_7562822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562822).length < 2 ^ (prefixWord ++ tailWord_7562822).sum := by decide
  have hdescent : baseEnd_7562822 < baseStart_7562822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562841 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_7562841 : Nat := 118140960795 + 7562841 * 2 ^ 59
def prefixEnd_7562841 : Nat := 4983230072969 + 3 ^ 40 * 7562841 * 2
def baseEnd_7562841 : Nat := 3883372546529950083506633

theorem tailTrace_7562841 : CollatzResearch.WordTrace tailWord_7562841 prefixEnd_7562841 3883372546529950083506633 := by
  unfold tailWord_7562841
  simp only [CollatzResearch.WordTrace]
  refine ⟨275839472394126162255960377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183892981596084108170640251 275839472394126162255960377)
  ·
    refine ⟨206879604295594621691970283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275839472394126162255960377 206879604295594621691970283)
    ·
      refine ⟨310319406443391932537955425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206879604295594621691970283 310319406443391932537955425)
      ·
        refine ⟨232739554832543949403466569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310319406443391932537955425 232739554832543949403466569)
        ·
          refine ⟨174554666124407962052599927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232739554832543949403466569 174554666124407962052599927)
          ·
            refine ⟨261831999186611943078899891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174554666124407962052599927 261831999186611943078899891)
            ·
              refine ⟨392747998779917914618349837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261831999186611943078899891 392747998779917914618349837)
              ·
                refine ⟨147280499542469217981881189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392747998779917914618349837 147280499542469217981881189)
                ·
                  refine ⟨27615093664212978371602723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147280499542469217981881189 27615093664212978371602723)
                  ·
                    refine ⟨41422640496319467557404085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27615093664212978371602723 41422640496319467557404085)
                    ·
                      refine ⟨3883372546529950083506633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41422640496319467557404085 3883372546529950083506633)
                      ·
                        rfl

theorem cell23_7562841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_7562841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562841 prefixEnd_7562841 := by exact prefixLift 7562841
  have htrace : WordTrace (prefixWord ++ tailWord_7562841) baseStart_7562841 baseEnd_7562841 := by
    simpa [prefixWord, tailWord_7562841, baseEnd_7562841] using wordTrace_append hprefix tailTrace_7562841
  have hstable : (prefixWord ++ tailWord_7562841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562841).length < 2 ^ (prefixWord ++ tailWord_7562841).sum := by decide
  have hdescent : baseEnd_7562841 < baseStart_7562841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562855 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_7562855 : Nat := 118140960795 + 7562855 * 2 ^ 59
def prefixEnd_7562855 : Nat := 4983230072969 + 3 ^ 40 * 7562855 * 2
def baseEnd_7562855 : Nat := 3883379735259113028731569

theorem tailTrace_7562855 : CollatzResearch.WordTrace tailWord_7562855 prefixEnd_7562855 3883379735259113028731569 := by
  unfold tailWord_7562855
  simp only [CollatzResearch.WordTrace]
  refine ⟨275839983016075442646970019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183893322010716961764646679 275839983016075442646970019)
  ·
    refine ⟨413759974524113163970455029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275839983016075442646970019 413759974524113163970455029)
    ·
      refine ⟨38789997611635609122230159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 413759974524113163970455029 38789997611635609122230159)
      ·
        refine ⟨58184996417453413683345239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38789997611635609122230159 58184996417453413683345239)
        ·
          refine ⟨87277494626180120525017859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58184996417453413683345239 87277494626180120525017859)
          ·
            refine ⟨130916241939270180787526789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87277494626180120525017859 130916241939270180787526789)
            ·
              refine ⟨24546795363613158897661273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130916241939270180787526789 24546795363613158897661273)
              ·
                refine ⟨18410096522709869173245955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24546795363613158897661273 18410096522709869173245955)
                ·
                  refine ⟨27615144784064803759868933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18410096522709869173245955 27615144784064803759868933)
                  ·
                    refine ⟨5177839647012150704975425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27615144784064803759868933 5177839647012150704975425)
                    ·
                      refine ⟨3883379735259113028731569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177839647012150704975425 3883379735259113028731569)
                      ·
                        rfl

theorem cell23_7562855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_7562855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562855 prefixEnd_7562855 := by exact prefixLift 7562855
  have htrace : WordTrace (prefixWord ++ tailWord_7562855) baseStart_7562855 baseEnd_7562855 := by
    simpa [prefixWord, tailWord_7562855, baseEnd_7562855] using wordTrace_append hprefix tailTrace_7562855
  have hstable : (prefixWord ++ tailWord_7562855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562855).length < 2 ^ (prefixWord ++ tailWord_7562855).sum := by decide
  have hdescent : baseEnd_7562855 < baseStart_7562855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562891 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 3, 7]
def baseStart_7562891 : Nat := 118140960795 + 7562891 * 2 ^ 59
def prefixEnd_7562891 : Nat := 4983230072969 + 3 ^ 40 * 7562891 * 2
def baseEnd_7562891 : Nat := 1294466073520891629293801

theorem tailTrace_7562891 : CollatzResearch.WordTrace tailWord_7562891 prefixEnd_7562891 1294466073520891629293801 := by
  unfold tailWord_7562891
  simp only [CollatzResearch.WordTrace]
  refine ⟨275841296043945020795280527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183894197362630013863520351 275841296043945020795280527)
  ·
    refine ⟨413761944065917531192920791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275841296043945020795280527 413761944065917531192920791)
    ·
      refine ⟨620642916098876296789381187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413761944065917531192920791 620642916098876296789381187)
      ·
        refine ⟨930964374148314445184071781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620642916098876296789381187 930964374148314445184071781)
        ·
          refine ⟨174555820152808958472013459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 930964374148314445184071781 174555820152808958472013459)
          ·
            refine ⟨261833730229213437708020189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174555820152808958472013459 261833730229213437708020189)
            ·
              refine ⟨98187648835955039140507571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261833730229213437708020189 98187648835955039140507571)
              ·
                refine ⟨147281473253932558710761357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98187648835955039140507571 147281473253932558710761357)
                ·
                  refine ⟨55230552470224709516535509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147281473253932558710761357 55230552470224709516535509)
                  ·
                    refine ⟨1294466073520891629293801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55230552470224709516535509 1294466073520891629293801)
                    ·
                      rfl

theorem cell23_7562891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 7].length) (baseStart_7562891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562891 prefixEnd_7562891 := by exact prefixLift 7562891
  have htrace : WordTrace (prefixWord ++ tailWord_7562891) baseStart_7562891 baseEnd_7562891 := by
    simpa [prefixWord, tailWord_7562891, baseEnd_7562891] using wordTrace_append hprefix tailTrace_7562891
  have hstable : (prefixWord ++ tailWord_7562891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562891).length < 2 ^ (prefixWord ++ tailWord_7562891).sum := by decide
  have hdescent : baseEnd_7562891 < baseStart_7562891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562912 : List Nat := [2, 1, 1, 4, 3, 3, 1, 3, 5]
def baseStart_7562912 : Nat := 118140960795 + 7562912 * 2 ^ 59
def prefixEnd_7562912 : Nat := 4983230072969 + 3 ^ 40 * 7562912 * 2
def baseEnd_7562912 : Nat := 431489889295157700635423

theorem tailTrace_7562912 : CollatzResearch.WordTrace tailWord_7562912 prefixEnd_7562912 431489889295157700635423 := by
  unfold tailWord_7562912
  simp only [CollatzResearch.WordTrace]
  refine ⟨137921030988434470690897495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183894707984579294254529993 137921030988434470690897495)
  ·
    refine ⟨206881546482651706036346243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137921030988434470690897495 206881546482651706036346243)
    ·
      refine ⟨310322319723977559054519365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206881546482651706036346243 310322319723977559054519365)
      ·
        refine ⟨58185434948245792322722381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310322319723977559054519365 58185434948245792322722381)
        ·
          refine ⟨21819538105592172121020893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58185434948245792322722381 21819538105592172121020893)
          ·
            refine ⟨8182326789597064545382835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21819538105592172121020893 8182326789597064545382835)
            ·
              refine ⟨12273490184395596818074253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8182326789597064545382835 12273490184395596818074253)
              ·
                refine ⟨4602558819148348806777845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12273490184395596818074253 4602558819148348806777845)
                ·
                  refine ⟨431489889295157700635423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4602558819148348806777845 431489889295157700635423)
                  ·
                    rfl

theorem cell23_7562912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 5].length) (baseStart_7562912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562912 prefixEnd_7562912 := by exact prefixLift 7562912
  have htrace : WordTrace (prefixWord ++ tailWord_7562912) baseStart_7562912 baseEnd_7562912 := by
    simpa [prefixWord, tailWord_7562912, baseEnd_7562912] using wordTrace_append hprefix tailTrace_7562912
  have hstable : (prefixWord ++ tailWord_7562912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562912).length < 2 ^ (prefixWord ++ tailWord_7562912).sum := by decide
  have hdescent : baseEnd_7562912 < baseStart_7562912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562921 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 4, 8]
def baseStart_7562921 : Nat := 118140960795 + 7562921 * 2 ^ 59
def prefixEnd_7562921 : Nat := 4983230072969 + 3 ^ 40 * 7562921 * 2
def baseEnd_7562921 : Nat := 1294471208327436590168755

theorem tailTrace_7562921 : CollatzResearch.WordTrace tailWord_7562921 prefixEnd_7562921 1294471208327436590168755 := by
  unfold tailWord_7562921
  simp only [CollatzResearch.WordTrace]
  refine ⟨275842390233836335918872617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183894926822557557279248411 275842390233836335918872617)
  ·
    refine ⟨206881792675377251939154463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275842390233836335918872617 206881792675377251939154463)
    ·
      refine ⟨310322689013065877908731695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206881792675377251939154463 310322689013065877908731695)
      ·
        refine ⟨465484033519598816863097543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310322689013065877908731695 465484033519598816863097543)
        ·
          refine ⟨698226050279398225294646315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465484033519598816863097543 698226050279398225294646315)
          ·
            refine ⟨1047339075419097337941969473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698226050279398225294646315 1047339075419097337941969473)
            ·
              refine ⟨785504306564323003456477105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047339075419097337941969473 785504306564323003456477105)
              ·
                refine ⟨589128229923242252592357829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785504306564323003456477105 589128229923242252592357829)
                ·
                  refine ⟨110461543110607922361067093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 589128229923242252592357829 110461543110607922361067093)
                  ·
                    refine ⟨1294471208327436590168755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110461543110607922361067093 1294471208327436590168755)
                    ·
                      rfl

theorem cell23_7562921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_7562921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562921 prefixEnd_7562921 := by exact prefixLift 7562921
  have htrace : WordTrace (prefixWord ++ tailWord_7562921) baseStart_7562921 baseEnd_7562921 := by
    simpa [prefixWord, tailWord_7562921, baseEnd_7562921] using wordTrace_append hprefix tailTrace_7562921
  have hstable : (prefixWord ++ tailWord_7562921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562921).length < 2 ^ (prefixWord ++ tailWord_7562921).sum := by decide
  have hdescent : baseEnd_7562921 < baseStart_7562921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562925 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_7562925 : Nat := 118140960795 + 7562925 * 2 ^ 59
def prefixEnd_7562925 : Nat := 4983230072969 + 3 ^ 40 * 7562925 * 2
def baseEnd_7562925 : Nat := 1294471892968309251618749

theorem tailTrace_7562925 : CollatzResearch.WordTrace tailWord_7562925 prefixEnd_7562925 1294471892968309251618749 := by
  unfold tailWord_7562925
  simp only [CollatzResearch.WordTrace]
  refine ⟨275842536125821844602018229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183895024083881229734678819 275842536125821844602018229)
  ·
    refine ⟨25860237761795797931439209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275842536125821844602018229 25860237761795797931439209)
    ·
      refine ⟨19395178321346848448579407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25860237761795797931439209 19395178321346848448579407)
      ·
        refine ⟨29092767482020272672869111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19395178321346848448579407 29092767482020272672869111)
        ·
          refine ⟨43639151223030409009303667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29092767482020272672869111 43639151223030409009303667)
          ·
            refine ⟨65458726834545613513955501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43639151223030409009303667 65458726834545613513955501)
            ·
              refine ⟨24547022562954605067733313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65458726834545613513955501 24547022562954605067733313)
              ·
                refine ⟨18410266922215953800799985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24547022562954605067733313 18410266922215953800799985)
                ·
                  refine ⟨13807700191661965350599989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18410266922215953800799985 13807700191661965350599989)
                  ·
                    refine ⟨1294471892968309251618749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13807700191661965350599989 1294471892968309251618749)
                    ·
                      rfl

theorem cell23_7562925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_7562925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562925 prefixEnd_7562925 := by exact prefixLift 7562925
  have htrace : WordTrace (prefixWord ++ tailWord_7562925) baseStart_7562925 baseEnd_7562925 := by
    simpa [prefixWord, tailWord_7562925, baseEnd_7562925] using wordTrace_append hprefix tailTrace_7562925
  have hstable : (prefixWord ++ tailWord_7562925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562925).length < 2 ^ (prefixWord ++ tailWord_7562925).sum := by decide
  have hdescent : baseEnd_7562925 < baseStart_7562925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562928 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_7562928 : Nat := 118140960795 + 7562928 * 2 ^ 59
def prefixEnd_7562928 : Nat := 4983230072969 + 3 ^ 40 * 7562928 * 2
def baseEnd_7562928 : Nat := 3883417219346891243118733

theorem tailTrace_7562928 : CollatzResearch.WordTrace tailWord_7562928 prefixEnd_7562928 3883417219346891243118733 := by
  unfold tailWord_7562928
  simp only [CollatzResearch.WordTrace]
  refine ⟨137921322772405488057188719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183895097029873984076251625 137921322772405488057188719)
  ·
    refine ⟨206881984158608232085783079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137921322772405488057188719 206881984158608232085783079)
    ·
      refine ⟨310322976237912348128674619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206881984158608232085783079 310322976237912348128674619)
      ·
        refine ⟨465484464356868522193011929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310322976237912348128674619 465484464356868522193011929)
        ·
          refine ⟨349113348267651391644758947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465484464356868522193011929 349113348267651391644758947)
          ·
            refine ⟨523670022401477087467138421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349113348267651391644758947 523670022401477087467138421)
            ·
              refine ⟨49094064600138476950044227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 523670022401477087467138421 49094064600138476950044227)
              ·
                refine ⟨73641096900207715425066341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49094064600138476950044227 73641096900207715425066341)
                ·
                  refine ⟨13807705668788946642199939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73641096900207715425066341 13807705668788946642199939)
                  ·
                    refine ⟨20711558503183419963299909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13807705668788946642199939 20711558503183419963299909)
                    ·
                      refine ⟨3883417219346891243118733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20711558503183419963299909 3883417219346891243118733)
                      ·
                        rfl

theorem cell23_7562928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_7562928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562928 prefixEnd_7562928 := by exact prefixLift 7562928
  have htrace : WordTrace (prefixWord ++ tailWord_7562928) baseStart_7562928 baseEnd_7562928 := by
    simpa [prefixWord, tailWord_7562928, baseEnd_7562928] using wordTrace_append hprefix tailTrace_7562928
  have hstable : (prefixWord ++ tailWord_7562928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562928).length < 2 ^ (prefixWord ++ tailWord_7562928).sum := by decide
  have hdescent : baseEnd_7562928 < baseStart_7562928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562962 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_7562962 : Nat := 118140960795 + 7562962 * 2 ^ 59
def prefixEnd_7562962 : Nat := 4983230072969 + 3 ^ 40 * 7562962 * 2
def baseEnd_7562962 : Nat := 3883434677689144110093577

theorem tailTrace_7562962 : CollatzResearch.WordTrace tailWord_7562962 prefixEnd_7562962 3883434677689144110093577 := by
  unfold tailWord_7562962
  simp only [CollatzResearch.WordTrace]
  refine ⟨68960971406671949980278785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183895923751125199947410093 68960971406671949980278785)
  ·
    refine ⟨51720728555003962485209089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68960971406671949980278785 51720728555003962485209089)
    ·
      refine ⟨38790546416252971863906817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51720728555003962485209089 38790546416252971863906817)
      ·
        refine ⟨29092909812189728897930113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38790546416252971863906817 29092909812189728897930113)
        ·
          refine ⟨21819682359142296673447585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29092909812189728897930113 21819682359142296673447585)
          ·
            refine ⟨16364761769356722505085689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21819682359142296673447585 16364761769356722505085689)
            ·
              refine ⟨12273571327017541878814267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16364761769356722505085689 12273571327017541878814267)
              ·
                refine ⟨18410356990526312818221401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12273571327017541878814267 18410356990526312818221401)
                ·
                  refine ⟨13807767742894734613666051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18410356990526312818221401 13807767742894734613666051)
                  ·
                    refine ⟨20711651614342101920499077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13807767742894734613666051 20711651614342101920499077)
                    ·
                      refine ⟨3883434677689144110093577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20711651614342101920499077 3883434677689144110093577)
                      ·
                        rfl

theorem cell23_7562962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_7562962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562962 prefixEnd_7562962 := by exact prefixLift 7562962
  have htrace : WordTrace (prefixWord ++ tailWord_7562962) baseStart_7562962 baseEnd_7562962 := by
    simpa [prefixWord, tailWord_7562962, baseEnd_7562962] using wordTrace_append hprefix tailTrace_7562962
  have hstable : (prefixWord ++ tailWord_7562962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562962).length < 2 ^ (prefixWord ++ tailWord_7562962).sum := by decide
  have hdescent : baseEnd_7562962 < baseStart_7562962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562989 : List Nat := [1, 5, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_7562989 : Nat := 118140960795 + 7562989 * 2 ^ 59
def prefixEnd_7562989 : Nat := 4983230072969 + 3 ^ 40 * 7562989 * 2
def baseEnd_7562989 : Nat := 1294482847222271834818651

theorem tailTrace_7562989 : CollatzResearch.WordTrace tailWord_7562989 prefixEnd_7562989 1294482847222271834818651 := by
  unfold tailWord_7562989
  simp only [CollatzResearch.WordTrace]
  refine ⟨275844870397589983532348021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183896580265059989021565347 275844870397589983532348021)
  ·
    refine ⟨25860456599774060956157627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275844870397589983532348021 25860456599774060956157627)
    ·
      refine ⟨38790684899661091434236441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25860456599774060956157627 38790684899661091434236441)
      ·
        refine ⟨29093013674745818575677331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38790684899661091434236441 29093013674745818575677331)
        ·
          refine ⟨43639520512118727863515997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29093013674745818575677331 43639520512118727863515997)
          ·
            refine ⟨16364820192044522948818499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43639520512118727863515997 16364820192044522948818499)
            ·
              refine ⟨24547230288066784423227749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16364820192044522948818499 24547230288066784423227749)
              ·
                refine ⟨4602605679012522079355203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24547230288066784423227749 4602605679012522079355203)
                ·
                  refine ⟨6903908518518783119032805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602605679012522079355203 6903908518518783119032805)
                  ·
                    refine ⟨1294482847222271834818651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6903908518518783119032805 1294482847222271834818651)
                    ·
                      rfl

theorem cell23_7562989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_7562989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562989 prefixEnd_7562989 := by exact prefixLift 7562989
  have htrace : WordTrace (prefixWord ++ tailWord_7562989) baseStart_7562989 baseEnd_7562989 := by
    simpa [prefixWord, tailWord_7562989, baseEnd_7562989] using wordTrace_append hprefix tailTrace_7562989
  have hstable : (prefixWord ++ tailWord_7562989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562989).length < 2 ^ (prefixWord ++ tailWord_7562989).sum := by decide
  have hdescent : baseEnd_7562989 < baseStart_7562989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7562996 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7562996 : Nat := 118140960795 + 7562996 * 2 ^ 59
def prefixEnd_7562996 : Nat := 4983230072969 + 3 ^ 40 * 7562996 * 2
def baseEnd_7562996 : Nat := 3883452136031396977068421

theorem tailTrace_7562996 : CollatzResearch.WordTrace tailWord_7562996 prefixEnd_7562996 3883452136031396977068421 := by
  unfold tailWord_7562996
  simp only [CollatzResearch.WordTrace]
  refine ⟨137922562854282311863926421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183896750472376415818568561 137922562854282311863926421)
  ·
    refine ⟨6465120133794483368621551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137922562854282311863926421 6465120133794483368621551)
    ·
      refine ⟨9697680200691725052932327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6465120133794483368621551 9697680200691725052932327)
      ·
        refine ⟨14546520301037587579398491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9697680200691725052932327 14546520301037587579398491)
        ·
          refine ⟨21819780451556381369097737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14546520301037587579398491 21819780451556381369097737)
          ·
            refine ⟨16364835338667286026823303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21819780451556381369097737 16364835338667286026823303)
            ·
              refine ⟨24547253008000929040234955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16364835338667286026823303 24547253008000929040234955)
              ·
                refine ⟨36820879512001393560352433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24547253008000929040234955 36820879512001393560352433)
                ·
                  refine ⟨27615659634001045170264325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36820879512001393560352433 27615659634001045170264325)
                  ·
                    refine ⟨5177936181375195969424561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27615659634001045170264325 5177936181375195969424561)
                    ·
                      refine ⟨3883452136031396977068421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5177936181375195969424561 3883452136031396977068421)
                      ·
                        rfl

theorem cell23_7562996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7562996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7562996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7562996 prefixEnd_7562996 := by exact prefixLift 7562996
  have htrace : WordTrace (prefixWord ++ tailWord_7562996) baseStart_7562996 baseEnd_7562996 := by
    simpa [prefixWord, tailWord_7562996, baseEnd_7562996] using wordTrace_append hprefix tailTrace_7562996
  have hstable : (prefixWord ++ tailWord_7562996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7562996).length < 2 ^ (prefixWord ++ tailWord_7562996).sum := by decide
  have hdescent : baseEnd_7562996 < baseStart_7562996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7562996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563012 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_7563012 : Nat := 118140960795 + 7563012 * 2 ^ 59
def prefixEnd_7563012 : Nat := 4983230072969 + 3 ^ 40 * 7563012 * 2
def baseEnd_7563012 : Nat := 3883460351721868914468347

theorem tailTrace_7563012 : CollatzResearch.WordTrace tailWord_7563012 prefixEnd_7563012 3883460351721868914468347 := by
  unfold tailWord_7563012
  simp only [CollatzResearch.WordTrace]
  refine ⟨137922854638253329230217645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183897139517671105640290193 137922854638253329230217645)
  ·
    refine ⟨51721070489344998461331617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137922854638253329230217645 51721070489344998461331617)
    ·
      refine ⟨38790802867008748845998713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51721070489344998461331617 38790802867008748845998713)
      ·
        refine ⟨29093102150256561634499035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38790802867008748845998713 29093102150256561634499035)
        ·
          refine ⟨43639653225384842451748553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29093102150256561634499035 43639653225384842451748553)
          ·
            refine ⟨32729739919038631838811415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43639653225384842451748553 32729739919038631838811415)
            ·
              refine ⟨49094609878557947758217123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32729739919038631838811415 49094609878557947758217123)
              ·
                refine ⟨73641914817836921637325685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49094609878557947758217123 73641914817836921637325685)
                ·
                  refine ⟨6903929514172211403499283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73641914817836921637325685 6903929514172211403499283)
                  ·
                    refine ⟨10355894271258317105248925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6903929514172211403499283 10355894271258317105248925)
                    ·
                      refine ⟨3883460351721868914468347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10355894271258317105248925 3883460351721868914468347)
                      ·
                        rfl

theorem cell23_7563012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_7563012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563012 prefixEnd_7563012 := by exact prefixLift 7563012
  have htrace : WordTrace (prefixWord ++ tailWord_7563012) baseStart_7563012 baseEnd_7563012 := by
    simpa [prefixWord, tailWord_7563012, baseEnd_7563012] using wordTrace_append hprefix tailTrace_7563012
  have hstable : (prefixWord ++ tailWord_7563012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563012).length < 2 ^ (prefixWord ++ tailWord_7563012).sum := by decide
  have hdescent : baseEnd_7563012 < baseStart_7563012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563029 : List Nat := [1, 3, 2, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_7563029 : Nat := 118140960795 + 7563029 * 2 ^ 59
def prefixEnd_7563029 : Nat := 4983230072969 + 3 ^ 40 * 7563029 * 2
def baseEnd_7563029 : Nat := 3883469080892995347955769

theorem tailTrace_7563029 : CollatzResearch.WordTrace tailWord_7563029 prefixEnd_7563029 3883469080892995347955769 := by
  unfold tailWord_7563029
  simp only [CollatzResearch.WordTrace]
  refine ⟨275846329317445070363804141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183897552878296713575869427 275846329317445070363804141)
  ·
    refine ⟨103442373494041901386426553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275846329317445070363804141 103442373494041901386426553)
    ·
      refine ⟨77581780120531426039819915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103442373494041901386426553 77581780120531426039819915)
      ·
        refine ⟨116372670180797139059729873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77581780120531426039819915 116372670180797139059729873)
        ·
          refine ⟨87279502635597854294797405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116372670180797139059729873 87279502635597854294797405)
          ·
            refine ⟨32729813488349195360549027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87279502635597854294797405 32729813488349195360549027)
            ·
              refine ⟨49094720232523793040823541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32729813488349195360549027 49094720232523793040823541)
              ·
                refine ⟨4602630021799105597577207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49094720232523793040823541 4602630021799105597577207)
                ·
                  refine ⟨6903945032698658396365811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602630021799105597577207 6903945032698658396365811)
                  ·
                    refine ⟨10355917549047987594548717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6903945032698658396365811 10355917549047987594548717)
                    ·
                      refine ⟨3883469080892995347955769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10355917549047987594548717 3883469080892995347955769)
                      ·
                        rfl

theorem cell23_7563029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_7563029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563029 prefixEnd_7563029 := by exact prefixLift 7563029
  have htrace : WordTrace (prefixWord ++ tailWord_7563029) baseStart_7563029 baseEnd_7563029 := by
    simpa [prefixWord, tailWord_7563029, baseEnd_7563029] using wordTrace_append hprefix tailTrace_7563029
  have hstable : (prefixWord ++ tailWord_7563029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563029).length < 2 ^ (prefixWord ++ tailWord_7563029).sum := by decide
  have hdescent : baseEnd_7563029 < baseStart_7563029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563032 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 1, 5]
def baseStart_7563032 : Nat := 118140960795 + 7563032 * 2 ^ 59
def prefixEnd_7563032 : Nat := 4983230072969 + 3 ^ 40 * 7563032 * 2
def baseEnd_7563032 : Nat := 1294490207111652945406085

theorem tailTrace_7563032 : CollatzResearch.WordTrace tailWord_7563032 prefixEnd_7563032 1294490207111652945406085 := by
  unfold tailWord_7563032
  simp only [CollatzResearch.WordTrace]
  refine ⟨137923219368217100938081675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183897625824289467917442233 137923219368217100938081675)
  ·
    refine ⟨206884829052325651407122513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137923219368217100938081675 206884829052325651407122513)
    ·
      refine ⟨155163621789244238555341885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206884829052325651407122513 155163621789244238555341885)
      ·
        refine ⟨58186358170966589458253207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155163621789244238555341885 58186358170966589458253207)
        ·
          refine ⟨87279537256449884187379811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58186358170966589458253207 87279537256449884187379811)
          ·
            refine ⟨130919305884674826281069717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87279537256449884187379811 130919305884674826281069717)
            ·
              refine ⟨6136842463344132481925143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130919305884674826281069717 6136842463344132481925143)
              ·
                refine ⟨9205263695016198722887715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136842463344132481925143 9205263695016198722887715)
                ·
                  refine ⟨13807895542524298084331573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205263695016198722887715 13807895542524298084331573)
                  ·
                    refine ⟨1294490207111652945406085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13807895542524298084331573 1294490207111652945406085)
                    ·
                      rfl

theorem cell23_7563032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_7563032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563032 prefixEnd_7563032 := by exact prefixLift 7563032
  have htrace : WordTrace (prefixWord ++ tailWord_7563032) baseStart_7563032 baseEnd_7563032 := by
    simpa [prefixWord, tailWord_7563032, baseEnd_7563032] using wordTrace_append hprefix tailTrace_7563032
  have hstable : (prefixWord ++ tailWord_7563032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563032).length < 2 ^ (prefixWord ++ tailWord_7563032).sum := by decide
  have hdescent : baseEnd_7563032 < baseStart_7563032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563035 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 4]
def baseStart_7563035 : Nat := 118140960795 + 7563035 * 2 ^ 59
def prefixEnd_7563035 : Nat := 4983230072969 + 3 ^ 40 * 7563035 * 2
def baseEnd_7563035 : Nat := 3883472161776922324480741

theorem tailTrace_7563035 : CollatzResearch.WordTrace tailWord_7563035 prefixEnd_7563035 3883472161776922324480741 := by
  unfold tailWord_7563035
  simp only [CollatzResearch.WordTrace]
  refine ⟨275846548155423333388522559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183897698770282222259015039 275846548155423333388522559)
  ·
    refine ⟨413769822233135000082783839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275846548155423333388522559 413769822233135000082783839)
    ·
      refine ⟨620654733349702500124175759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413769822233135000082783839 620654733349702500124175759)
      ·
        refine ⟨930982100024553750186263639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620654733349702500124175759 930982100024553750186263639)
        ·
          refine ⟨1396473150036830625279395459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930982100024553750186263639 1396473150036830625279395459)
          ·
            refine ⟨2094709725055245937919093189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396473150036830625279395459 2094709725055245937919093189)
            ·
              refine ⟨392758073447858613359829973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2094709725055245937919093189 392758073447858613359829973)
              ·
                refine ⟨9205267346434186250621015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 392758073447858613359829973 9205267346434186250621015)
                ·
                  refine ⟨13807901019651279375931523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205267346434186250621015 13807901019651279375931523)
                  ·
                    refine ⟨20711851529476919063897285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13807901019651279375931523 20711851529476919063897285)
                    ·
                      refine ⟨3883472161776922324480741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20711851529476919063897285 3883472161776922324480741)
                      ·
                        rfl

theorem cell23_7563035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 4].length) (baseStart_7563035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563035 prefixEnd_7563035 := by exact prefixLift 7563035
  have htrace : WordTrace (prefixWord ++ tailWord_7563035) baseStart_7563035 baseEnd_7563035 := by
    simpa [prefixWord, tailWord_7563035, baseEnd_7563035] using wordTrace_append hprefix tailTrace_7563035
  have hstable : (prefixWord ++ tailWord_7563035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563035).length < 2 ^ (prefixWord ++ tailWord_7563035).sum := by decide
  have hdescent : baseEnd_7563035 < baseStart_7563035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563069 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7563069 : Nat := 118140960795 + 7563069 * 2 ^ 59
def prefixEnd_7563069 : Nat := 4983230072969 + 3 ^ 40 * 7563069 * 2
def baseEnd_7563069 : Nat := 3883489620119175191455585

theorem tailTrace_7563069 : CollatzResearch.WordTrace tailWord_7563069 prefixEnd_7563069 3883489620119175191455585 := by
  unfold tailWord_7563069
  simp only [CollatzResearch.WordTrace]
  refine ⟨275847788237300157195260261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183898525491533438130173507 275847788237300157195260261)
  ·
    refine ⟨51721460294493779474111299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275847788237300157195260261 51721460294493779474111299)
    ·
      refine ⟨77582190441740669211166949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51721460294493779474111299 77582190441740669211166949)
      ·
        refine ⟨14546660707826375477093803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77582190441740669211166949 14546660707826375477093803)
        ·
          refine ⟨21819991061739563215640705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14546660707826375477093803 21819991061739563215640705)
          ·
            refine ⟨16364993296304672411730529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21819991061739563215640705 16364993296304672411730529)
            ·
              refine ⟨12273744972228504308797897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16364993296304672411730529 12273744972228504308797897)
              ·
                refine ⟨9205308729171378231598423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12273744972228504308797897 9205308729171378231598423)
                ·
                  refine ⟨13807963093757067347397635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205308729171378231598423 13807963093757067347397635)
                  ·
                    refine ⟨20711944640635601021096453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13807963093757067347397635 20711944640635601021096453)
                    ·
                      refine ⟨3883489620119175191455585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20711944640635601021096453 3883489620119175191455585)
                      ·
                        rfl

theorem cell23_7563069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7563069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563069 prefixEnd_7563069 := by exact prefixLift 7563069
  have htrace : WordTrace (prefixWord ++ tailWord_7563069) baseStart_7563069 baseEnd_7563069 := by
    simpa [prefixWord, tailWord_7563069, baseEnd_7563069] using wordTrace_append hprefix tailTrace_7563069
  have hstable : (prefixWord ++ tailWord_7563069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563069).length < 2 ^ (prefixWord ++ tailWord_7563069).sum := by decide
  have hdescent : baseEnd_7563069 < baseStart_7563069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563075 : List Nat := [1, 1, 1, 3, 1, 5, 4, 7]
def baseStart_7563075 : Nat := 118140960795 + 7563075 * 2 ^ 59
def prefixEnd_7563075 : Nat := 4983230072969 + 3 ^ 40 * 7563075 * 2
def baseEnd_7563075 : Nat := 143833063000114895110391

theorem tailTrace_7563075 : CollatzResearch.WordTrace tailWord_7563075 prefixEnd_7563075 143833063000114895110391 := by
  unfold tailWord_7563075
  simp only [CollatzResearch.WordTrace]
  refine ⟨275848007075278420219978679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183898671383518946813319119 275848007075278420219978679)
  ·
    refine ⟨413772010612917630329968019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275848007075278420219978679 413772010612917630329968019)
    ·
      refine ⟨620658015919376445494952029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413772010612917630329968019 620658015919376445494952029)
      ·
        refine ⟨232746755969766167060607011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620658015919376445494952029 232746755969766167060607011)
        ·
          refine ⟨349120133954649250590910517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232746755969766167060607011 349120133954649250590910517)
          ·
            refine ⟨32730012558248367242897861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349120133954649250590910517 32730012558248367242897861)
            ·
              refine ⟨6136877354671568858043349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32730012558248367242897861 6136877354671568858043349)
              ·
                refine ⟨143833063000114895110391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6136877354671568858043349 143833063000114895110391)
                ·
                  rfl

theorem cell23_7563075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 7].length) (baseStart_7563075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563075 prefixEnd_7563075 := by exact prefixLift 7563075
  have htrace : WordTrace (prefixWord ++ tailWord_7563075) baseStart_7563075 baseEnd_7563075 := by
    simpa [prefixWord, tailWord_7563075, baseEnd_7563075] using wordTrace_append hprefix tailTrace_7563075
  have hstable : (prefixWord ++ tailWord_7563075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563075).length < 2 ^ (prefixWord ++ tailWord_7563075).sum := by decide
  have hdescent : baseEnd_7563075 < baseStart_7563075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563088 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 1, 9]
def baseStart_7563088 : Nat := 118140960795 + 7563088 * 2 ^ 59
def prefixEnd_7563088 : Nat := 4983230072969 + 3 ^ 40 * 7563088 * 2
def baseEnd_7563088 : Nat := 1294499792083870205705999

theorem tailTrace_7563088 : CollatzResearch.WordTrace tailWord_7563088 prefixEnd_7563088 1294499792083870205705999 := by
  unfold tailWord_7563088
  simp only [CollatzResearch.WordTrace]
  refine ⟨137924240612115661720100959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183898987482820882293467945 137924240612115661720100959)
  ·
    refine ⟨206886360918173492580151439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137924240612115661720100959 206886360918173492580151439)
    ·
      refine ⟨310329541377260238870227159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206886360918173492580151439 310329541377260238870227159)
      ·
        refine ⟨465494312065890358305340739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310329541377260238870227159 465494312065890358305340739)
        ·
          refine ⟨698241468098835537458011109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465494312065890358305340739 698241468098835537458011109)
          ·
            refine ⟨130920275268531663273377083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 698241468098835537458011109 130920275268531663273377083)
            ·
              refine ⟨196380412902797494910065625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130920275268531663273377083 196380412902797494910065625)
              ·
                refine ⟨147285309677098121182549219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196380412902797494910065625 147285309677098121182549219)
                ·
                  refine ⟨220927964515647181773823829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147285309677098121182549219 220927964515647181773823829)
                  ·
                    refine ⟨1294499792083870205705999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 220927964515647181773823829 1294499792083870205705999)
                    ·
                      rfl

theorem cell23_7563088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_7563088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563088 prefixEnd_7563088 := by exact prefixLift 7563088
  have htrace : WordTrace (prefixWord ++ tailWord_7563088) baseStart_7563088 baseEnd_7563088 := by
    simpa [prefixWord, tailWord_7563088, baseEnd_7563088] using wordTrace_append hprefix tailTrace_7563088
  have hstable : (prefixWord ++ tailWord_7563088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563088).length < 2 ^ (prefixWord ++ tailWord_7563088).sum := by decide
  have hdescent : baseEnd_7563088 < baseStart_7563088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563103 : List Nat := [1, 1, 2, 3, 1, 5, 3, 2, 1, 2, 2]
def baseStart_7563103 : Nat := 118140960795 + 7563103 * 2 ^ 59
def prefixEnd_7563103 : Nat := 4983230072969 + 3 ^ 40 * 7563103 * 2
def baseEnd_7563103 : Nat := 3883507078461428058430429

theorem tailTrace_7563103 : CollatzResearch.WordTrace tailWord_7563103 prefixEnd_7563103 3883507078461428058430429 := by
  unfold tailWord_7563103
  simp only [CollatzResearch.WordTrace]
  refine ⟨275849028319176981001997963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183899352212784654001331975 275849028319176981001997963)
  ·
    refine ⟨413773542478765471502996945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275849028319176981001997963 413773542478765471502996945)
    ·
      refine ⟨310330156859074103627247709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413773542478765471502996945 310330156859074103627247709)
      ·
        refine ⟨116373808822152788860217891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310330156859074103627247709 116373808822152788860217891)
        ·
          refine ⟨174560713233229183290326837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116373808822152788860217891 174560713233229183290326837)
          ·
            refine ⟨16365066865615235933468141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174560713233229183290326837 16365066865615235933468141)
            ·
              refine ⟨6136900074605713475050553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16365066865615235933468141 6136900074605713475050553)
              ·
                refine ⟨4602675055954285106287915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6136900074605713475050553 4602675055954285106287915)
                ·
                  refine ⟨6904012583931427659431873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602675055954285106287915 6904012583931427659431873)
                  ·
                    refine ⟨5178009437948570744573905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6904012583931427659431873 5178009437948570744573905)
                    ·
                      refine ⟨3883507078461428058430429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5178009437948570744573905 3883507078461428058430429)
                      ·
                        rfl

theorem cell23_7563103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_7563103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563103 prefixEnd_7563103 := by exact prefixLift 7563103
  have htrace : WordTrace (prefixWord ++ tailWord_7563103) baseStart_7563103 baseEnd_7563103 := by
    simpa [prefixWord, tailWord_7563103, baseEnd_7563103] using wordTrace_append hprefix tailTrace_7563103
  have hstable : (prefixWord ++ tailWord_7563103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563103).length < 2 ^ (prefixWord ++ tailWord_7563103).sum := by decide
  have hdescent : baseEnd_7563103 < baseStart_7563103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563145 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_7563145 : Nat := 118140960795 + 7563145 * 2 ^ 59
def prefixEnd_7563145 : Nat := 4983230072969 + 3 ^ 40 * 7563145 * 2
def baseEnd_7563145 : Nat := 3883528644648916894105235

theorem tailTrace_7563145 : CollatzResearch.WordTrace tailWord_7563145 prefixEnd_7563145 3883528644648916894105235 := by
  unfold tailWord_7563145
  simp only [CollatzResearch.WordTrace]
  refine ⟨275850560185024822175026889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183900373456683214783351259 275850560185024822175026889)
  ·
    refine ⟨206887920138768616631270167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275850560185024822175026889 206887920138768616631270167)
    ·
      refine ⟨310331880208152924946905251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206887920138768616631270167 310331880208152924946905251)
      ·
        refine ⟨465497820312229387420357877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310331880208152924946905251 465497820312229387420357877)
        ·
          refine ⟨43640420654271505070658551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 465497820312229387420357877 43640420654271505070658551)
          ·
            refine ⟨65460630981407257605987827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43640420654271505070658551 65460630981407257605987827)
            ·
              refine ⟨98190946472110886408981741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65460630981407257605987827 98190946472110886408981741)
              ·
                refine ⟨36821604927041582403368153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98190946472110886408981741 36821604927041582403368153)
                ·
                  refine ⟨27616203695281186802526115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36821604927041582403368153 27616203695281186802526115)
                  ·
                    refine ⟨41424305542921780203789173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27616203695281186802526115 41424305542921780203789173)
                    ·
                      refine ⟨3883528644648916894105235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41424305542921780203789173 3883528644648916894105235)
                      ·
                        rfl

theorem cell23_7563145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_7563145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563145 prefixEnd_7563145 := by exact prefixLift 7563145
  have htrace : WordTrace (prefixWord ++ tailWord_7563145) baseStart_7563145 baseEnd_7563145 := by
    simpa [prefixWord, tailWord_7563145, baseEnd_7563145] using wordTrace_append hprefix tailTrace_7563145
  have hstable : (prefixWord ++ tailWord_7563145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563145).length < 2 ^ (prefixWord ++ tailWord_7563145).sum := by decide
  have hdescent : baseEnd_7563145 < baseStart_7563145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563162 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_7563162 : Nat := 118140960795 + 7563162 * 2 ^ 59
def prefixEnd_7563162 : Nat := 4983230072969 + 3 ^ 40 * 7563162 * 2
def baseEnd_7563162 : Nat := 3883537373820043327592657

theorem tailTrace_7563162 : CollatzResearch.WordTrace tailWord_7563162 prefixEnd_7563162 3883537373820043327592657 := by
  unfold tailWord_7563162
  simp only [CollatzResearch.WordTrace]
  refine ⟨68962795056490808519598935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183900786817308822718930493 68962795056490808519598935)
  ·
    refine ⟨103444192584736212779398403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68962795056490808519598935 103444192584736212779398403)
    ·
      refine ⟨155166288877104319169097605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103444192584736212779398403 155166288877104319169097605)
      ·
        refine ⟨29093679164457059844205801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155166288877104319169097605 29093679164457059844205801)
        ·
          refine ⟨21820259373342794883154351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29093679164457059844205801 21820259373342794883154351)
          ·
            refine ⟨32730389060014192324731527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21820259373342794883154351 32730389060014192324731527)
            ·
              refine ⟨49095583590021288487097291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32730389060014192324731527 49095583590021288487097291)
              ·
                refine ⟨73643375385031932730645937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49095583590021288487097291 73643375385031932730645937)
                ·
                  refine ⟨55232531538773949547984453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73643375385031932730645937 55232531538773949547984453)
                  ·
                    refine ⟨10356099663520115540247085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55232531538773949547984453 10356099663520115540247085)
                    ·
                      refine ⟨3883537373820043327592657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10356099663520115540247085 3883537373820043327592657)
                      ·
                        rfl

theorem cell23_7563162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_7563162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563162 prefixEnd_7563162 := by exact prefixLift 7563162
  have htrace : WordTrace (prefixWord ++ tailWord_7563162) baseStart_7563162 baseEnd_7563162 := by
    simpa [prefixWord, tailWord_7563162, baseEnd_7563162] using wordTrace_append hprefix tailTrace_7563162
  have hstable : (prefixWord ++ tailWord_7563162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563162).length < 2 ^ (prefixWord ++ tailWord_7563162).sum := by decide
  have hdescent : baseEnd_7563162 < baseStart_7563162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563172 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_7563172 : Nat := 118140960795 + 7563172 * 2 ^ 59
def prefixEnd_7563172 : Nat := 4983230072969 + 3 ^ 40 * 7563172 * 2
def baseEnd_7563172 : Nat := 3883542508626588288467611

theorem tailTrace_7563172 : CollatzResearch.WordTrace tailWord_7563172 prefixEnd_7563172 3883542508626588288467611 := by
  unfold tailWord_7563172
  simp only [CollatzResearch.WordTrace]
  refine ⟨137925772477963502893129885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183901029970618003857506513 137925772477963502893129885)
  ·
    refine ⟨51722164679236313584923707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137925772477963502893129885 51722164679236313584923707)
    ·
      refine ⟨77583247018854470377385561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51722164679236313584923707 77583247018854470377385561)
      ·
        refine ⟨58187435264140852783039171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77583247018854470377385561 58187435264140852783039171)
        ·
          refine ⟨87281152896211279174558757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58187435264140852783039171 87281152896211279174558757)
          ·
            refine ⟨16365216168039614845229767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87281152896211279174558757 16365216168039614845229767)
            ·
              refine ⟨24547824252059422267844651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16365216168039614845229767 24547824252059422267844651)
              ·
                refine ⟨36821736378089133401766977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24547824252059422267844651 36821736378089133401766977)
                ·
                  refine ⟨27616302283566850051325233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36821736378089133401766977 27616302283566850051325233)
                  ·
                    refine ⟨20712226712675137538493925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27616302283566850051325233 20712226712675137538493925)
                    ·
                      refine ⟨3883542508626588288467611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20712226712675137538493925 3883542508626588288467611)
                      ·
                        rfl

theorem cell23_7563172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_7563172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563172 prefixEnd_7563172 := by exact prefixLift 7563172
  have htrace : WordTrace (prefixWord ++ tailWord_7563172) baseStart_7563172 baseEnd_7563172 := by
    simpa [prefixWord, tailWord_7563172, baseEnd_7563172] using wordTrace_append hprefix tailTrace_7563172
  have hstable : (prefixWord ++ tailWord_7563172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563172).length < 2 ^ (prefixWord ++ tailWord_7563172).sum := by decide
  have hdescent : baseEnd_7563172 < baseStart_7563172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563205 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_7563205 : Nat := 118140960795 + 7563205 * 2 ^ 59
def prefixEnd_7563205 : Nat := 4983230072969 + 3 ^ 40 * 7563205 * 2
def baseEnd_7563205 : Nat := 3883559453488186659354959

theorem tailTrace_7563205 : CollatzResearch.WordTrace tailWord_7563205 prefixEnd_7563205 3883559453488186659354959 := by
  unfold tailWord_7563205
  simp only [CollatzResearch.WordTrace]
  refine ⟨275852748564807452422211069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183901832376538301614807379 275852748564807452422211069)
  ·
    refine ⟨103444780711802794658329151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275852748564807452422211069 103444780711802794658329151)
    ·
      refine ⟨155167171067704191987493727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103444780711802794658329151 155167171067704191987493727)
      ·
        refine ⟨232750756601556287981240591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155167171067704191987493727 232750756601556287981240591)
        ·
          refine ⟨349126134902334431971860887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232750756601556287981240591 349126134902334431971860887)
          ·
            refine ⟨523689202353501647957791331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349126134902334431971860887 523689202353501647957791331)
            ·
              refine ⟨785533803530252471936686997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523689202353501647957791331 785533803530252471936686997)
              ·
                refine ⟨36821897040480584622032203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 785533803530252471936686997 36821897040480584622032203)
                ·
                  refine ⟨55232845560720876933048305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36821897040480584622032203 55232845560720876933048305)
                  ·
                    refine ⟨41424634170540657699786229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55232845560720876933048305 41424634170540657699786229)
                    ·
                      refine ⟨3883559453488186659354959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41424634170540657699786229 3883559453488186659354959)
                      ·
                        rfl

theorem cell23_7563205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_7563205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563205 prefixEnd_7563205 := by exact prefixLift 7563205
  have htrace : WordTrace (prefixWord ++ tailWord_7563205) baseStart_7563205 baseEnd_7563205 := by
    simpa [prefixWord, tailWord_7563205, baseEnd_7563205] using wordTrace_append hprefix tailTrace_7563205
  have hstable : (prefixWord ++ tailWord_7563205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563205).length < 2 ^ (prefixWord ++ tailWord_7563205).sum := by decide
  have hdescent : baseEnd_7563205 < baseStart_7563205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563269 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_7563269 : Nat := 118140960795 + 7563269 * 2 ^ 59
def prefixEnd_7563269 : Nat := 4983230072969 + 3 ^ 40 * 7563269 * 2
def baseEnd_7563269 : Nat := 3883592316250074408954665

theorem tailTrace_7563269 : CollatzResearch.WordTrace tailWord_7563269 prefixEnd_7563269 3883592316250074408954665 := by
  unfold tailWord_7563269
  simp only [CollatzResearch.WordTrace]
  refine ⟨275855082836575591352540861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183903388557717060901693907 275855082836575591352540861)
  ·
    refine ⟨103445656063715846757202823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275855082836575591352540861 103445656063715846757202823)
    ·
      refine ⟨155168484095573770135804235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103445656063715846757202823 155168484095573770135804235)
      ·
        refine ⟨232752726143360655203706353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155168484095573770135804235 232752726143360655203706353)
        ·
          refine ⟨174564544607520491402779765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232752726143360655203706353 174564544607520491402779765)
          ·
            refine ⟨16365426056955046069010603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174564544607520491402779765 16365426056955046069010603)
            ·
              refine ⟨24548139085432569103515905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16365426056955046069010603 24548139085432569103515905)
              ·
                refine ⟨18411104314074426827636929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24548139085432569103515905 18411104314074426827636929)
                ·
                  refine ⟨13808328235555820120727697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18411104314074426827636929 13808328235555820120727697)
                  ·
                    refine ⟨10356246176666865090545773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13808328235555820120727697 10356246176666865090545773)
                    ·
                      refine ⟨3883592316250074408954665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10356246176666865090545773 3883592316250074408954665)
                      ·
                        rfl

theorem cell23_7563269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_7563269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563269 prefixEnd_7563269 := by exact prefixLift 7563269
  have htrace : WordTrace (prefixWord ++ tailWord_7563269) baseStart_7563269 baseEnd_7563269 := by
    simpa [prefixWord, tailWord_7563269, baseEnd_7563269] using wordTrace_append hprefix tailTrace_7563269
  have hstable : (prefixWord ++ tailWord_7563269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563269).length < 2 ^ (prefixWord ++ tailWord_7563269).sum := by decide
  have hdescent : baseEnd_7563269 < baseStart_7563269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563272 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 6]
def baseStart_7563272 : Nat := 118140960795 + 7563272 * 2 ^ 59
def prefixEnd_7563272 : Nat := 4983230072969 + 3 ^ 40 * 7563272 * 2
def baseEnd_7563272 : Nat := 431510428521337544135239

theorem tailTrace_7563272 : CollatzResearch.WordTrace tailWord_7563272 prefixEnd_7563272 431510428521337544135239 := by
  unfold tailWord_7563272
  simp only [CollatzResearch.WordTrace]
  refine ⟨137927596127782361432450035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183903461503709815243266713 137927596127782361432450035)
  ·
    refine ⟨206891394191673542148675053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137927596127782361432450035 206891394191673542148675053)
    ·
      refine ⟨77584272821877578305753145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206891394191673542148675053 77584272821877578305753145)
      ·
        refine ⟨58188204616408183729314859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77584272821877578305753145 58188204616408183729314859)
        ·
          refine ⟨87282306924612275593972289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58188204616408183729314859 87282306924612275593972289)
          ·
            refine ⟨65461730193459206695479217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87282306924612275593972289 65461730193459206695479217)
            ·
              refine ⟨49096297645094405021609413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65461730193459206695479217 49096297645094405021609413)
              ·
                refine ⟨9205555808455200941551765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49096297645094405021609413 9205555808455200941551765)
                ·
                  refine ⟨431510428521337544135239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9205555808455200941551765 431510428521337544135239)
                  ·
                    rfl

theorem cell23_7563272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 6].length) (baseStart_7563272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563272 prefixEnd_7563272 := by exact prefixLift 7563272
  have htrace : WordTrace (prefixWord ++ tailWord_7563272) baseStart_7563272 baseEnd_7563272 := by
    simpa [prefixWord, tailWord_7563272, baseEnd_7563272] using wordTrace_append hprefix tailTrace_7563272
  have hstable : (prefixWord ++ tailWord_7563272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563272).length < 2 ^ (prefixWord ++ tailWord_7563272).sum := by decide
  have hdescent : baseEnd_7563272 < baseStart_7563272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563299 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 3]
def baseStart_7563299 : Nat := 118140960795 + 7563299 * 2 ^ 59
def prefixEnd_7563299 : Nat := 4983230072969 + 3 ^ 40 * 7563299 * 2
def baseEnd_7563299 : Nat := 3883607720669709291579527

theorem tailTrace_7563299 : CollatzResearch.WordTrace tailWord_7563299 prefixEnd_7563299 3883607720669709291579527 := by
  unfold tailWord_7563299
  simp only [CollatzResearch.WordTrace]
  refine ⟨275856177026466906476132951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183904118017644604317421967 275856177026466906476132951)
  ·
    refine ⟨413784265539700359714199427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275856177026466906476132951 413784265539700359714199427)
    ·
      refine ⟨620676398309550539571299141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413784265539700359714199427 620676398309550539571299141)
      ·
        refine ⟨116376824683040726169618589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 620676398309550539571299141 116376824683040726169618589)
        ·
          refine ⟨43641309256140272313606971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116376824683040726169618589 43641309256140272313606971)
          ·
            refine ⟨65461963884210408470410457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43641309256140272313606971 65461963884210408470410457)
            ·
              refine ⟨49096472913157806352807843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65461963884210408470410457 49096472913157806352807843)
              ·
                refine ⟨73644709369736709529211765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49096472913157806352807843 73644709369736709529211765)
                ·
                  refine ⟨6904191503412816518363603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73644709369736709529211765 6904191503412816518363603)
                  ·
                    refine ⟨10356287255119224777545405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6904191503412816518363603 10356287255119224777545405)
                    ·
                      refine ⟨3883607720669709291579527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10356287255119224777545405 3883607720669709291579527)
                      ·
                        rfl

theorem cell23_7563299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_7563299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563299 prefixEnd_7563299 := by exact prefixLift 7563299
  have htrace : WordTrace (prefixWord ++ tailWord_7563299) baseStart_7563299 baseEnd_7563299 := by
    simpa [prefixWord, tailWord_7563299, baseEnd_7563299] using wordTrace_append hprefix tailTrace_7563299
  have hstable : (prefixWord ++ tailWord_7563299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563299).length < 2 ^ (prefixWord ++ tailWord_7563299).sum := by decide
  have hdescent : baseEnd_7563299 < baseStart_7563299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563303 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_7563303 : Nat := 118140960795 + 7563303 * 2 ^ 59
def prefixEnd_7563303 : Nat := 4983230072969 + 3 ^ 40 * 7563303 * 2
def baseEnd_7563303 : Nat := 3883609774592327275929509

theorem tailTrace_7563303 : CollatzResearch.WordTrace tailWord_7563303 prefixEnd_7563303 3883609774592327275929509 := by
  unfold tailWord_7563303
  simp only [CollatzResearch.WordTrace]
  refine ⟨275856322918452415159278563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183904215278968276772852375 275856322918452415159278563)
  ·
    refine ⟨413784484377678622738917845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275856322918452415159278563 413784484377678622738917845)
    ·
      refine ⟨9698073852601842720443387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 413784484377678622738917845 9698073852601842720443387)
      ·
        refine ⟨14547110778902764080665081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698073852601842720443387 14547110778902764080665081)
        ·
          refine ⟨10910333084177073060498811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14547110778902764080665081 10910333084177073060498811)
          ·
            refine ⟨16365499626265609590748217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10910333084177073060498811 16365499626265609590748217)
            ·
              refine ⟨12274124719699207193061163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16365499626265609590748217 12274124719699207193061163)
              ·
                refine ⟨18411187079548810789591745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12274124719699207193061163 18411187079548810789591745)
                ·
                  refine ⟨13808390309661608092193809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18411187079548810789591745 13808390309661608092193809)
                  ·
                    refine ⟨10356292732246206069145357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13808390309661608092193809 10356292732246206069145357)
                    ·
                      refine ⟨3883609774592327275929509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10356292732246206069145357 3883609774592327275929509)
                      ·
                        rfl

theorem cell23_7563303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_7563303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563303 prefixEnd_7563303 := by exact prefixLift 7563303
  have htrace : WordTrace (prefixWord ++ tailWord_7563303) baseStart_7563303 baseEnd_7563303 := by
    simpa [prefixWord, tailWord_7563303, baseEnd_7563303] using wordTrace_append hprefix tailTrace_7563303
  have hstable : (prefixWord ++ tailWord_7563303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563303).length < 2 ^ (prefixWord ++ tailWord_7563303).sum := by decide
  have hdescent : baseEnd_7563303 < baseStart_7563303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563349 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_7563349 : Nat := 118140960795 + 7563349 * 2 ^ 59
def prefixEnd_7563349 : Nat := 4983230072969 + 3 ^ 40 * 7563349 * 2
def baseEnd_7563349 : Nat := 1294544464900811365318099

theorem tailTrace_7563349 : CollatzResearch.WordTrace tailWord_7563349 prefixEnd_7563349 1294544464900811365318099 := by
  unfold tailWord_7563349
  simp only [CollatzResearch.WordTrace]
  refine ⟨275858000676285765015453101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183905333784190510010302067 275858000676285765015453101)
  ·
    refine ⟨103446750253607161880794913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275858000676285765015453101 103446750253607161880794913)
    ·
      refine ⟨77585062690205371410596185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103446750253607161880794913 77585062690205371410596185)
      ·
        refine ⟨58188797017654028557947139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77585062690205371410596185 58188797017654028557947139)
        ·
          refine ⟨87283195526481042836920709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58188797017654028557947139 87283195526481042836920709)
          ·
            refine ⟨16365599161215195531922633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87283195526481042836920709 16365599161215195531922633)
            ·
              refine ⟨12274199370911396648941975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16365599161215195531922633 12274199370911396648941975)
              ·
                refine ⟨18411299056367094973412963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12274199370911396648941975 18411299056367094973412963)
                ·
                  refine ⟨27616948584550642460119445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18411299056367094973412963 27616948584550642460119445)
                  ·
                    refine ⟨1294544464900811365318099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27616948584550642460119445 1294544464900811365318099)
                    ·
                      rfl

theorem cell23_7563349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_7563349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563349 prefixEnd_7563349 := by exact prefixLift 7563349
  have htrace : WordTrace (prefixWord ++ tailWord_7563349) baseStart_7563349 baseEnd_7563349 := by
    simpa [prefixWord, tailWord_7563349, baseEnd_7563349] using wordTrace_append hprefix tailTrace_7563349
  have hstable : (prefixWord ++ tailWord_7563349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563349).length < 2 ^ (prefixWord ++ tailWord_7563349).sum := by decide
  have hdescent : baseEnd_7563349 < baseStart_7563349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563350 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_7563350 : Nat := 118140960795 + 7563350 * 2 ^ 59
def prefixEnd_7563350 : Nat := 4983230072969 + 3 ^ 40 * 7563350 * 2
def baseEnd_7563350 : Nat := 3883633908183088592041793

theorem tailTrace_7563350 : CollatzResearch.WordTrace tailWord_7563350 prefixEnd_7563350 3883633908183088592041793 := by
  unfold tailWord_7563350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241127321830133886639969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183905358099521428124159669 17241127321830133886639969)
  ·
    refine ⟨12930845491372600414979977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17241127321830133886639969 12930845491372600414979977)
    ·
      refine ⟨9698134118529450311234983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12930845491372600414979977 9698134118529450311234983)
      ·
        refine ⟨14547201177794175466852475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698134118529450311234983 14547201177794175466852475)
        ·
          refine ⟨21820801766691263200278713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14547201177794175466852475 21820801766691263200278713)
          ·
            refine ⟨16365601325018447400209035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21820801766691263200278713 16365601325018447400209035)
            ·
              refine ⟨24548401987527671100313553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16365601325018447400209035 24548401987527671100313553)
              ·
                refine ⟨18411301490645753325235165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24548401987527671100313553 18411301490645753325235165)
                ·
                  refine ⟨6904238058992157496963187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18411301490645753325235165 6904238058992157496963187)
                  ·
                    refine ⟨10356357088488236245444781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6904238058992157496963187 10356357088488236245444781)
                    ·
                      refine ⟨3883633908183088592041793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10356357088488236245444781 3883633908183088592041793)
                      ·
                        rfl

theorem cell23_7563350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_7563350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563350 prefixEnd_7563350 := by exact prefixLift 7563350
  have htrace : WordTrace (prefixWord ++ tailWord_7563350) baseStart_7563350 baseEnd_7563350 := by
    simpa [prefixWord, tailWord_7563350, baseEnd_7563350] using wordTrace_append hprefix tailTrace_7563350
  have hstable : (prefixWord ++ tailWord_7563350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563350).length < 2 ^ (prefixWord ++ tailWord_7563350).sum := by decide
  have hdescent : baseEnd_7563350 < baseStart_7563350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563370 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_7563370 : Nat := 118140960795 + 7563370 * 2 ^ 59
def prefixEnd_7563370 : Nat := 4983230072969 + 3 ^ 40 * 7563370 * 2
def baseEnd_7563370 : Nat := 1294548059265392837930567

theorem tailTrace_7563370 : CollatzResearch.WordTrace tailWord_7563370 prefixEnd_7563370 1294548059265392837930567 := by
  unfold tailWord_7563370
  simp only [CollatzResearch.WordTrace]
  refine ⟨68964691652302421400491891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183905844406139790401311709 68964691652302421400491891)
  ·
    refine ⟨103447037478453632100737837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68964691652302421400491891 103447037478453632100737837)
    ·
      refine ⟨38792639054420112037776689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103447037478453632100737837 38792639054420112037776689)
      ·
        refine ⟨29094479290815084028332517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38792639054420112037776689 29094479290815084028332517)
        ·
          refine ⟨5455214867027828255312347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29094479290815084028332517 5455214867027828255312347)
          ·
            refine ⟨8182822300541742382968521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455214867027828255312347 8182822300541742382968521)
            ·
              refine ⟨6137116725406306787226391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8182822300541742382968521 6137116725406306787226391)
              ·
                refine ⟨9205675088109460180839587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137116725406306787226391 9205675088109460180839587)
                ·
                  refine ⟨13808512632164190271259381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205675088109460180839587 13808512632164190271259381)
                  ·
                    refine ⟨1294548059265392837930567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13808512632164190271259381 1294548059265392837930567)
                    ·
                      rfl

theorem cell23_7563370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_7563370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563370 prefixEnd_7563370 := by exact prefixLift 7563370
  have htrace : WordTrace (prefixWord ++ tailWord_7563370) baseStart_7563370 baseEnd_7563370 := by
    simpa [prefixWord, tailWord_7563370, baseEnd_7563370] using wordTrace_append hprefix tailTrace_7563370
  have hstable : (prefixWord ++ tailWord_7563370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563370).length < 2 ^ (prefixWord ++ tailWord_7563370).sum := by decide
  have hdescent : baseEnd_7563370 < baseStart_7563370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563376 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 3]
def baseStart_7563376 : Nat := 118140960795 + 7563376 * 2 ^ 59
def prefixEnd_7563376 : Nat := 4983230072969 + 3 ^ 40 * 7563376 * 2
def baseEnd_7563376 : Nat := 3883647258680105490316673

theorem tailTrace_7563376 : CollatzResearch.WordTrace tailWord_7563376 prefixEnd_7563376 3883647258680105490316673 := by
  unfold tailWord_7563376
  simp only [CollatzResearch.WordTrace]
  refine ⟨137929492723593974313342991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183905990298125299084457321 137929492723593974313342991)
  ·
    refine ⟨206894239085390961470014487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137929492723593974313342991 206894239085390961470014487)
    ·
      refine ⟨310341358628086442205021731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206894239085390961470014487 310341358628086442205021731)
      ·
        refine ⟨465512037942129663307532597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310341358628086442205021731 465512037942129663307532597)
        ·
          refine ⟨43641753557074655935081181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 465512037942129663307532597 43641753557074655935081181)
          ·
            refine ⟨16365657583902995975655443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43641753557074655935081181 16365657583902995975655443)
            ·
              refine ⟨24548486375854493963483165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16365657583902995975655443 24548486375854493963483165)
              ·
                refine ⟨9205682390945435236306187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24548486375854493963483165 9205682390945435236306187)
                ·
                  refine ⟨13808523586418152854459281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205682390945435236306187 13808523586418152854459281)
                  ·
                    refine ⟨10356392689813614640844461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13808523586418152854459281 10356392689813614640844461)
                    ·
                      refine ⟨3883647258680105490316673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10356392689813614640844461 3883647258680105490316673)
                      ·
                        rfl

theorem cell23_7563376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 3].length) (baseStart_7563376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563376 prefixEnd_7563376 := by exact prefixLift 7563376
  have htrace : WordTrace (prefixWord ++ tailWord_7563376) baseStart_7563376 baseEnd_7563376 := by
    simpa [prefixWord, tailWord_7563376, baseEnd_7563376] using wordTrace_append hprefix tailTrace_7563376
  have hstable : (prefixWord ++ tailWord_7563376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563376).length < 2 ^ (prefixWord ++ tailWord_7563376).sum := by decide
  have hdescent : baseEnd_7563376 < baseStart_7563376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563449 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 3]
def baseStart_7563449 : Nat := 118140960795 + 7563449 * 2 ^ 59
def prefixEnd_7563449 : Nat := 4983230072969 + 3 ^ 40 * 7563449 * 2
def baseEnd_7563449 : Nat := 3883684742767883704703837

theorem tailTrace_7563449 : CollatzResearch.WordTrace tailWord_7563449 prefixEnd_7563449 3883684742767883704703837 := by
  unfold tailWord_7563449
  simp only [CollatzResearch.WordTrace]
  refine ⟨275861647975923482094093401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183907765317282321396062267 275861647975923482094093401)
  ·
    refine ⟨206896235981942611570570051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275861647975923482094093401 206896235981942611570570051)
    ·
      refine ⟨310344353972913917355855077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206896235981942611570570051 310344353972913917355855077)
      ·
        refine ⟨58189566369921359504222827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310344353972913917355855077 58189566369921359504222827)
        ·
          refine ⟨87284349554882039256334241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58189566369921359504222827 87284349554882039256334241)
          ·
            refine ⟨65463262166161529442250681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87284349554882039256334241 65463262166161529442250681)
            ·
              refine ⟨49097446624621147081688011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65463262166161529442250681 49097446624621147081688011)
              ·
                refine ⟨73646169936931720622532017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49097446624621147081688011 73646169936931720622532017)
                ·
                  refine ⟨55234627452698790466899013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73646169936931720622532017 55234627452698790466899013)
                  ·
                    refine ⟨10356492647381023212543565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55234627452698790466899013 10356492647381023212543565)
                    ·
                      refine ⟨3883684742767883704703837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10356492647381023212543565 3883684742767883704703837)
                      ·
                        rfl

theorem cell23_7563449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_7563449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563449 prefixEnd_7563449 := by exact prefixLift 7563449
  have htrace : WordTrace (prefixWord ++ tailWord_7563449) baseStart_7563449 baseEnd_7563449 := by
    simpa [prefixWord, tailWord_7563449, baseEnd_7563449] using wordTrace_append hprefix tailTrace_7563449
  have hstable : (prefixWord ++ tailWord_7563449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563449).length < 2 ^ (prefixWord ++ tailWord_7563449).sum := by decide
  have hdescent : baseEnd_7563449 < baseStart_7563449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563472 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_7563472 : Nat := 118140960795 + 7563472 * 2 ^ 59
def prefixEnd_7563472 : Nat := 4983230072969 + 3 ^ 40 * 7563472 * 2
def baseEnd_7563472 : Nat := 3883696552822937114716231

theorem tailTrace_7563472 : CollatzResearch.WordTrace tailWord_7563472 prefixEnd_7563472 3883696552822937114716231 := by
  unfold tailWord_7563472
  simp only [CollatzResearch.WordTrace]
  refine ⟨137931243427420078511090335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183908324569893438014787113 137931243427420078511090335)
  ·
    refine ⟨206896865141130117766635503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137931243427420078511090335 206896865141130117766635503)
    ·
      refine ⟨310345297711695176649953255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206896865141130117766635503 310345297711695176649953255)
      ·
        refine ⟨465517946567542764974929883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310345297711695176649953255 465517946567542764974929883)
        ·
          refine ⟨698276919851314147462394825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465517946567542764974929883 698276919851314147462394825)
          ·
            refine ⟨523707689888485610596796119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698276919851314147462394825 523707689888485610596796119)
            ·
              refine ⟨785561534832728415895194179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523707689888485610596796119 785561534832728415895194179)
              ·
                refine ⟨1178342302249092623842791269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785561534832728415895194179 1178342302249092623842791269)
                ·
                  refine ⟨220939181671704866970523363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178342302249092623842791269 220939181671704866970523363)
                  ·
                    refine ⟨331408772507557300455785045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220939181671704866970523363 331408772507557300455785045)
                    ·
                      refine ⟨3883696552822937114716231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 331408772507557300455785045 3883696552822937114716231)
                      ·
                        rfl

theorem cell23_7563472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_7563472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563472 prefixEnd_7563472 := by exact prefixLift 7563472
  have htrace : WordTrace (prefixWord ++ tailWord_7563472) baseStart_7563472 baseEnd_7563472 := by
    simpa [prefixWord, tailWord_7563472, baseEnd_7563472] using wordTrace_append hprefix tailTrace_7563472
  have hstable : (prefixWord ++ tailWord_7563472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563472).length < 2 ^ (prefixWord ++ tailWord_7563472).sum := by decide
  have hdescent : baseEnd_7563472 < baseStart_7563472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563479 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_7563479 : Nat := 118140960795 + 7563479 * 2 ^ 59
def prefixEnd_7563479 : Nat := 4983230072969 + 3 ^ 40 * 7563479 * 2
def baseEnd_7563479 : Nat := 3883700147187518587328699

theorem tailTrace_7563479 : CollatzResearch.WordTrace tailWord_7563479 prefixEnd_7563479 3883700147187518587328699 := by
  unfold tailWord_7563479
  simp only [CollatzResearch.WordTrace]
  refine ⟨275862742165814797217685491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183908494777209864811790327 275862742165814797217685491)
  ·
    refine ⟨413794113248722195826528237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275862742165814797217685491 413794113248722195826528237)
    ·
      refine ⟨155172792468270823434948089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413794113248722195826528237 155172792468270823434948089)
      ·
        refine ⟨116379594351203117576211067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155172792468270823434948089 116379594351203117576211067)
        ·
          refine ⟨174569391526804676364316601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116379594351203117576211067 174569391526804676364316601)
          ·
            refine ⟨130927043645103507273237451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174569391526804676364316601 130927043645103507273237451)
            ·
              refine ⟨196390565467655260909856177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130927043645103507273237451 196390565467655260909856177)
              ·
                refine ⟨147292924100741445682392133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196390565467655260909856177 147292924100741445682392133)
                ·
                  refine ⟨27617423268889021065448525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147292924100741445682392133 27617423268889021065448525)
                  ·
                    refine ⟨10356533725833382899543197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27617423268889021065448525 10356533725833382899543197)
                    ·
                      refine ⟨3883700147187518587328699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10356533725833382899543197 3883700147187518587328699)
                      ·
                        rfl

theorem cell23_7563479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_7563479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563479 prefixEnd_7563479 := by exact prefixLift 7563479
  have htrace : WordTrace (prefixWord ++ tailWord_7563479) baseStart_7563479 baseEnd_7563479 := by
    simpa [prefixWord, tailWord_7563479, baseEnd_7563479] using wordTrace_append hprefix tailTrace_7563479
  have hstable : (prefixWord ++ tailWord_7563479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563479).length < 2 ^ (prefixWord ++ tailWord_7563479).sum := by decide
  have hdescent : baseEnd_7563479 < baseStart_7563479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563484 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7563484 : Nat := 118140960795 + 7563484 * 2 ^ 59
def prefixEnd_7563484 : Nat := 4983230072969 + 3 ^ 40 * 7563484 * 2
def baseEnd_7563484 : Nat := 3883702714590791067766177

theorem tailTrace_7563484 : CollatzResearch.WordTrace tailWord_7563484 prefixEnd_7563484 3883702714590791067766177 := by
  unfold tailWord_7563484
  simp only [CollatzResearch.WordTrace]
  refine ⟨137931462265398341535808753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183908616353864455381078337 137931462265398341535808753)
  ·
    refine ⟨103448596699048756151856565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137931462265398341535808753 103448596699048756151856565)
    ·
      refine ⟨9698305940535820889236553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103448596699048756151856565 9698305940535820889236553)
      ·
        refine ⟨7273729455401865666927415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9698305940535820889236553 7273729455401865666927415)
        ·
          refine ⟨10910594183102798500391123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7273729455401865666927415 10910594183102798500391123)
          ·
            refine ⟨16365891274654197750586685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10910594183102798500391123 16365891274654197750586685)
            ·
              refine ⟨6137209227995324156470007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16365891274654197750586685 6137209227995324156470007)
              ·
                refine ⟨9205813841992986234705011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137209227995324156470007 9205813841992986234705011)
                ·
                  refine ⟨13808720762989479352057517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205813841992986234705011 13808720762989479352057517)
                  ·
                    refine ⟨5178270286121054757021569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13808720762989479352057517 5178270286121054757021569)
                    ·
                      refine ⟨3883702714590791067766177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5178270286121054757021569 3883702714590791067766177)
                      ·
                        rfl

theorem cell23_7563484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7563484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563484 prefixEnd_7563484 := by exact prefixLift 7563484
  have htrace : WordTrace (prefixWord ++ tailWord_7563484) baseStart_7563484 baseEnd_7563484 := by
    simpa [prefixWord, tailWord_7563484, baseEnd_7563484] using wordTrace_append hprefix tailTrace_7563484
  have hstable : (prefixWord ++ tailWord_7563484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563484).length < 2 ^ (prefixWord ++ tailWord_7563484).sum := by decide
  have hdescent : baseEnd_7563484 < baseStart_7563484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563499 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 2, 5]
def baseStart_7563499 : Nat := 118140960795 + 7563499 * 2 ^ 59
def prefixEnd_7563499 : Nat := 4983230072969 + 3 ^ 40 * 7563499 * 2
def baseEnd_7563499 : Nat := 1294570138933536169692869

theorem tailTrace_7563499 : CollatzResearch.WordTrace tailWord_7563499 prefixEnd_7563499 1294570138933536169692869 := by
  unfold tailWord_7563499
  simp only [CollatzResearch.WordTrace]
  refine ⟨275863471625742340633413551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183908981083828227088942367 275863471625742340633413551)
  ·
    refine ⟨413795207438613510950120327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275863471625742340633413551 413795207438613510950120327)
    ·
      refine ⟨620692811157920266425180491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413795207438613510950120327 620692811157920266425180491)
      ·
        refine ⟨931039216736880399637770737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620692811157920266425180491 931039216736880399637770737)
        ·
          refine ⟨698279412552660299728328053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931039216736880399637770737 698279412552660299728328053)
          ·
            refine ⟨65463694926811903099530755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 698279412552660299728328053 65463694926811903099530755)
            ·
              refine ⟨98195542390217854649296133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65463694926811903099530755 98195542390217854649296133)
              ·
                refine ⟨18411664198165847746743025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98195542390217854649296133 18411664198165847746743025)
                ·
                  refine ⟨13808748148624385810057269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18411664198165847746743025 13808748148624385810057269)
                  ·
                    refine ⟨1294570138933536169692869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13808748148624385810057269 1294570138933536169692869)
                    ·
                      rfl

theorem cell23_7563499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 5].length) (baseStart_7563499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563499 prefixEnd_7563499 := by exact prefixLift 7563499
  have htrace : WordTrace (prefixWord ++ tailWord_7563499) baseStart_7563499 baseEnd_7563499 := by
    simpa [prefixWord, tailWord_7563499, baseEnd_7563499] using wordTrace_append hprefix tailTrace_7563499
  have hstable : (prefixWord ++ tailWord_7563499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563499).length < 2 ^ (prefixWord ++ tailWord_7563499).sum := by decide
  have hdescent : baseEnd_7563499 < baseStart_7563499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563503 : List Nat := [1, 1, 2, 1, 6, 1, 4, 2, 5]
def baseStart_7563503 : Nat := 118140960795 + 7563503 * 2 ^ 59
def prefixEnd_7563503 : Nat := 4983230072969 + 3 ^ 40 * 7563503 * 2
def baseEnd_7563503 : Nat := 431523607858136277047621

theorem tailTrace_7563503 : CollatzResearch.WordTrace tailWord_7563503 prefixEnd_7563503 431523607858136277047621 := by
  unfold tailWord_7563503
  simp only [CollatzResearch.WordTrace]
  refine ⟨275863617517727849316559163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183909078345151899544372775 275863617517727849316559163)
  ·
    refine ⟨413795426276591773974838745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275863617517727849316559163 413795426276591773974838745)
    ·
      refine ⟨310346569707443830481129059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413795426276591773974838745 310346569707443830481129059)
      ·
        refine ⟨465519854561165745721693589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310346569707443830481129059 465519854561165745721693589)
        ·
          refine ⟨21821243182554644330704387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 465519854561165745721693589 21821243182554644330704387)
          ·
            refine ⟨32731864773831966496056581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21821243182554644330704387 32731864773831966496056581)
            ·
              refine ⟨6137224645093493718010609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32731864773831966496056581 6137224645093493718010609)
              ·
                refine ⟨4602918483820120288507957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6137224645093493718010609 4602918483820120288507957)
                ·
                  refine ⟨431523607858136277047621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4602918483820120288507957 431523607858136277047621)
                  ·
                    rfl

theorem cell23_7563503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 5].length) (baseStart_7563503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563503 prefixEnd_7563503 := by exact prefixLift 7563503
  have htrace : WordTrace (prefixWord ++ tailWord_7563503) baseStart_7563503 baseEnd_7563503 := by
    simpa [prefixWord, tailWord_7563503, baseEnd_7563503] using wordTrace_append hprefix tailTrace_7563503
  have hstable : (prefixWord ++ tailWord_7563503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563503).length < 2 ^ (prefixWord ++ tailWord_7563503).sum := by decide
  have hdescent : baseEnd_7563503 < baseStart_7563503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563519 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_7563519 : Nat := 118140960795 + 7563519 * 2 ^ 59
def prefixEnd_7563519 : Nat := 4983230072969 + 3 ^ 40 * 7563519 * 2
def baseEnd_7563519 : Nat := 3883720686413698430828515

theorem tailTrace_7563519 : CollatzResearch.WordTrace tailWord_7563519 prefixEnd_7563519 3883720686413698430828515 := by
  unfold tailWord_7563519
  simp only [CollatzResearch.WordTrace]
  refine ⟨275864201085669884049141611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183909467390446589366094407 275864201085669884049141611)
  ·
    refine ⟨413796301628504826073712417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275864201085669884049141611 413796301628504826073712417)
    ·
      refine ⟨310347226221378619555284313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413796301628504826073712417 310347226221378619555284313)
      ·
        refine ⟨232760419666033964666463235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310347226221378619555284313 232760419666033964666463235)
        ·
          refine ⟨349140629499050946999694853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232760419666033964666463235 349140629499050946999694853)
          ·
            refine ⟨65463868031072052562442785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349140629499050946999694853 65463868031072052562442785)
            ·
              refine ⟨49097901023304039421832089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65463868031072052562442785 49097901023304039421832089)
              ·
                refine ⟨36823425767478029566374067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49097901023304039421832089 36823425767478029566374067)
                ·
                  refine ⟨55235138651217044349561101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36823425767478029566374067 55235138651217044349561101)
                  ·
                    refine ⟨20713176994206391631085413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55235138651217044349561101 20713176994206391631085413)
                    ·
                      refine ⟨3883720686413698430828515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20713176994206391631085413 3883720686413698430828515)
                      ·
                        rfl

theorem cell23_7563519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_7563519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563519 prefixEnd_7563519 := by exact prefixLift 7563519
  have htrace : WordTrace (prefixWord ++ tailWord_7563519) baseStart_7563519 baseEnd_7563519 := by
    simpa [prefixWord, tailWord_7563519, baseEnd_7563519] using wordTrace_append hprefix tailTrace_7563519
  have hstable : (prefixWord ++ tailWord_7563519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563519).length < 2 ^ (prefixWord ++ tailWord_7563519).sum := by decide
  have hdescent : baseEnd_7563519 < baseStart_7563519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563643 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 4]
def baseStart_7563643 : Nat := 118140960795 + 7563643 * 2 ^ 59
def prefixEnd_7563643 : Nat := 4983230072969 + 3 ^ 40 * 7563643 * 2
def baseEnd_7563643 : Nat := 3883784358014855945677945

theorem tailTrace_7563643 : CollatzResearch.WordTrace tailWord_7563643 prefixEnd_7563643 3883784358014855945677945 := by
  unfold tailWord_7563643
  simp only [CollatzResearch.WordTrace]
  refine ⟨275868723737220653226655583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183912482491480435484437055 275868723737220653226655583)
  ·
    refine ⟨413803085605830979839983375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275868723737220653226655583 413803085605830979839983375)
    ·
      refine ⟨620704628408746469759975063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413803085605830979839983375 620704628408746469759975063)
      ·
        refine ⟨931056942613119704639962595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620704628408746469759975063 931056942613119704639962595)
        ·
          refine ⟨1396585413919679556959943893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931056942613119704639962595 1396585413919679556959943893)
          ·
            refine ⟨32732470638742489616248685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1396585413919679556959943893 32732470638742489616248685)
            ·
              refine ⟨12274676489528433606093257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32732470638742489616248685 12274676489528433606093257)
              ·
                refine ⟨9206007367146325204569943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12274676489528433606093257 9206007367146325204569943)
                ·
                  refine ⟨13809011050719487806854915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9206007367146325204569943 13809011050719487806854915)
                  ·
                    refine ⟨20713516576079231710282373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13809011050719487806854915 20713516576079231710282373)
                    ·
                      refine ⟨3883784358014855945677945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20713516576079231710282373 3883784358014855945677945)
                      ·
                        rfl

theorem cell23_7563643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 4].length) (baseStart_7563643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563643 prefixEnd_7563643 := by exact prefixLift 7563643
  have htrace : WordTrace (prefixWord ++ tailWord_7563643) baseStart_7563643 baseEnd_7563643 := by
    simpa [prefixWord, tailWord_7563643, baseEnd_7563643] using wordTrace_append hprefix tailTrace_7563643
  have hstable : (prefixWord ++ tailWord_7563643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563643).length < 2 ^ (prefixWord ++ tailWord_7563643).sum := by decide
  have hdescent : baseEnd_7563643 < baseStart_7563643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563660 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 1, 1, 4]
def baseStart_7563660 : Nat := 118140960795 + 7563660 * 2 ^ 59
def prefixEnd_7563660 : Nat := 4983230072969 + 3 ^ 40 * 7563660 * 2
def baseEnd_7563660 : Nat := 3883793087185982379165367

theorem tailTrace_7563660 : CollatzResearch.WordTrace tailWord_7563660 prefixEnd_7563660 3883793087185982379165367 := by
  unfold tailWord_7563660
  simp only [CollatzResearch.WordTrace]
  refine ⟨137934671889079532565012217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183912895852106043420016289 137934671889079532565012217)
  ·
    refine ⟨103451003916809649423759163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137934671889079532565012217 103451003916809649423759163)
    ·
      refine ⟨155176505875214474135638745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103451003916809649423759163 155176505875214474135638745)
      ·
        refine ⟨116382379406410855601729059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155176505875214474135638745 116382379406410855601729059)
        ·
          refine ⟨174573569109616283402593589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116382379406410855601729059 174573569109616283402593589)
          ·
            refine ⟨16366272104026526568993149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174573569109616283402593589 16366272104026526568993149)
            ·
              refine ⟨6137352039009947463372431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16366272104026526568993149 6137352039009947463372431)
              ·
                refine ⟨9206028058514921195058647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137352039009947463372431 9206028058514921195058647)
                ·
                  refine ⟨13809042087772381792587971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9206028058514921195058647 13809042087772381792587971)
                  ·
                    refine ⟨20713563131658572688881957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13809042087772381792587971 20713563131658572688881957)
                    ·
                      refine ⟨3883793087185982379165367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20713563131658572688881957 3883793087185982379165367)
                      ·
                        rfl

theorem cell23_7563660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_7563660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563660 prefixEnd_7563660 := by exact prefixLift 7563660
  have htrace : WordTrace (prefixWord ++ tailWord_7563660) baseStart_7563660 baseEnd_7563660 := by
    simpa [prefixWord, tailWord_7563660, baseEnd_7563660] using wordTrace_append hprefix tailTrace_7563660
  have hstable : (prefixWord ++ tailWord_7563660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563660).length < 2 ^ (prefixWord ++ tailWord_7563660).sum := by decide
  have hdescent : baseEnd_7563660 < baseStart_7563660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563736 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_7563736 : Nat := 118140960795 + 7563736 * 2 ^ 59
def prefixEnd_7563736 : Nat := 4983230072969 + 3 ^ 40 * 7563736 * 2
def baseEnd_7563736 : Nat := 3883832111715724081815017

theorem tailTrace_7563736 : CollatzResearch.WordTrace tailWord_7563736 prefixEnd_7563736 3883832111715724081815017 := by
  unfold tailWord_7563736
  simp only [CollatzResearch.WordTrace]
  refine ⟨137936057862941865054895531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183914743817255820073194041 137936057862941865054895531)
  ·
    refine ⟨206904086794412797582343297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137936057862941865054895531 206904086794412797582343297)
    ·
      refine ⟨155178065095809598186757473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206904086794412797582343297 155178065095809598186757473)
      ·
        refine ⟨116383548821857198640068105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155178065095809598186757473 116383548821857198640068105)
        ·
          refine ⟨87287661616392898980051079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116383548821857198640068105 87287661616392898980051079)
          ·
            refine ⟨130931492424589348470076619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87287661616392898980051079 130931492424589348470076619)
            ·
              refine ⟨196397238636884022705114929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130931492424589348470076619 196397238636884022705114929)
              ·
                refine ⟨147297928977663017028836197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196397238636884022705114929 147297928977663017028836197)
                ·
                  refine ⟨27618361683311815692906787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147297928977663017028836197 27618361683311815692906787)
                  ·
                    refine ⟨41427542524967723539360181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27618361683311815692906787 41427542524967723539360181)
                    ·
                      refine ⟨3883832111715724081815017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41427542524967723539360181 3883832111715724081815017)
                      ·
                        rfl

theorem cell23_7563736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_7563736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563736 prefixEnd_7563736 := by exact prefixLift 7563736
  have htrace : WordTrace (prefixWord ++ tailWord_7563736) baseStart_7563736 baseEnd_7563736 := by
    simpa [prefixWord, tailWord_7563736, baseEnd_7563736] using wordTrace_append hprefix tailTrace_7563736
  have hstable : (prefixWord ++ tailWord_7563736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563736).length < 2 ^ (prefixWord ++ tailWord_7563736).sum := by decide
  have hdescent : baseEnd_7563736 < baseStart_7563736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563756 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 7]
def baseStart_7563756 : Nat := 118140960795 + 7563756 * 2 ^ 59
def prefixEnd_7563756 : Nat := 4983230072969 + 3 ^ 40 * 7563756 * 2
def baseEnd_7563756 : Nat := 431538042369868222618325

theorem tailTrace_7563756 : CollatzResearch.WordTrace tailWord_7563756 prefixEnd_7563756 431538042369868222618325 := by
  unfold tailWord_7563756
  simp only [CollatzResearch.WordTrace]
  refine ⟨137936422592905636762759561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183915230123874182350346081 137936422592905636762759561)
  ·
    refine ⟨103452316944679227572069671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137936422592905636762759561 103452316944679227572069671)
    ·
      refine ⟨155178475417018841358104507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103452316944679227572069671 155178475417018841358104507)
      ·
        refine ⟨232767713125528262037156761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155178475417018841358104507 232767713125528262037156761)
        ·
          refine ⟨174575784844146196527867571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232767713125528262037156761 174575784844146196527867571)
          ·
            refine ⟨261863677266219294791801357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174575784844146196527867571 261863677266219294791801357)
            ·
              refine ⟨98198878974832235546925509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261863677266219294791801357 98198878974832235546925509)
              ·
                refine ⟨18412289807781044165048533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98198878974832235546925509 18412289807781044165048533)
                ·
                  refine ⟨431538042369868222618325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18412289807781044165048533 431538042369868222618325)
                  ·
                    rfl

theorem cell23_7563756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_7563756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563756 prefixEnd_7563756 := by exact prefixLift 7563756
  have htrace : WordTrace (prefixWord ++ tailWord_7563756) baseStart_7563756 baseEnd_7563756 := by
    simpa [prefixWord, tailWord_7563756, baseEnd_7563756] using wordTrace_append hprefix tailTrace_7563756
  have hstable : (prefixWord ++ tailWord_7563756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563756).length < 2 ^ (prefixWord ++ tailWord_7563756).sum := by decide
  have hdescent : baseEnd_7563756 < baseStart_7563756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563790 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_7563790 : Nat := 118140960795 + 7563790 * 2 ^ 59
def prefixEnd_7563790 : Nat := 4983230072969 + 3 ^ 40 * 7563790 * 2
def baseEnd_7563790 : Nat := 431539982185674096726641

theorem tailTrace_7563790 : CollatzResearch.WordTrace tailWord_7563790 prefixEnd_7563790 431539982185674096726641 := by
  unfold tailWord_7563790
  simp only [CollatzResearch.WordTrace]
  refine ⟨34484260658461012166532103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183916056845125398221504549 34484260658461012166532103)
  ·
    refine ⟨51726390987691518249798155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34484260658461012166532103 51726390987691518249798155)
    ·
      refine ⟨77589586481537277374697233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51726390987691518249798155 77589586481537277374697233)
      ·
        refine ⟨58192189861152958031022925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77589586481537277374697233 58192189861152958031022925)
        ·
          refine ⟨21822071197932359261633597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58192189861152958031022925 21822071197932359261633597)
          ·
            refine ⟨8183276699224634723112599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21822071197932359261633597 8183276699224634723112599)
            ·
              refine ⟨12274915048836952084668899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183276699224634723112599 12274915048836952084668899)
              ·
                refine ⟨18412372573255428127003349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12274915048836952084668899 18412372573255428127003349)
                ·
                  refine ⟨431539982185674096726641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18412372573255428127003349 431539982185674096726641)
                  ·
                    rfl

theorem cell23_7563790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_7563790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563790 prefixEnd_7563790 := by exact prefixLift 7563790
  have htrace : WordTrace (prefixWord ++ tailWord_7563790) baseStart_7563790 baseEnd_7563790 := by
    simpa [prefixWord, tailWord_7563790, baseEnd_7563790] using wordTrace_append hprefix tailTrace_7563790
  have hstable : (prefixWord ++ tailWord_7563790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563790).length < 2 ^ (prefixWord ++ tailWord_7563790).sum := by decide
  have hdescent : baseEnd_7563790 < baseStart_7563790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563830 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_7563830 : Nat := 118140960795 + 7563830 * 2 ^ 59
def prefixEnd_7563830 : Nat := 4983230072969 + 3 ^ 40 * 7563830 * 2
def baseEnd_7563830 : Nat := 3883880378897246714039585

theorem tailTrace_7563830 : CollatzResearch.WordTrace tailWord_7563830 prefixEnd_7563830 3883880378897246714039585 := by
  unfold tailWord_7563830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17242221511721449010232059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183917029458362122775808629 17242221511721449010232059)
  ·
    refine ⟨25863332267582173515348089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17242221511721449010232059 25863332267582173515348089)
    ·
      refine ⟨19397499200686630136511067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25863332267582173515348089 19397499200686630136511067)
      ·
        refine ⟨29096248801029945204766601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19397499200686630136511067 29096248801029945204766601)
        ·
          refine ⟨21822186600772458903574951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29096248801029945204766601 21822186600772458903574951)
          ·
            refine ⟨32733279901158688355362427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21822186600772458903574951 32733279901158688355362427)
            ·
              refine ⟨49099919851738032533043641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32733279901158688355362427 49099919851738032533043641)
              ·
                refine ⟨36824939888803524399782731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49099919851738032533043641 36824939888803524399782731)
                ·
                  refine ⟨55237409833205286599674097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36824939888803524399782731 55237409833205286599674097)
                  ·
                    refine ⟨41428057374903964949755573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55237409833205286599674097 41428057374903964949755573)
                    ·
                      refine ⟨3883880378897246714039585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41428057374903964949755573 3883880378897246714039585)
                      ·
                        rfl

theorem cell23_7563830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_7563830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563830 prefixEnd_7563830 := by exact prefixLift 7563830
  have htrace : WordTrace (prefixWord ++ tailWord_7563830) baseStart_7563830 baseEnd_7563830 := by
    simpa [prefixWord, tailWord_7563830, baseEnd_7563830] using wordTrace_append hprefix tailTrace_7563830
  have hstable : (prefixWord ++ tailWord_7563830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563830).length < 2 ^ (prefixWord ++ tailWord_7563830).sum := by decide
  have hdescent : baseEnd_7563830 < baseStart_7563830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563863 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 6]
def baseStart_7563863 : Nat := 118140960795 + 7563863 * 2 ^ 59
def prefixEnd_7563863 : Nat := 4983230072969 + 3 ^ 40 * 7563863 * 2
def baseEnd_7563863 : Nat := 431544147084316120547437

theorem tailTrace_7563863 : CollatzResearch.WordTrace tailWord_7563863 prefixEnd_7563863 431544147084316120547437 := by
  unfold tailWord_7563863
  simp only [CollatzResearch.WordTrace]
  refine ⟨275876747796423630799664243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183917831864282420533109495 275876747796423630799664243)
  ·
    refine ⟨413815121694635446199496365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275876747796423630799664243 413815121694635446199496365)
    ·
      refine ⟨155180670635488292324811137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413815121694635446199496365 155180670635488292324811137)
      ·
        refine ⟨116385502976616219243608353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155180670635488292324811137 116385502976616219243608353)
        ·
          refine ⟨87289127232462164432706265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116385502976616219243608353 87289127232462164432706265)
          ·
            refine ⟨65466845424346623324529699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87289127232462164432706265 65466845424346623324529699)
            ·
              refine ⟨98200268136519934986794549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65466845424346623324529699 98200268136519934986794549)
              ·
                refine ⟨9206275137798743905011989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98200268136519934986794549 9206275137798743905011989)
                ·
                  refine ⟨431544147084316120547437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9206275137798743905011989 431544147084316120547437)
                  ·
                    rfl

theorem cell23_7563863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 6].length) (baseStart_7563863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563863 prefixEnd_7563863 := by exact prefixLift 7563863
  have htrace : WordTrace (prefixWord ++ tailWord_7563863) baseStart_7563863 baseEnd_7563863 := by
    simpa [prefixWord, tailWord_7563863, baseEnd_7563863] using wordTrace_append hprefix tailTrace_7563863
  have hstable : (prefixWord ++ tailWord_7563863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563863).length < 2 ^ (prefixWord ++ tailWord_7563863).sum := by decide
  have hdescent : baseEnd_7563863 < baseStart_7563863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563924 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7563924 : Nat := 118140960795 + 7563924 * 2 ^ 59
def prefixEnd_7563924 : Nat := 4983230072969 + 3 ^ 40 * 7563924 * 2
def baseEnd_7563924 : Nat := 3883928646078769346264153

theorem tailTrace_7563924 : CollatzResearch.WordTrace tailWord_7563924 prefixEnd_7563924 3883928646078769346264153 := by
  unfold tailWord_7563924
  simp only [CollatzResearch.WordTrace]
  refine ⟨137939486324601319108817413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183919315099468425478423217 137939486324601319108817413)
  ·
    refine ⟨25863653685862747332903265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137939486324601319108817413 25863653685862747332903265)
    ·
      refine ⟨19397740264397060499677449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25863653685862747332903265 19397740264397060499677449)
      ·
        refine ⟨14548305198297795374758087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19397740264397060499677449 14548305198297795374758087)
        ·
          refine ⟨21822457797446693062137131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14548305198297795374758087 21822457797446693062137131)
          ·
            refine ⟨32733686696170039593205697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21822457797446693062137131 32733686696170039593205697)
            ·
              refine ⟨24550265022127529694904273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32733686696170039593205697 24550265022127529694904273)
              ·
                refine ⟨18412698766595647271178205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24550265022127529694904273 18412698766595647271178205)
                ·
                  refine ⟨6904762037473367726691827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18412698766595647271178205 6904762037473367726691827)
                  ·
                    refine ⟨10357143056210051590037741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6904762037473367726691827 10357143056210051590037741)
                    ·
                      refine ⟨3883928646078769346264153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10357143056210051590037741 3883928646078769346264153)
                      ·
                        rfl

theorem cell23_7563924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7563924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563924 prefixEnd_7563924 := by exact prefixLift 7563924
  have htrace : WordTrace (prefixWord ++ tailWord_7563924) baseStart_7563924 baseEnd_7563924 := by
    simpa [prefixWord, tailWord_7563924, baseEnd_7563924] using wordTrace_append hprefix tailTrace_7563924
  have hstable : (prefixWord ++ tailWord_7563924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563924).length < 2 ^ (prefixWord ++ tailWord_7563924).sum := by decide
  have hdescent : baseEnd_7563924 < baseStart_7563924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563934 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_7563934 : Nat := 118140960795 + 7563934 * 2 ^ 59
def prefixEnd_7563934 : Nat := 4983230072969 + 3 ^ 40 * 7563934 * 2
def baseEnd_7563934 : Nat := 3883933780885314307139107

theorem tailTrace_7563934 : CollatzResearch.WordTrace tailWord_7563934 prefixEnd_7563934 3883933780885314307139107 := by
  unfold tailWord_7563934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34484917172395801240687357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183919558252777606616999237 34484917172395801240687357)
  ·
    refine ⟨12931843939648425465257759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34484917172395801240687357 12931843939648425465257759)
    ·
      refine ⟨19397765909472638197886639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12931843939648425465257759 19397765909472638197886639)
      ·
        refine ⟨29096648864208957296829959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19397765909472638197886639 29096648864208957296829959)
        ·
          refine ⟨43644973296313435945244939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29096648864208957296829959 43644973296313435945244939)
          ·
            refine ⟨65467459944470153917867409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43644973296313435945244939 65467459944470153917867409)
            ·
              refine ⟨49100594958352615438400557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65467459944470153917867409 49100594958352615438400557)
              ·
                refine ⟨18412723109382230789400209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49100594958352615438400557 18412723109382230789400209)
                ·
                  refine ⟨13809542332036673092050157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18412723109382230789400209 13809542332036673092050157)
                  ·
                    refine ⟨5178578374513752409518809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13809542332036673092050157 5178578374513752409518809)
                    ·
                      refine ⟨3883933780885314307139107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5178578374513752409518809 3883933780885314307139107)
                      ·
                        rfl

theorem cell23_7563934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_7563934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563934 prefixEnd_7563934 := by exact prefixLift 7563934
  have htrace : WordTrace (prefixWord ++ tailWord_7563934) baseStart_7563934 baseEnd_7563934 := by
    simpa [prefixWord, tailWord_7563934, baseEnd_7563934] using wordTrace_append hprefix tailTrace_7563934
  have hstable : (prefixWord ++ tailWord_7563934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563934).length < 2 ^ (prefixWord ++ tailWord_7563934).sum := by decide
  have hdescent : baseEnd_7563934 < baseStart_7563934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563940 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_7563940 : Nat := 118140960795 + 7563940 * 2 ^ 59
def prefixEnd_7563940 : Nat := 4983230072969 + 3 ^ 40 * 7563940 * 2
def baseEnd_7563940 : Nat := 1294645620589747094554693

theorem tailTrace_7563940 : CollatzResearch.WordTrace tailWord_7563940 prefixEnd_7563940 1294645620589747094554693 := by
  unfold tailWord_7563940
  simp only [CollatzResearch.WordTrace]
  refine ⟨137939778108572336475108637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183919704144763115300144849 137939778108572336475108637)
  ·
    refine ⟨51727416790714626178165739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137939778108572336475108637 51727416790714626178165739)
    ·
      refine ⟨77591125186071939267248609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51727416790714626178165739 77591125186071939267248609)
      ·
        refine ⟨58193343889553954450436457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77591125186071939267248609 58193343889553954450436457)
        ·
          refine ⟨43645007917165465837827343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58193343889553954450436457 43645007917165465837827343)
          ·
            refine ⟨65467511875748198756741015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43645007917165465837827343 65467511875748198756741015)
            ·
              refine ⟨98201267813622298135111523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65467511875748198756741015 98201267813622298135111523)
              ·
                refine ⟨147301901720433447202667285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98201267813622298135111523 147301901720433447202667285)
                ·
                  refine ⟨6904776643145317837625029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147301901720433447202667285 6904776643145317837625029)
                  ·
                    refine ⟨1294645620589747094554693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6904776643145317837625029 1294645620589747094554693)
                    ·
                      rfl

theorem cell23_7563940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_7563940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563940 prefixEnd_7563940 := by exact prefixLift 7563940
  have htrace : WordTrace (prefixWord ++ tailWord_7563940) baseStart_7563940 baseEnd_7563940 := by
    simpa [prefixWord, tailWord_7563940, baseEnd_7563940] using wordTrace_append hprefix tailTrace_7563940
  have hstable : (prefixWord ++ tailWord_7563940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563940).length < 2 ^ (prefixWord ++ tailWord_7563940).sum := by decide
  have hdescent : baseEnd_7563940 < baseStart_7563940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563957 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_7563957 : Nat := 118140960795 + 7563957 * 2 ^ 59
def prefixEnd_7563957 : Nat := 4983230072969 + 3 ^ 40 * 7563957 * 2
def baseEnd_7563957 : Nat := 1294648530313455905717167

theorem tailTrace_7563957 : CollatzResearch.WordTrace tailWord_7563957 prefixEnd_7563957 1294648530313455905717167 := by
  unfold tailWord_7563957
  simp only [CollatzResearch.WordTrace]
  refine ⟨275880176258083084853586125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183920117505388723235724083 275880176258083084853586125)
  ·
    refine ⟨103455066096781156820094797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275880176258083084853586125 103455066096781156820094797)
    ·
      refine ⟨38795649786292933807535549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103455066096781156820094797 38795649786292933807535549)
      ·
        refine ⟨14548368669859850177825831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38795649786292933807535549 14548368669859850177825831)
        ·
          refine ⟨21822553004789775266738747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14548368669859850177825831 21822553004789775266738747)
          ·
            refine ⟨32733829507184662900108121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21822553004789775266738747 32733829507184662900108121)
            ·
              refine ⟨24550372130388497175081091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32733829507184662900108121 24550372130388497175081091)
              ·
                refine ⟨36825558195582745762621637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24550372130388497175081091 36825558195582745762621637)
                ·
                  refine ⟨6904792161671764830491557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36825558195582745762621637 6904792161671764830491557)
                  ·
                    refine ⟨1294648530313455905717167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6904792161671764830491557 1294648530313455905717167)
                    ·
                      rfl

theorem cell23_7563957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_7563957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563957 prefixEnd_7563957 := by exact prefixLift 7563957
  have htrace : WordTrace (prefixWord ++ tailWord_7563957) baseStart_7563957 baseEnd_7563957 := by
    simpa [prefixWord, tailWord_7563957, baseEnd_7563957] using wordTrace_append hprefix tailTrace_7563957
  have hstable : (prefixWord ++ tailWord_7563957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563957).length < 2 ^ (prefixWord ++ tailWord_7563957).sum := by decide
  have hdescent : baseEnd_7563957 < baseStart_7563957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7563958 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_7563958 : Nat := 118140960795 + 7563958 * 2 ^ 59
def prefixEnd_7563958 : Nat := 4983230072969 + 3 ^ 40 * 7563958 * 2
def baseEnd_7563958 : Nat := 3883946104421022213238997

theorem tailTrace_7563958 : CollatzResearch.WordTrace tailWord_7563958 prefixEnd_7563958 3883946104421022213238997 := by
  unfold tailWord_7563958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17242513295692466376523283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183920141820719641349581685 17242513295692466376523283)
  ·
    refine ⟨25863769943538699564784925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17242513295692466376523283 25863769943538699564784925)
    ·
      refine ⟨9698913728827012336794347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25863769943538699564784925 9698913728827012336794347)
      ·
        refine ⟨14548370593240518505191521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698913728827012336794347 14548370593240518505191521)
        ·
          refine ⟨10911277944930388878893641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14548370593240518505191521 10911277944930388878893641)
          ·
            refine ⟨8183458458697791659170231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10911277944930388878893641 8183458458697791659170231)
            ·
              refine ⟨12275187688046687488755347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183458458697791659170231 12275187688046687488755347)
              ·
                refine ⟨18412781532070031233133021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12275187688046687488755347 18412781532070031233133021)
                ·
                  refine ⟨6904793074526261712424883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18412781532070031233133021 6904793074526261712424883)
                  ·
                    refine ⟨10357189611789392568637325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6904793074526261712424883 10357189611789392568637325)
                    ·
                      refine ⟨3883946104421022213238997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10357189611789392568637325 3883946104421022213238997)
                      ·
                        rfl

theorem cell23_7563958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_7563958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7563958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7563958 prefixEnd_7563958 := by exact prefixLift 7563958
  have htrace : WordTrace (prefixWord ++ tailWord_7563958) baseStart_7563958 baseEnd_7563958 := by
    simpa [prefixWord, tailWord_7563958, baseEnd_7563958] using wordTrace_append hprefix tailTrace_7563958
  have hstable : (prefixWord ++ tailWord_7563958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7563958).length < 2 ^ (prefixWord ++ tailWord_7563958).sum := by decide
  have hdescent : baseEnd_7563958 < baseStart_7563958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7563958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564014 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_7564014 : Nat := 118140960795 + 7564014 * 2 ^ 59
def prefixEnd_7564014 : Nat := 4983230072969 + 3 ^ 40 * 7564014 * 2
def baseEnd_7564014 : Nat := 3883974859337673994138739

theorem tailTrace_7564014 : CollatzResearch.WordTrace tailWord_7564014 prefixEnd_7564014 3883974859337673994138739 := by
  unfold tailWord_7564014
  simp only [CollatzResearch.WordTrace]
  refine ⟨34485281902359572948551387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183921503479251055725607397 34485281902359572948551387)
  ·
    refine ⟨51727922853539359422827081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34485281902359572948551387 51727922853539359422827081)
    ·
      refine ⟨38795942140154519567120311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51727922853539359422827081 38795942140154519567120311)
      ·
        refine ⟨58193913210231779350680467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38795942140154519567120311 58193913210231779350680467)
        ·
          refine ⟨87290869815347669026020701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58193913210231779350680467 87290869815347669026020701)
          ·
            refine ⟨32734076180755375884757763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87290869815347669026020701 32734076180755375884757763)
            ·
              refine ⟨49101114271133063827136645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32734076180755375884757763 49101114271133063827136645)
              ·
                refine ⟨9206458925837449467588121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49101114271133063827136645 9206458925837449467588121)
                ·
                  refine ⟨6904844194378087100691091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9206458925837449467588121 6904844194378087100691091)
                  ·
                    refine ⟨10357266291567130651036637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6904844194378087100691091 10357266291567130651036637)
                    ·
                      refine ⟨3883974859337673994138739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10357266291567130651036637 3883974859337673994138739)
                      ·
                        rfl

theorem cell23_7564014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_7564014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564014 prefixEnd_7564014 := by exact prefixLift 7564014
  have htrace : WordTrace (prefixWord ++ tailWord_7564014) baseStart_7564014 baseEnd_7564014 := by
    simpa [prefixWord, tailWord_7564014, baseEnd_7564014] using wordTrace_append hprefix tailTrace_7564014
  have hstable : (prefixWord ++ tailWord_7564014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564014).length < 2 ^ (prefixWord ++ tailWord_7564014).sum := by decide
  have hdescent : baseEnd_7564014 < baseStart_7564014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564021 : List Nat := [1, 3, 6, 1, 1, 2, 1, 8]
def baseStart_7564021 : Nat := 118140960795 + 7564021 * 2 ^ 59
def prefixEnd_7564021 : Nat := 4983230072969 + 3 ^ 40 * 7564021 * 2
def baseEnd_7564021 : Nat := 143851053840824276546341

theorem tailTrace_7564021 : CollatzResearch.WordTrace tailWord_7564021 prefixEnd_7564021 143851053840824276546341 := by
  unfold tailWord_7564021
  simp only [CollatzResearch.WordTrace]
  refine ⟨275882510529851223783915917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183921673686567482522610611 275882510529851223783915917)
  ·
    refine ⟨103455941448694208918968469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275882510529851223783915917 103455941448694208918968469)
    ·
      refine ⟨4849497255407541043076647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103455941448694208918968469 4849497255407541043076647)
      ·
        refine ⟨7274245883111311564614971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4849497255407541043076647 7274245883111311564614971)
        ·
          refine ⟨10911368824666967346922457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7274245883111311564614971 10911368824666967346922457)
          ·
            refine ⟨8183526618500225510191843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10911368824666967346922457 8183526618500225510191843)
            ·
              refine ⟨12275289927750338265287765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183526618500225510191843 12275289927750338265287765)
              ·
                refine ⟨143851053840824276546341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12275289927750338265287765 143851053840824276546341)
                ·
                  rfl

theorem cell23_7564021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 8].length) (baseStart_7564021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564021 prefixEnd_7564021 := by exact prefixLift 7564021
  have htrace : WordTrace (prefixWord ++ tailWord_7564021) baseStart_7564021 baseEnd_7564021 := by
    simpa [prefixWord, tailWord_7564021, baseEnd_7564021] using wordTrace_append hprefix tailTrace_7564021
  have hstable : (prefixWord ++ tailWord_7564021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564021).length < 2 ^ (prefixWord ++ tailWord_7564021).sum := by decide
  have hdescent : baseEnd_7564021 < baseStart_7564021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564124 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_7564124 : Nat := 118140960795 + 7564124 * 2 ^ 59
def prefixEnd_7564124 : Nat := 4983230072969 + 3 ^ 40 * 7564124 * 2
def baseEnd_7564124 : Nat := 1294677114069889521254411

theorem tailTrace_7564124 : CollatzResearch.WordTrace tailWord_7564124 prefixEnd_7564124 1294677114069889521254411 := by
  unfold tailWord_7564124
  simp only [CollatzResearch.WordTrace]
  refine ⟨137943133624239036187457713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183924178165652048249943617 137943133624239036187457713)
  ·
    refine ⟨103457350218179277140593285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137943133624239036187457713 103457350218179277140593285)
    ·
      refine ⟨19398253165908614463861241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103457350218179277140593285 19398253165908614463861241)
      ·
        refine ⟨14548689874431460847895931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19398253165908614463861241 14548689874431460847895931)
        ·
          refine ⟨21823034811647191271843897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14548689874431460847895931 21823034811647191271843897)
          ·
            refine ⟨16367276108735393453882923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21823034811647191271843897 16367276108735393453882923)
            ·
              refine ⟨24550914163103090180824385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16367276108735393453882923 24550914163103090180824385)
              ·
                refine ⟨18413185622327317635618289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24550914163103090180824385 18413185622327317635618289)
                ·
                  refine ⟨13809889216745488226713717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18413185622327317635618289 13809889216745488226713717)
                  ·
                    refine ⟨1294677114069889521254411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13809889216745488226713717 1294677114069889521254411)
                    ·
                      rfl

theorem cell23_7564124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_7564124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564124 prefixEnd_7564124 := by exact prefixLift 7564124
  have htrace : WordTrace (prefixWord ++ tailWord_7564124) baseStart_7564124 baseEnd_7564124 := by
    simpa [prefixWord, tailWord_7564124, baseEnd_7564124] using wordTrace_append hprefix tailTrace_7564124
  have hstable : (prefixWord ++ tailWord_7564124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564124).length < 2 ^ (prefixWord ++ tailWord_7564124).sum := by decide
  have hdescent : baseEnd_7564124 < baseStart_7564124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564127 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_7564127 : Nat := 118140960795 + 7564127 * 2 ^ 59
def prefixEnd_7564127 : Nat := 4983230072969 + 3 ^ 40 * 7564127 * 2
def baseEnd_7564127 : Nat := 3884032882651632052025719

theorem tailTrace_7564127 : CollatzResearch.WordTrace tailWord_7564127 prefixEnd_7564127 3884032882651632052025719 := by
  unfold tailWord_7564127
  simp only [CollatzResearch.WordTrace]
  refine ⟨275886376667467203887274635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183924251111644802591516423 275886376667467203887274635)
  ·
    refine ⟨413829565001200805830911953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275886376667467203887274635 413829565001200805830911953)
    ·
      refine ⟨310372173750900604373183965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413829565001200805830911953 310372173750900604373183965)
      ·
        refine ⟨116389565156587726639943987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310372173750900604373183965 116389565156587726639943987)
        ·
          refine ⟨174584347734881589959915981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116389565156587726639943987 174584347734881589959915981)
          ·
            refine ⟨65469130400580596234968493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174584347734881589959915981 65469130400580596234968493)
            ·
              refine ⟨24550923900217723588113185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65469130400580596234968493 24550923900217723588113185)
              ·
                refine ⟨18413192925163292691084889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24550923900217723588113185 18413192925163292691084889)
                ·
                  refine ⟨13809894693872469518313667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18413192925163292691084889 13809894693872469518313667)
                  ·
                    refine ⟨20714842040808704277470501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13809894693872469518313667 20714842040808704277470501)
                    ·
                      refine ⟨3884032882651632052025719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20714842040808704277470501 3884032882651632052025719)
                      ·
                        rfl

theorem cell23_7564127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_7564127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564127 prefixEnd_7564127 := by exact prefixLift 7564127
  have htrace : WordTrace (prefixWord ++ tailWord_7564127) baseStart_7564127 baseEnd_7564127 := by
    simpa [prefixWord, tailWord_7564127, baseEnd_7564127] using wordTrace_append hprefix tailTrace_7564127
  have hstable : (prefixWord ++ tailWord_7564127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564127).length < 2 ^ (prefixWord ++ tailWord_7564127).sum := by decide
  have hdescent : baseEnd_7564127 < baseStart_7564127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564187 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 11, 2]
def baseStart_7564187 : Nat := 118140960795 + 7564187 * 2 ^ 59
def prefixEnd_7564187 : Nat := 4983230072969 + 3 ^ 40 * 7564187 * 2
def baseEnd_7564187 : Nat := 3884063691490901817275443

theorem tailTrace_7564187 : CollatzResearch.WordTrace tailWord_7564187 prefixEnd_7564187 3884063691490901817275443 := by
  unfold tailWord_7564187
  simp only [CollatzResearch.WordTrace]
  refine ⟨275888565047249834134458815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183925710031499889422972543 275888565047249834134458815)
  ·
    refine ⟨413832847570874751201688223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275888565047249834134458815 413832847570874751201688223)
    ·
      refine ⟨620749271356312126802532335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413832847570874751201688223 620749271356312126802532335)
      ·
        refine ⟨931123907034468190203798503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620749271356312126802532335 931123907034468190203798503)
        ·
          refine ⟨1396685860551702285305697755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931123907034468190203798503 1396685860551702285305697755)
          ·
            refine ⟨2095028790827553427958546633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396685860551702285305697755 2095028790827553427958546633)
            ·
              refine ⟨1571271593120665070968909975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095028790827553427958546633 1571271593120665070968909975)
              ·
                refine ⟨2356907389680997606453364963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571271593120665070968909975 2356907389680997606453364963)
                ·
                  refine ⟨3535361084521496409680047445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356907389680997606453364963 3535361084521496409680047445)
                  ·
                    refine ⟨5178751588654535756367257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 3535361084521496409680047445 5178751588654535756367257)
                    ·
                      refine ⟨3884063691490901817275443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5178751588654535756367257 3884063691490901817275443)
                      ·
                        rfl

theorem cell23_7564187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 11, 2].length) (baseStart_7564187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564187 prefixEnd_7564187 := by exact prefixLift 7564187
  have htrace : WordTrace (prefixWord ++ tailWord_7564187) baseStart_7564187 baseEnd_7564187 := by
    simpa [prefixWord, tailWord_7564187, baseEnd_7564187] using wordTrace_append hprefix tailTrace_7564187
  have hstable : (prefixWord ++ tailWord_7564187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564187).length < 2 ^ (prefixWord ++ tailWord_7564187).sum := by decide
  have hdescent : baseEnd_7564187 < baseStart_7564187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564188 : List Nat := [2, 2, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_7564188 : Nat := 118140960795 + 7564188 * 2 ^ 59
def prefixEnd_7564188 : Nat := 4983230072969 + 3 ^ 40 * 7564188 * 2
def baseEnd_7564188 : Nat := 1294688068323852104454313

theorem tailTrace_7564188 : CollatzResearch.WordTrace tailWord_7564188 prefixEnd_7564188 1294688068323852104454313 := by
  unfold tailWord_7564188
  simp only [CollatzResearch.WordTrace]
  refine ⟨137944300760123105652622609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183925734346830807536830145 137944300760123105652622609)
  ·
    refine ⟨103458225570092329239466957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137944300760123105652622609 103458225570092329239466957)
    ·
      refine ⟨38796834588784623464800109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103458225570092329239466957 38796834588784623464800109)
      ·
        refine ⟨14548812970794233799300041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38796834588784623464800109 14548812970794233799300041)
        ·
          refine ⟨10911609728095675349475031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14548812970794233799300041 10911609728095675349475031)
          ·
            refine ⟨16367414592143513024212547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10911609728095675349475031 16367414592143513024212547)
            ·
              refine ⟨24551121888215269536318821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16367414592143513024212547 24551121888215269536318821)
              ·
                refine ⟨4603335354040363038059779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24551121888215269536318821 4603335354040363038059779)
                ·
                  refine ⟨6905003031060544557089669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603335354040363038059779 6905003031060544557089669)
                  ·
                    refine ⟨1294688068323852104454313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6905003031060544557089669 1294688068323852104454313)
                    ·
                      rfl

theorem cell23_7564188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_7564188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564188 prefixEnd_7564188 := by exact prefixLift 7564188
  have htrace : WordTrace (prefixWord ++ tailWord_7564188) baseStart_7564188 baseEnd_7564188 := by
    simpa [prefixWord, tailWord_7564188, baseEnd_7564188] using wordTrace_append hprefix tailTrace_7564188
  have hstable : (prefixWord ++ tailWord_7564188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564188).length < 2 ^ (prefixWord ++ tailWord_7564188).sum := by decide
  have hdescent : baseEnd_7564188 < baseStart_7564188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564221 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_7564221 : Nat := 118140960795 + 7564221 * 2 ^ 59
def prefixEnd_7564221 : Nat := 4983230072969 + 3 ^ 40 * 7564221 * 2
def baseEnd_7564221 : Nat := 3884081149833154684250287

theorem tailTrace_7564221 : CollatzResearch.WordTrace tailWord_7564221 prefixEnd_7564221 3884081149833154684250287 := by
  unfold tailWord_7564221
  simp only [CollatzResearch.WordTrace]
  refine ⟨275889805129126657941196517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183926536752751105294131011 275889805129126657941196517)
  ·
    refine ⟨51729338461711248363974347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275889805129126657941196517 51729338461711248363974347)
    ·
      refine ⟨77594007692566872545961521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51729338461711248363974347 77594007692566872545961521)
      ·
        refine ⟨58195505769425154409471141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77594007692566872545961521 58195505769425154409471141)
        ·
          refine ⟨10911657331767216451775839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58195505769425154409471141 10911657331767216451775839)
          ·
            refine ⟨16367485997650824677663759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10911657331767216451775839 16367485997650824677663759)
            ·
              refine ⟨24551228996476237016495639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16367485997650824677663759 24551228996476237016495639)
              ·
                refine ⟨36826843494714355524743459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24551228996476237016495639 36826843494714355524743459)
                ·
                  refine ⟨55240265242071533287115189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36826843494714355524743459 55240265242071533287115189)
                  ·
                    refine ⟨5178774866444206245667049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55240265242071533287115189 5178774866444206245667049)
                    ·
                      refine ⟨3884081149833154684250287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5178774866444206245667049 3884081149833154684250287)
                      ·
                        rfl

theorem cell23_7564221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_7564221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564221 prefixEnd_7564221 := by exact prefixLift 7564221
  have htrace : WordTrace (prefixWord ++ tailWord_7564221) baseStart_7564221 baseEnd_7564221 := by
    simpa [prefixWord, tailWord_7564221, baseEnd_7564221] using wordTrace_append hprefix tailTrace_7564221
  have hstable : (prefixWord ++ tailWord_7564221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564221).length < 2 ^ (prefixWord ++ tailWord_7564221).sum := by decide
  have hdescent : baseEnd_7564221 < baseStart_7564221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564227 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 6, 4]
def baseStart_7564227 : Nat := 118140960795 + 7564227 * 2 ^ 59
def prefixEnd_7564227 : Nat := 4983230072969 + 3 ^ 40 * 7564227 * 2
def baseEnd_7564227 : Nat := 1294694743572360553591753

theorem tailTrace_7564227 : CollatzResearch.WordTrace tailWord_7564227 prefixEnd_7564227 1294694743572360553591753 := by
  unfold tailWord_7564227
  simp only [CollatzResearch.WordTrace]
  refine ⟨275890023967104920965914935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183926682644736613977276623 275890023967104920965914935)
  ·
    refine ⟨413835035950657381448872403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275890023967104920965914935 413835035950657381448872403)
    ·
      refine ⟨620752553925986072173308605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413835035950657381448872403 620752553925986072173308605)
      ·
        refine ⟨232782207722244777064990727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620752553925986072173308605 232782207722244777064990727)
        ·
          refine ⟨349173311583367165597486091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232782207722244777064990727 349173311583367165597486091)
          ·
            refine ⟨523759967375050748396229137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349173311583367165597486091 523759967375050748396229137)
            ·
              refine ⟨392819975531288061297171853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523759967375050748396229137 392819975531288061297171853)
              ·
                refine ⟨147307490824233022986439445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392819975531288061297171853 147307490824233022986439445)
                ·
                  refine ⟨6905038632385922952489349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147307490824233022986439445 6905038632385922952489349)
                  ·
                    refine ⟨1294694743572360553591753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6905038632385922952489349 1294694743572360553591753)
                    ·
                      rfl

theorem cell23_7564227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 4].length) (baseStart_7564227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564227 prefixEnd_7564227 := by exact prefixLift 7564227
  have htrace : WordTrace (prefixWord ++ tailWord_7564227) baseStart_7564227 baseEnd_7564227 := by
    simpa [prefixWord, tailWord_7564227, baseEnd_7564227] using wordTrace_append hprefix tailTrace_7564227
  have hstable : (prefixWord ++ tailWord_7564227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564227).length < 2 ^ (prefixWord ++ tailWord_7564227).sum := by decide
  have hdescent : baseEnd_7564227 < baseStart_7564227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564264 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_7564264 : Nat := 118140960795 + 7564264 * 2 ^ 59
def prefixEnd_7564264 : Nat := 4983230072969 + 3 ^ 40 * 7564264 * 2
def baseEnd_7564264 : Nat := 3884103229501298016012589

theorem tailTrace_7564264 : CollatzResearch.WordTrace tailWord_7564264 prefixEnd_7564264 3884103229501298016012589 := by
  unfold tailWord_7564264
  simp only [CollatzResearch.WordTrace]
  refine ⟨137945686733985438142505923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183927582311980584190007897 137945686733985438142505923)
  ·
    refine ⟨206918530100978157213758885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137945686733985438142505923 206918530100978157213758885)
    ·
      refine ⟨38797224393933404477579791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206918530100978157213758885 38797224393933404477579791)
      ·
        refine ⟨58195836590900106716369687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38797224393933404477579791 58195836590900106716369687)
        ·
          refine ⟨87293754886350160074554531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58195836590900106716369687 87293754886350160074554531)
          ·
            refine ⟨130940632329525240111831797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87293754886350160074554531 130940632329525240111831797)
            ·
              refine ⟨12275684280892991260484231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130940632329525240111831797 12275684280892991260484231)
              ·
                refine ⟨18413526421339486890726347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12275684280892991260484231 18413526421339486890726347)
                ·
                  refine ⟨27620289632009230336089521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18413526421339486890726347 27620289632009230336089521)
                  ·
                    refine ⟨20715217224006922752067141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27620289632009230336089521 20715217224006922752067141)
                    ·
                      refine ⟨3884103229501298016012589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20715217224006922752067141 3884103229501298016012589)
                      ·
                        rfl

theorem cell23_7564264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_7564264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564264 prefixEnd_7564264 := by exact prefixLift 7564264
  have htrace : WordTrace (prefixWord ++ tailWord_7564264) baseStart_7564264 baseEnd_7564264 := by
    simpa [prefixWord, tailWord_7564264, baseEnd_7564264] using wordTrace_append hprefix tailTrace_7564264
  have hstable : (prefixWord ++ tailWord_7564264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564264).length < 2 ^ (prefixWord ++ tailWord_7564264).sum := by decide
  have hdescent : baseEnd_7564264 < baseStart_7564264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564271 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 3]
def baseStart_7564271 : Nat := 118140960795 + 7564271 * 2 ^ 59
def prefixEnd_7564271 : Nat := 4983230072969 + 3 ^ 40 * 7564271 * 2
def baseEnd_7564271 : Nat := 3884106823865879488625057

theorem tailTrace_7564271 : CollatzResearch.WordTrace tailWord_7564271 prefixEnd_7564271 3884106823865879488625057 := by
  unfold tailWord_7564271
  simp only [CollatzResearch.WordTrace]
  refine ⟨275891628778945516480516667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183927752519297010987011111 275891628778945516480516667)
  ·
    refine ⟨413837443168418274720775001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275891628778945516480516667 413837443168418274720775001)
    ·
      refine ⟨310378082376313706040581251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413837443168418274720775001 310378082376313706040581251)
      ·
        refine ⟨465567123564470559060871877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310378082376313706040581251 465567123564470559060871877)
        ·
          refine ⟨87293835668338229823913477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465567123564470559060871877 87293835668338229823913477)
          ·
            refine ⟨16367594187813418091983777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87293835668338229823913477 16367594187813418091983777)
            ·
              refine ⟨12275695640860063568987833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16367594187813418091983777 12275695640860063568987833)
              ·
                refine ⟨9206771730645047676740875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12275695640860063568987833 9206771730645047676740875)
                ·
                  refine ⟨13810157595967571515111313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9206771730645047676740875 13810157595967571515111313)
                  ·
                    refine ⟨10357618196975678636333485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13810157595967571515111313 10357618196975678636333485)
                    ·
                      refine ⟨3884106823865879488625057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10357618196975678636333485 3884106823865879488625057)
                      ·
                        rfl

theorem cell23_7564271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 3].length) (baseStart_7564271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564271 prefixEnd_7564271 := by exact prefixLift 7564271
  have htrace : WordTrace (prefixWord ++ tailWord_7564271) baseStart_7564271 baseEnd_7564271 := by
    simpa [prefixWord, tailWord_7564271, baseEnd_7564271] using wordTrace_append hprefix tailTrace_7564271
  have hstable : (prefixWord ++ tailWord_7564271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564271).length < 2 ^ (prefixWord ++ tailWord_7564271).sum := by decide
  have hdescent : baseEnd_7564271 < baseStart_7564271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564302 : List Nat := [4, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_7564302 : Nat := 118140960795 + 7564302 * 2 ^ 59
def prefixEnd_7564302 : Nat := 4983230072969 + 3 ^ 40 * 7564302 * 2
def baseEnd_7564302 : Nat := 3884122741766168867337415

theorem tailTrace_7564302 : CollatzResearch.WordTrace tailWord_7564302 prefixEnd_7564302 3884122741766168867337415 := by
  unfold tailWord_7564302
  simp only [CollatzResearch.WordTrace]
  refine ⟨34486594930229151096861895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183928506294555472516596773 34486594930229151096861895)
  ·
    refine ⟨51729892395343726645292843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34486594930229151096861895 51729892395343726645292843)
    ·
      refine ⟨77594838593015589967939265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51729892395343726645292843 77594838593015589967939265)
      ·
        refine ⟨58196128944761692475954449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77594838593015589967939265 58196128944761692475954449)
        ·
          refine ⟨43647096708571269356965837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58196128944761692475954449 43647096708571269356965837)
          ·
            refine ⟨16367661265714226008862189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43647096708571269356965837 16367661265714226008862189)
            ·
              refine ⟨6137872974642834753323321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16367661265714226008862189 6137872974642834753323321)
              ·
                refine ⟨4603404730982126064992491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6137872974642834753323321 4603404730982126064992491)
                ·
                  refine ⟨6905107096473189097488737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603404730982126064992491 6905107096473189097488737)
                  ·
                    refine ⟨5178830322354891823116553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905107096473189097488737 5178830322354891823116553)
                    ·
                      refine ⟨3884122741766168867337415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5178830322354891823116553 3884122741766168867337415)
                      ·
                        rfl

theorem cell23_7564302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_7564302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564302 prefixEnd_7564302 := by exact prefixLift 7564302
  have htrace : WordTrace (prefixWord ++ tailWord_7564302) baseStart_7564302 baseEnd_7564302 := by
    simpa [prefixWord, tailWord_7564302, baseEnd_7564302] using wordTrace_append hprefix tailTrace_7564302
  have hstable : (prefixWord ++ tailWord_7564302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564302).length < 2 ^ (prefixWord ++ tailWord_7564302).sum := by decide
  have hdescent : baseEnd_7564302 < baseStart_7564302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564307 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 4]
def baseStart_7564307 : Nat := 118140960795 + 7564307 * 2 ^ 59
def prefixEnd_7564307 : Nat := 4983230072969 + 3 ^ 40 * 7564307 * 2
def baseEnd_7564307 : Nat := 3884125309169441347774891

theorem tailTrace_7564307 : CollatzResearch.WordTrace tailWord_7564307 prefixEnd_7564307 3884125309169441347774891 := by
  unfold tailWord_7564307
  simp only [CollatzResearch.WordTrace]
  refine ⟨275892941806815094628827175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183928627871210063085884783 275892941806815094628827175)
  ·
    refine ⟨413839412710222641943240763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275892941806815094628827175 413839412710222641943240763)
    ·
      refine ⟨620759119065333962914861145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413839412710222641943240763 620759119065333962914861145)
      ·
        refine ⟨465569339299000472186145859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620759119065333962914861145 465569339299000472186145859)
        ·
          refine ⟨698354008948500708279218789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465569339299000472186145859 698354008948500708279218789)
          ·
            refine ⟨130941376677843882802353523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 698354008948500708279218789 130941376677843882802353523)
            ·
              refine ⟨196412065016765824203530285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130941376677843882802353523 196412065016765824203530285)
              ·
                refine ⟨73654524381287184076323857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196412065016765824203530285 73654524381287184076323857)
                ·
                  refine ⟨55240893285965388057242893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73654524381287184076323857 55240893285965388057242893)
                  ·
                    refine ⟨20715334982237020521466085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55240893285965388057242893 20715334982237020521466085)
                    ·
                      refine ⟨3884125309169441347774891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20715334982237020521466085 3884125309169441347774891)
                      ·
                        rfl

theorem cell23_7564307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_7564307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564307 prefixEnd_7564307 := by exact prefixLift 7564307
  have htrace : WordTrace (prefixWord ++ tailWord_7564307) baseStart_7564307 baseEnd_7564307 := by
    simpa [prefixWord, tailWord_7564307, baseEnd_7564307] using wordTrace_append hprefix tailTrace_7564307
  have hstable : (prefixWord ++ tailWord_7564307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564307).length < 2 ^ (prefixWord ++ tailWord_7564307).sum := by decide
  have hdescent : baseEnd_7564307 < baseStart_7564307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564344 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_7564344 : Nat := 118140960795 + 7564344 * 2 ^ 59
def prefixEnd_7564344 : Nat := 4983230072969 + 3 ^ 40 * 7564344 * 2
def baseEnd_7564344 : Nat := 3884144307953657703012221

theorem tailTrace_7564344 : CollatzResearch.WordTrace tailWord_7564344 prefixEnd_7564344 3884144307953657703012221 := by
  unfold tailWord_7564344
  simp only [CollatzResearch.WordTrace]
  refine ⟨137947145653840524973962043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183929527538454033298616057 137947145653840524973962043)
  ·
    refine ⟨206920718480760787460943065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137947145653840524973962043 206920718480760787460943065)
    ·
      refine ⟨155190538860570590595707299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206920718480760787460943065 155190538860570590595707299)
      ·
        refine ⟨232785808290855885893560949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155190538860570590595707299 232785808290855885893560949)
        ·
          refine ⟨21823669527267739302521339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232785808290855885893560949 21823669527267739302521339)
          ·
            refine ⟨32735504290901608953782009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21823669527267739302521339 32735504290901608953782009)
            ·
              refine ⟨24551628218176206715336507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32735504290901608953782009 24551628218176206715336507)
              ·
                refine ⟨36827442327264310073004761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24551628218176206715336507 36827442327264310073004761)
                ·
                  refine ⟨27620581745448232554753571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36827442327264310073004761 27620581745448232554753571)
                  ·
                    refine ⟨41430872618172348832130357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27620581745448232554753571 41430872618172348832130357)
                    ·
                      refine ⟨3884144307953657703012221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41430872618172348832130357 3884144307953657703012221)
                      ·
                        rfl

theorem cell23_7564344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_7564344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564344 prefixEnd_7564344 := by exact prefixLift 7564344
  have htrace : WordTrace (prefixWord ++ tailWord_7564344) baseStart_7564344 baseEnd_7564344 := by
    simpa [prefixWord, tailWord_7564344, baseEnd_7564344] using wordTrace_append hprefix tailTrace_7564344
  have hstable : (prefixWord ++ tailWord_7564344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564344).length < 2 ^ (prefixWord ++ tailWord_7564344).sum := by decide
  have hdescent : baseEnd_7564344 < baseStart_7564344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564345 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 1, 3, 2]
def baseStart_7564345 : Nat := 118140960795 + 7564345 * 2 ^ 59
def prefixEnd_7564345 : Nat := 4983230072969 + 3 ^ 40 * 7564345 * 2
def baseEnd_7564345 : Nat := 3884144821434312199099717

theorem tailTrace_7564345 : CollatzResearch.WordTrace tailWord_7564345 prefixEnd_7564345 3884144821434312199099717 := by
  unfold tailWord_7564345
  simp only [CollatzResearch.WordTrace]
  refine ⟨275894327780677427118710489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183929551853784951412473659 275894327780677427118710489)
  ·
    refine ⟨206920745835508070339032867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275894327780677427118710489 206920745835508070339032867)
    ·
      refine ⟨310381118753262105508549301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206920745835508070339032867 310381118753262105508549301)
      ·
        refine ⟨29098229883118322391426497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310381118753262105508549301 29098229883118322391426497)
        ·
          refine ⟨21823672412338741793569873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29098229883118322391426497 21823672412338741793569873)
          ·
            refine ⟨16367754309254056345177405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21823672412338741793569873 16367754309254056345177405)
            ·
              refine ⟨6137907865970271129441527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16367754309254056345177405 6137907865970271129441527)
              ·
                refine ⟨9206861798955406694162291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137907865970271129441527 9206861798955406694162291)
                ·
                  refine ⟨13810292698433110041243437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9206861798955406694162291 13810292698433110041243437)
                  ·
                    refine ⟨5178859761912416265466289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13810292698433110041243437 5178859761912416265466289)
                    ·
                      refine ⟨3884144821434312199099717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5178859761912416265466289 3884144821434312199099717)
                      ·
                        rfl

theorem cell23_7564345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_7564345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564345 prefixEnd_7564345 := by exact prefixLift 7564345
  have htrace : WordTrace (prefixWord ++ tailWord_7564345) baseStart_7564345 baseEnd_7564345 := by
    simpa [prefixWord, tailWord_7564345, baseEnd_7564345] using wordTrace_append hprefix tailTrace_7564345
  have hstable : (prefixWord ++ tailWord_7564345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564345).length < 2 ^ (prefixWord ++ tailWord_7564345).sum := by decide
  have hdescent : baseEnd_7564345 < baseStart_7564345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564357 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_7564357 : Nat := 118140960795 + 7564357 * 2 ^ 59
def prefixEnd_7564357 : Nat := 4983230072969 + 3 ^ 40 * 7564357 * 2
def baseEnd_7564357 : Nat := 3884150983202166152149661

theorem tailTrace_7564357 : CollatzResearch.WordTrace tailWord_7564357 prefixEnd_7564357 3884150983202166152149661 := by
  unfold tailWord_7564357
  simp only [CollatzResearch.WordTrace]
  refine ⟨275894765456633953168147325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183929843637755968778764883 275894765456633953168147325)
  ·
    refine ⟨103460537046237732438055247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275894765456633953168147325 103460537046237732438055247)
    ·
      refine ⟨155190805569356598657082871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103460537046237732438055247 155190805569356598657082871)
      ·
        refine ⟨232786208354034897985624307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155190805569356598657082871 232786208354034897985624307)
        ·
          refine ⟨349179312531052346978436461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232786208354034897985624307 349179312531052346978436461)
          ·
            refine ⟨130942242199144630116913673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349179312531052346978436461 130942242199144630116913673)
            ·
              refine ⟨98206681649358472587685255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130942242199144630116913673 98206681649358472587685255)
              ·
                refine ⟨147310022474037708881527883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98206681649358472587685255 147310022474037708881527883)
                ·
                  refine ⟨220965033711056563322291825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147310022474037708881527883 220965033711056563322291825)
                  ·
                    refine ⟨165723775283292422491718869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220965033711056563322291825 165723775283292422491718869)
                    ·
                      refine ⟨3884150983202166152149661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165723775283292422491718869 3884150983202166152149661)
                      ·
                        rfl

theorem cell23_7564357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_7564357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564357 prefixEnd_7564357 := by exact prefixLift 7564357
  have htrace : WordTrace (prefixWord ++ tailWord_7564357) baseStart_7564357 baseEnd_7564357 := by
    simpa [prefixWord, tailWord_7564357, baseEnd_7564357] using wordTrace_append hprefix tailTrace_7564357
  have hstable : (prefixWord ++ tailWord_7564357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564357).length < 2 ^ (prefixWord ++ tailWord_7564357).sum := by decide
  have hdescent : baseEnd_7564357 < baseStart_7564357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564398 : List Nat := [4, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_7564398 : Nat := 118140960795 + 7564398 * 2 ^ 59
def prefixEnd_7564398 : Nat := 4983230072969 + 3 ^ 40 * 7564398 * 2
def baseEnd_7564398 : Nat := 431574670656555610192997

theorem tailTrace_7564398 : CollatzResearch.WordTrace tailWord_7564398 prefixEnd_7564398 431574670656555610192997 := by
  unfold tailWord_7564398
  simp only [CollatzResearch.WordTrace]
  refine ⟨34487032606185677146298731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183930840566323611446926565 34487032606185677146298731)
  ·
    refine ⟨51730548909278515719448097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34487032606185677146298731 51730548909278515719448097)
    ·
      refine ⟨38797911681958886789586073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51730548909278515719448097 38797911681958886789586073)
      ·
        refine ⟨29098433761469165092189555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38797911681958886789586073 29098433761469165092189555)
        ·
          refine ⟨43647650642203747638284333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29098433761469165092189555 43647650642203747638284333)
          ·
            refine ⟨16367868990826405364356625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43647650642203747638284333 16367868990826405364356625)
            ·
              refine ⟨12275901743119804023267469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16367868990826405364356625 12275901743119804023267469)
              ·
                refine ⟨4603463153669926508725301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12275901743119804023267469 4603463153669926508725301)
                ·
                  refine ⟨431574670656555610192997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4603463153669926508725301 431574670656555610192997)
                  ·
                    rfl

theorem cell23_7564398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_7564398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564398 prefixEnd_7564398 := by exact prefixLift 7564398
  have htrace : WordTrace (prefixWord ++ tailWord_7564398) baseStart_7564398 baseEnd_7564398 := by
    simpa [prefixWord, tailWord_7564398, baseEnd_7564398] using wordTrace_append hprefix tailTrace_7564398
  have hstable : (prefixWord ++ tailWord_7564398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564398).length < 2 ^ (prefixWord ++ tailWord_7564398).sum := by decide
  have hdescent : baseEnd_7564398 < baseStart_7564398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564464 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 3]
def baseStart_7564464 : Nat := 118140960795 + 7564464 * 2 ^ 59
def prefixEnd_7564464 : Nat := 4983230072969 + 3 ^ 40 * 7564464 * 2
def baseEnd_7564464 : Nat := 3884205925632197233511669

theorem tailTrace_7564464 : CollatzResearch.WordTrace tailWord_7564464 prefixEnd_7564464 3884205925632197233511669 := by
  unfold tailWord_7564464
  simp only [CollatzResearch.WordTrace]
  refine ⟨137949334033623155221146223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183932445378164206961528297 137949334033623155221146223)
  ·
    refine ⟨206924001050434732831719335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137949334033623155221146223 206924001050434732831719335)
    ·
      refine ⟨310386001575652099247579003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206924001050434732831719335 310386001575652099247579003)
      ·
        refine ⟨465579002363478148871368505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310386001575652099247579003 465579002363478148871368505)
        ·
          refine ⟨349184251772608611653526379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465579002363478148871368505 349184251772608611653526379)
          ·
            refine ⟨523776377658912917480289569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349184251772608611653526379 523776377658912917480289569)
            ·
              refine ⟨392832283244184688110217177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523776377658912917480289569 392832283244184688110217177)
              ·
                refine ⟨294624212433138516082662883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392832283244184688110217177 294624212433138516082662883)
                ·
                  refine ⟨441936318649707774123994325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294624212433138516082662883 441936318649707774123994325)
                  ·
                    refine ⟨10357882468352525956031117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 441936318649707774123994325 10357882468352525956031117)
                    ·
                      refine ⟨3884205925632197233511669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10357882468352525956031117 3884205925632197233511669)
                      ·
                        rfl

theorem cell23_7564464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_7564464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564464 prefixEnd_7564464 := by exact prefixLift 7564464
  have htrace : WordTrace (prefixWord ++ tailWord_7564464) baseStart_7564464 baseEnd_7564464 := by
    simpa [prefixWord, tailWord_7564464, baseEnd_7564464] using wordTrace_append hprefix tailTrace_7564464
  have hstable : (prefixWord ++ tailWord_7564464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564464).length < 2 ^ (prefixWord ++ tailWord_7564464).sum := by decide
  have hdescent : baseEnd_7564464 < baseStart_7564464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564491 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 1, 5, 2]
def baseStart_7564491 : Nat := 118140960795 + 7564491 * 2 ^ 59
def prefixEnd_7564491 : Nat := 4983230072969 + 3 ^ 40 * 7564491 * 2
def baseEnd_7564491 : Nat := 3884219789609868627874045

theorem tailTrace_7564491 : CollatzResearch.WordTrace tailWord_7564491 prefixEnd_7564491 3884219789609868627874045 := by
  unfold tailWord_7564491
  simp only [CollatzResearch.WordTrace]
  refine ⟨275899652838148494053525327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183933101892098996035683551 275899652838148494053525327)
  ·
    refine ⟨413849479257222741080287991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275899652838148494053525327 413849479257222741080287991)
    ·
      refine ⟨620774218885834111620431987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413849479257222741080287991 620774218885834111620431987)
      ·
        refine ⟨931161328328751167430647981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620774218885834111620431987 931161328328751167430647981)
        ·
          refine ⟨349185498123281687786492993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 931161328328751167430647981 349185498123281687786492993)
          ·
            refine ⟨261889123592461265839869745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349185498123281687786492993 261889123592461265839869745)
            ·
              refine ⟨196416842694345949379902309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261889123592461265839869745 196416842694345949379902309)
              ·
                refine ⟨36828158005189865508731683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196416842694345949379902309 36828158005189865508731683)
                ·
                  refine ⟨55242237007784798263097525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36828158005189865508731683 55242237007784798263097525)
                  ·
                    refine ⟨5178959719479824837165393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55242237007784798263097525 5178959719479824837165393)
                    ·
                      refine ⟨3884219789609868627874045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5178959719479824837165393 3884219789609868627874045)
                      ·
                        rfl

theorem cell23_7564491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 5, 2].length) (baseStart_7564491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564491 prefixEnd_7564491 := by exact prefixLift 7564491
  have htrace : WordTrace (prefixWord ++ tailWord_7564491) baseStart_7564491 baseEnd_7564491 := by
    simpa [prefixWord, tailWord_7564491, baseEnd_7564491] using wordTrace_append hprefix tailTrace_7564491
  have hstable : (prefixWord ++ tailWord_7564491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564491).length < 2 ^ (prefixWord ++ tailWord_7564491).sum := by decide
  have hdescent : baseEnd_7564491 < baseStart_7564491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564498 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_7564498 : Nat := 118140960795 + 7564498 * 2 ^ 59
def prefixEnd_7564498 : Nat := 4983230072969 + 3 ^ 40 * 7564498 * 2
def baseEnd_7564498 : Nat := 3884223383974450100486513

theorem tailTrace_7564498 : CollatzResearch.WordTrace tailWord_7564498 prefixEnd_7564498 3884223383974450100486513 := by
  unfold tailWord_7564498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68974977037280783562257537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183933272099415422832686765 68974977037280783562257537)
  ·
    refine ⟨51731232777960587671693153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68974977037280783562257537 51731232777960587671693153)
    ·
      refine ⟨38798424583470440753769865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51731232777960587671693153 38798424583470440753769865)
      ·
        refine ⟨29098818437602830565327399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38798424583470440753769865 29098818437602830565327399)
        ·
          refine ⟨43648227656404245847991099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29098818437602830565327399 43648227656404245847991099)
          ·
            refine ⟨65472341484606368771986649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43648227656404245847991099 65472341484606368771986649)
            ·
              refine ⟨49104256113454776578989987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65472341484606368771986649 49104256113454776578989987)
              ·
                refine ⟨73656384170182164868484981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49104256113454776578989987 73656384170182164868484981)
                ·
                  refine ⟨6905286015954577956420467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73656384170182164868484981 6905286015954577956420467)
                  ·
                    refine ⟨10357929023931866934630701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6905286015954577956420467 10357929023931866934630701)
                    ·
                      refine ⟨3884223383974450100486513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10357929023931866934630701 3884223383974450100486513)
                      ·
                        rfl

theorem cell23_7564498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_7564498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564498 prefixEnd_7564498 := by exact prefixLift 7564498
  have htrace : WordTrace (prefixWord ++ tailWord_7564498) baseStart_7564498 baseEnd_7564498 := by
    simpa [prefixWord, tailWord_7564498, baseEnd_7564498] using wordTrace_append hprefix tailTrace_7564498
  have hstable : (prefixWord ++ tailWord_7564498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564498).length < 2 ^ (prefixWord ++ tailWord_7564498).sum := by decide
  have hdescent : baseEnd_7564498 < baseStart_7564498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564502 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_7564502 : Nat := 118140960795 + 7564502 * 2 ^ 59
def prefixEnd_7564502 : Nat := 4983230072969 + 3 ^ 40 * 7564502 * 2
def baseEnd_7564502 : Nat := 3884225437897068084836495

theorem tailTrace_7564502 : CollatzResearch.WordTrace tailWord_7564502 prefixEnd_7564502 3884225437897068084836495 := by
  unfold tailWord_7564502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17243753377569290183260985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183933369360739095288117173 17243753377569290183260985)
  ·
    refine ⟨12932815033176967637445739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17243753377569290183260985 12932815033176967637445739)
    ·
      refine ⟨19399222549765451456168609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12932815033176967637445739 19399222549765451456168609)
      ·
        refine ⟨14549416912324088592126457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19399222549765451456168609 14549416912324088592126457)
        ·
          refine ⟨10912062684243066444094843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14549416912324088592126457 10912062684243066444094843)
          ·
            refine ⟨16368094026364599666142265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10912062684243066444094843 16368094026364599666142265)
            ·
              refine ⟨12276070519773449749606699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16368094026364599666142265 12276070519773449749606699)
              ·
                refine ⟨18414105779660174624410049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276070519773449749606699 18414105779660174624410049)
                ·
                  refine ⟨13810579334745130968307537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18414105779660174624410049 13810579334745130968307537)
                  ·
                    refine ⟨10357934501058848226230653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13810579334745130968307537 10357934501058848226230653)
                    ·
                      refine ⟨3884225437897068084836495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10357934501058848226230653 3884225437897068084836495)
                      ·
                        rfl

theorem cell23_7564502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_7564502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564502 prefixEnd_7564502 := by exact prefixLift 7564502
  have htrace : WordTrace (prefixWord ++ tailWord_7564502) baseStart_7564502 baseEnd_7564502 := by
    simpa [prefixWord, tailWord_7564502, baseEnd_7564502] using wordTrace_append hprefix tailTrace_7564502
  have hstable : (prefixWord ++ tailWord_7564502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564502).length < 2 ^ (prefixWord ++ tailWord_7564502).sum := by decide
  have hdescent : baseEnd_7564502 < baseStart_7564502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564525 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_7564525 : Nat := 118140960795 + 7564525 * 2 ^ 59
def prefixEnd_7564525 : Nat := 4983230072969 + 3 ^ 40 * 7564525 * 2
def baseEnd_7564525 : Nat := 3884237247952121494848889

theorem tailTrace_7564525 : CollatzResearch.WordTrace tailWord_7564525 prefixEnd_7564525 3884237247952121494848889 := by
  unfold tailWord_7564525
  simp only [CollatzResearch.WordTrace]
  refine ⟨275900892920025317860263029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183933928613350211906842019 275900892920025317860263029)
  ·
    refine ⟨25865708711252373549399659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275900892920025317860263029 25865708711252373549399659)
    ·
      refine ⟨38798563066878560324099489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25865708711252373549399659 38798563066878560324099489)
      ·
        refine ⟨29098922300158920243074617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38798563066878560324099489 29098922300158920243074617)
        ·
          refine ⟨21824191725119190182305963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29098922300158920243074617 21824191725119190182305963)
          ·
            refine ⟨32736287587678785273458945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21824191725119190182305963 32736287587678785273458945)
            ·
              refine ⟨24552215690759088955094209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32736287587678785273458945 24552215690759088955094209)
              ·
                refine ⟨18414161768069316716320657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24552215690759088955094209 18414161768069316716320657)
                ·
                  refine ⟨13810621326051987537240493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18414161768069316716320657 13810621326051987537240493)
                  ·
                    refine ⟨5178982997269495326465185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13810621326051987537240493 5178982997269495326465185)
                    ·
                      refine ⟨3884237247952121494848889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5178982997269495326465185 3884237247952121494848889)
                      ·
                        rfl

theorem cell23_7564525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_7564525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564525 prefixEnd_7564525 := by exact prefixLift 7564525
  have htrace : WordTrace (prefixWord ++ tailWord_7564525) baseStart_7564525 baseEnd_7564525 := by
    simpa [prefixWord, tailWord_7564525, baseEnd_7564525] using wordTrace_append hprefix tailTrace_7564525
  have hstable : (prefixWord ++ tailWord_7564525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564525).length < 2 ^ (prefixWord ++ tailWord_7564525).sum := by decide
  have hdescent : baseEnd_7564525 < baseStart_7564525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564548 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_7564548 : Nat := 118140960795 + 7564548 * 2 ^ 59
def prefixEnd_7564548 : Nat := 4983230072969 + 3 ^ 40 * 7564548 * 2
def baseEnd_7564548 : Nat := 1294749686002391634953761

theorem tailTrace_7564548 : CollatzResearch.WordTrace tailWord_7564548 prefixEnd_7564548 1294749686002391634953761 := by
  unfold tailWord_7564548
  simp only [CollatzResearch.WordTrace]
  refine ⟨137950865899470996394175149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183934487865961328525566865 137950865899470996394175149)
  ·
    refine ⟨51731574712301623647815681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137950865899470996394175149 51731574712301623647815681)
    ·
      refine ⟨38798681034226217735861761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51731574712301623647815681 38798681034226217735861761)
      ·
        refine ⟨29099010775669663301896321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38798681034226217735861761 29099010775669663301896321)
        ·
          refine ⟨21824258081752247476422241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29099010775669663301896321 21824258081752247476422241)
          ·
            refine ⟨16368193561314185607316681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21824258081752247476422241 16368193561314185607316681)
            ·
              refine ⟨12276145170985639205487511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16368193561314185607316681 12276145170985639205487511)
              ·
                refine ⟨18414217756478458808231267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276145170985639205487511 18414217756478458808231267)
                ·
                  refine ⟨27621326634717688212346901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18414217756478458808231267 27621326634717688212346901)
                  ·
                    refine ⟨1294749686002391634953761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27621326634717688212346901 1294749686002391634953761)
                    ·
                      rfl

theorem cell23_7564548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_7564548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564548 prefixEnd_7564548 := by exact prefixLift 7564548
  have htrace : WordTrace (prefixWord ++ tailWord_7564548) baseStart_7564548 baseEnd_7564548 := by
    simpa [prefixWord, tailWord_7564548, baseEnd_7564548] using wordTrace_append hprefix tailTrace_7564548
  have hstable : (prefixWord ++ tailWord_7564548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564548).length < 2 ^ (prefixWord ++ tailWord_7564548).sum := by decide
  have hdescent : baseEnd_7564548 < baseStart_7564548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564555 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 3, 2, 2]
def baseStart_7564555 : Nat := 118140960795 + 7564555 * 2 ^ 59
def prefixEnd_7564555 : Nat := 4983230072969 + 3 ^ 40 * 7564555 * 2
def baseEnd_7564555 : Nat := 3884252652371756377473751

theorem tailTrace_7564555 : CollatzResearch.WordTrace tailWord_7564555 prefixEnd_7564555 3884252652371756377473751 := by
  unfold tailWord_7564555
  simp only [CollatzResearch.WordTrace]
  refine ⟨275901987109916632983855119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183934658073277755322570079 275901987109916632983855119)
  ·
    refine ⟨413852980664874949475782679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275901987109916632983855119 413852980664874949475782679)
    ·
      refine ⟨620779470997312424213674019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413852980664874949475782679 620779470997312424213674019)
      ·
        refine ⟨931169206495968636320511029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620779470997312424213674019 931169206495968636320511029)
        ·
          refine ⟨87297113108997059655047909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 931169206495968636320511029 87297113108997059655047909)
          ·
            refine ⟨16368208707936948685321483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87297113108997059655047909 16368208707936948685321483)
            ·
              refine ⟨24552313061905423027982225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16368208707936948685321483 24552313061905423027982225)
              ·
                refine ⟨18414234796429067270986669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24552313061905423027982225 18414234796429067270986669)
                ·
                  refine ⟨6905338048660900226620001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18414234796429067270986669 6905338048660900226620001)
                  ·
                    refine ⟨5179003536495675169965001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905338048660900226620001 5179003536495675169965001)
                    ·
                      refine ⟨3884252652371756377473751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179003536495675169965001 3884252652371756377473751)
                      ·
                        rfl

theorem cell23_7564555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 2, 2].length) (baseStart_7564555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564555 prefixEnd_7564555 := by exact prefixLift 7564555
  have htrace : WordTrace (prefixWord ++ tailWord_7564555) baseStart_7564555 baseEnd_7564555 := by
    simpa [prefixWord, tailWord_7564555, baseEnd_7564555] using wordTrace_append hprefix tailTrace_7564555
  have hstable : (prefixWord ++ tailWord_7564555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564555).length < 2 ^ (prefixWord ++ tailWord_7564555).sum := by decide
  have hdescent : baseEnd_7564555 < baseStart_7564555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564558 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_7564558 : Nat := 118140960795 + 7564558 * 2 ^ 59
def prefixEnd_7564558 : Nat := 4983230072969 + 3 ^ 40 * 7564558 * 2
def baseEnd_7564558 : Nat := 3884254192813719865736237

theorem tailTrace_7564558 : CollatzResearch.WordTrace tailWord_7564558 prefixEnd_7564558 3884254192813719865736237 := by
  unfold tailWord_7564558
  simp only [CollatzResearch.WordTrace]
  refine ⟨34487762066113220562026791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183934731019270509664142885 34487762066113220562026791)
  ·
    refine ⟨51731643099169830843040187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34487762066113220562026791 51731643099169830843040187)
    ·
      refine ⟨77597464648754746264560281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51731643099169830843040187 77597464648754746264560281)
      ·
        refine ⟨58198098486566059698420211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77597464648754746264560281 58198098486566059698420211)
        ·
          refine ⟨87297147729849089547630317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58198098486566059698420211 87297147729849089547630317)
          ·
            refine ⟨32736430398693408580361369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87297147729849089547630317 32736430398693408580361369)
            ·
              refine ⟨24552322799020056435271027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32736430398693408580361369 24552322799020056435271027)
              ·
                refine ⟨36828484198530084652906541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24552322799020056435271027 36828484198530084652906541)
                ·
                  refine ⟨13810681574448781744839953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36828484198530084652906541 13810681574448781744839953)
                  ·
                    refine ⟨10358011180836586308629965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13810681574448781744839953 10358011180836586308629965)
                    ·
                      refine ⟨3884254192813719865736237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10358011180836586308629965 3884254192813719865736237)
                      ·
                        rfl

theorem cell23_7564558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_7564558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564558 prefixEnd_7564558 := by exact prefixLift 7564558
  have htrace : WordTrace (prefixWord ++ tailWord_7564558) baseStart_7564558 baseEnd_7564558 := by
    simpa [prefixWord, tailWord_7564558, baseEnd_7564558] using wordTrace_append hprefix tailTrace_7564558
  have hstable : (prefixWord ++ tailWord_7564558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564558).length < 2 ^ (prefixWord ++ tailWord_7564558).sum := by decide
  have hdescent : baseEnd_7564558 < baseStart_7564558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564561 : List Nat := [1, 2, 2, 1, 1, 4, 5, 7]
def baseStart_7564561 : Nat := 118140960795 + 7564561 * 2 ^ 59
def prefixEnd_7564561 : Nat := 4983230072969 + 3 ^ 40 * 7564561 * 2
def baseEnd_7564561 : Nat := 143861323453914198296249

theorem tailTrace_7564561 : CollatzResearch.WordTrace tailWord_7564561 prefixEnd_7564561 143861323453914198296249 := by
  unfold tailWord_7564561
  simp only [CollatzResearch.WordTrace]
  refine ⟨275902205947894896008573537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183934803965263264005715691 275902205947894896008573537)
  ·
    refine ⟨206926654460921172006430153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275902205947894896008573537 206926654460921172006430153)
    ·
      refine ⟨155194990845690879004822615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206926654460921172006430153 155194990845690879004822615)
      ·
        refine ⟨232792486268536318507233923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155194990845690879004822615 232792486268536318507233923)
        ·
          refine ⟨349188729402804477760850885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232792486268536318507233923 349188729402804477760850885)
          ·
            refine ⟨65472886763025839580159541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349188729402804477760850885 65472886763025839580159541)
            ·
              refine ⟨6138083134033672460639957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65472886763025839580159541 6138083134033672460639957)
              ·
                refine ⟨143861323453914198296249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6138083134033672460639957 143861323453914198296249)
                ·
                  rfl

theorem cell23_7564561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 7].length) (baseStart_7564561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564561 prefixEnd_7564561 := by exact prefixLift 7564561
  have htrace : WordTrace (prefixWord ++ tailWord_7564561) baseStart_7564561 baseEnd_7564561 := by
    simpa [prefixWord, tailWord_7564561, baseEnd_7564561] using wordTrace_append hprefix tailTrace_7564561
  have hstable : (prefixWord ++ tailWord_7564561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564561).length < 2 ^ (prefixWord ++ tailWord_7564561).sum := by decide
  have hdescent : baseEnd_7564561 < baseStart_7564561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564572 : List Nat := [2, 2, 3, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_7564572 : Nat := 118140960795 + 7564572 * 2 ^ 59
def prefixEnd_7564572 : Nat := 4983230072969 + 3 ^ 40 * 7564572 * 2
def baseEnd_7564572 : Nat := 3884261381542882810961173

theorem tailTrace_7564572 : CollatzResearch.WordTrace tailWord_7564572 prefixEnd_7564572 3884261381542882810961173 := by
  unfold tailWord_7564572
  simp only [CollatzResearch.WordTrace]
  refine ⟨137951303575427522443611985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183935071433903363258149313 137951303575427522443611985)
  ·
    refine ⟨103463477681570641832708989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137951303575427522443611985 103463477681570641832708989)
    ·
      refine ⟨38798804130588990687265871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103463477681570641832708989 38798804130588990687265871)
      ·
        refine ⟨58198206195883486030898807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38798804130588990687265871 58198206195883486030898807)
        ·
          refine ⟨87297309293825229046348211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58198206195883486030898807 87297309293825229046348211)
          ·
            refine ⟨130945963940737843569522317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87297309293825229046348211 130945963940737843569522317)
            ·
              refine ⟨49104736477776691338570869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130945963940737843569522317 49104736477776691338570869)
              ·
                refine ⟨4603569044791564812991019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49104736477776691338570869 4603569044791564812991019)
                ·
                  refine ⟨6905353567187347219486529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603569044791564812991019 6905353567187347219486529)
                  ·
                    refine ⟨5179015175390510414614897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905353567187347219486529 5179015175390510414614897)
                    ·
                      refine ⟨3884261381542882810961173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179015175390510414614897 3884261381542882810961173)
                      ·
                        rfl

theorem cell23_7564572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_7564572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564572 prefixEnd_7564572 := by exact prefixLift 7564572
  have htrace : WordTrace (prefixWord ++ tailWord_7564572) baseStart_7564572 baseEnd_7564572 := by
    simpa [prefixWord, tailWord_7564572, baseEnd_7564572] using wordTrace_append hprefix tailTrace_7564572
  have hstable : (prefixWord ++ tailWord_7564572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564572).length < 2 ^ (prefixWord ++ tailWord_7564572).sum := by decide
  have hdescent : baseEnd_7564572 < baseStart_7564572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564575 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 3]
def baseStart_7564575 : Nat := 118140960795 + 7564575 * 2 ^ 59
def prefixEnd_7564575 : Nat := 4983230072969 + 3 ^ 40 * 7564575 * 2
def baseEnd_7564575 : Nat := 3884262921984846299223659

theorem tailTrace_7564575 : CollatzResearch.WordTrace tailWord_7564575 prefixEnd_7564575 3884262921984846299223659 := by
  unfold tailWord_7564575
  simp only [CollatzResearch.WordTrace]
  refine ⟨275902716569844176399583179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183935144379896117599722119 275902716569844176399583179)
  ·
    refine ⟨413854074854766264599374769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275902716569844176399583179 413854074854766264599374769)
    ·
      refine ⟨310390556141074698449531077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413854074854766264599374769 310390556141074698449531077)
      ·
        refine ⟨58198229276451505959287077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310390556141074698449531077 58198229276451505959287077)
        ·
          refine ⟨10912167989334657367366327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58198229276451505959287077 10912167989334657367366327)
          ·
            refine ⟨16368251984001986051049491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10912167989334657367366327 16368251984001986051049491)
            ·
              refine ⟨24552377976002979076574237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16368251984001986051049491 24552377976002979076574237)
              ·
                refine ⟨9207141741001117153715339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24552377976002979076574237 9207141741001117153715339)
                ·
                  refine ⟨13810712611501675730573009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9207141741001117153715339 13810712611501675730573009)
                  ·
                    refine ⟨10358034458626256797929757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13810712611501675730573009 10358034458626256797929757)
                    ·
                      refine ⟨3884262921984846299223659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10358034458626256797929757 3884262921984846299223659)
                      ·
                        rfl

theorem cell23_7564575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_7564575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564575 prefixEnd_7564575 := by exact prefixLift 7564575
  have htrace : WordTrace (prefixWord ++ tailWord_7564575) baseStart_7564575 baseEnd_7564575 := by
    simpa [prefixWord, tailWord_7564575, baseEnd_7564575] using wordTrace_append hprefix tailTrace_7564575
  have hstable : (prefixWord ++ tailWord_7564575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564575).length < 2 ^ (prefixWord ++ tailWord_7564575).sum := by decide
  have hdescent : baseEnd_7564575 < baseStart_7564575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564589 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_7564589 : Nat := 118140960795 + 7564589 * 2 ^ 59
def prefixEnd_7564589 : Nat := 4983230072969 + 3 ^ 40 * 7564589 * 2
def baseEnd_7564589 : Nat := 3884270110714009244448595

theorem tailTrace_7564589 : CollatzResearch.WordTrace tailWord_7564589 prefixEnd_7564589 3884270110714009244448595 := by
  unfold tailWord_7564589
  simp only [CollatzResearch.WordTrace]
  refine ⟨275903227191793456790592821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183935484794528971193728547 275903227191793456790592821)
  ·
    refine ⟨25865927549230636574118077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275903227191793456790592821 25865927549230636574118077)
    ·
      refine ⟨9699722830961488715294279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25865927549230636574118077 9699722830961488715294279)
      ·
        refine ⟨14549584246442233072941419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9699722830961488715294279 14549584246442233072941419)
        ·
          refine ⟨21824376369663349609412129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14549584246442233072941419 21824376369663349609412129)
          ·
            refine ⟨16368282277247512207059097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21824376369663349609412129 16368282277247512207059097)
            ·
              refine ⟨12276211707935634155294323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16368282277247512207059097 12276211707935634155294323)
              ·
                refine ⟨18414317561903451232941485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276211707935634155294323 18414317561903451232941485)
                ·
                  refine ⟨6905369085713794212353057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18414317561903451232941485 6905369085713794212353057)
                  ·
                    refine ⟨5179026814285345659264793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905369085713794212353057 5179026814285345659264793)
                    ·
                      refine ⟨3884270110714009244448595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179026814285345659264793 3884270110714009244448595)
                      ·
                        rfl

theorem cell23_7564589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_7564589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564589 prefixEnd_7564589 := by exact prefixLift 7564589
  have htrace : WordTrace (prefixWord ++ tailWord_7564589) baseStart_7564589 baseEnd_7564589 := by
    simpa [prefixWord, tailWord_7564589, baseEnd_7564589] using wordTrace_append hprefix tailTrace_7564589
  have hstable : (prefixWord ++ tailWord_7564589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564589).length < 2 ^ (prefixWord ++ tailWord_7564589).sum := by decide
  have hdescent : baseEnd_7564589 < baseStart_7564589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564615 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_7564615 : Nat := 118140960795 + 7564615 * 2 ^ 59
def prefixEnd_7564615 : Nat := 4983230072969 + 3 ^ 40 * 7564615 * 2
def baseEnd_7564615 : Nat := 3884283461211026142723475

theorem tailTrace_7564615 : CollatzResearch.WordTrace tailWord_7564615 prefixEnd_7564615 3884283461211026142723475 := by
  unfold tailWord_7564615
  simp only [CollatzResearch.WordTrace]
  refine ⟨275904175489699263231039299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183936116993132842154026199 275904175489699263231039299)
  ·
    refine ⟨413856263234548894846558949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275904175489699263231039299 413856263234548894846558949)
    ·
      refine ⟨77598049356477917783729803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413856263234548894846558949 77598049356477917783729803)
      ·
        refine ⟨116397074034716876675594705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77598049356477917783729803 116397074034716876675594705)
        ·
          refine ⟨87297805526037657506696029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116397074034716876675594705 87297805526037657506696029)
          ·
            refine ⟨32736677072264121565011011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87297805526037657506696029 32736677072264121565011011)
            ·
              refine ⟨49105015608396182347516517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32736677072264121565011011 49105015608396182347516517)
              ·
                refine ⟨9207190426574284190159347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49105015608396182347516517 9207190426574284190159347)
                ·
                  refine ⟨13810785639861426285239021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9207190426574284190159347 13810785639861426285239021)
                  ·
                    refine ⟨5179044614948034856964633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13810785639861426285239021 5179044614948034856964633)
                    ·
                      refine ⟨3884283461211026142723475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179044614948034856964633 3884283461211026142723475)
                      ·
                        rfl

theorem cell23_7564615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_7564615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564615 prefixEnd_7564615 := by exact prefixLift 7564615
  have htrace : WordTrace (prefixWord ++ tailWord_7564615) baseStart_7564615 baseEnd_7564615 := by
    simpa [prefixWord, tailWord_7564615, baseEnd_7564615] using wordTrace_append hprefix tailTrace_7564615
  have hstable : (prefixWord ++ tailWord_7564615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564615).length < 2 ^ (prefixWord ++ tailWord_7564615).sum := by decide
  have hdescent : baseEnd_7564615 < baseStart_7564615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564631 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_7564631 : Nat := 118140960795 + 7564631 * 2 ^ 59
def prefixEnd_7564631 : Nat := 4983230072969 + 3 ^ 40 * 7564631 * 2
def baseEnd_7564631 : Nat := 3884291676901498080123401

theorem tailTrace_7564631 : CollatzResearch.WordTrace tailWord_7564631 prefixEnd_7564631 3884291676901498080123401 := by
  unfold tailWord_7564631
  simp only [CollatzResearch.WordTrace]
  refine ⟨275904759057641297963621747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183936506038427531975747831 275904759057641297963621747)
  ·
    refine ⟨413857138586461946945432621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275904759057641297963621747 413857138586461946945432621)
    ·
      refine ⟨155196426969923230104537233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413857138586461946945432621 155196426969923230104537233)
      ·
        refine ⟨116397320227442422578402925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155196426969923230104537233 116397320227442422578402925)
        ·
          refine ⟨43648995085290908466901097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116397320227442422578402925 43648995085290908466901097)
          ·
            refine ⟨32736746313968181350175823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43648995085290908466901097 32736746313968181350175823)
            ·
              refine ⟨49105119470952272025263735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32736746313968181350175823 49105119470952272025263735)
              ·
                refine ⟨73657679206428408037895603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49105119470952272025263735 73657679206428408037895603)
                ·
                  refine ⟨110486518809642612056843405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73657679206428408037895603 110486518809642612056843405)
                  ·
                    refine ⟨41432444553615979521316277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110486518809642612056843405 41432444553615979521316277)
                    ·
                      refine ⟨3884291676901498080123401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41432444553615979521316277 3884291676901498080123401)
                      ·
                        rfl

theorem cell23_7564631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_7564631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564631 prefixEnd_7564631 := by exact prefixLift 7564631
  have htrace : WordTrace (prefixWord ++ tailWord_7564631) baseStart_7564631 baseEnd_7564631 := by
    simpa [prefixWord, tailWord_7564631, baseEnd_7564631] using wordTrace_append hprefix tailTrace_7564631
  have hstable : (prefixWord ++ tailWord_7564631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564631).length < 2 ^ (prefixWord ++ tailWord_7564631).sum := by decide
  have hdescent : baseEnd_7564631 < baseStart_7564631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564641 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_7564641 : Nat := 118140960795 + 7564641 * 2 ^ 59
def prefixEnd_7564641 : Nat := 4983230072969 + 3 ^ 40 * 7564641 * 2
def baseEnd_7564641 : Nat := 3884296811708043040998355

theorem tailTrace_7564641 : CollatzResearch.WordTrace tailWord_7564641 prefixEnd_7564641 3884296811708043040998355 := by
  unfold tailWord_7564641
  simp only [CollatzResearch.WordTrace]
  refine ⟨275905123787605069671485777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183936749191736713114323851 275905123787605069671485777)
  ·
    refine ⟨206928842840703802253614333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275905123787605069671485777 206928842840703802253614333)
    ·
      refine ⟨77598316065263925845105375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206928842840703802253614333 77598316065263925845105375)
      ·
        refine ⟨116397474097895888767658063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77598316065263925845105375 116397474097895888767658063)
        ·
          refine ⟨174596211146843833151487095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116397474097895888767658063 174596211146843833151487095)
          ·
            refine ⟨261894316720265749727230643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174596211146843833151487095 261894316720265749727230643)
            ·
              refine ⟨392841475080398624590845965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261894316720265749727230643 392841475080398624590845965)
              ·
                refine ⟨147315553155149484221567237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392841475080398624590845965 147315553155149484221567237)
                ·
                  refine ⟨27621666216590528291543857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147315553155149484221567237 27621666216590528291543857)
                  ·
                    refine ⟨20716249662442896218657893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27621666216590528291543857 20716249662442896218657893)
                    ·
                      refine ⟨3884296811708043040998355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20716249662442896218657893 3884296811708043040998355)
                      ·
                        rfl

theorem cell23_7564641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_7564641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564641 prefixEnd_7564641 := by exact prefixLift 7564641
  have htrace : WordTrace (prefixWord ++ tailWord_7564641) baseStart_7564641 baseEnd_7564641 := by
    simpa [prefixWord, tailWord_7564641, baseEnd_7564641] using wordTrace_append hprefix tailTrace_7564641
  have hstable : (prefixWord ++ tailWord_7564641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564641).length < 2 ^ (prefixWord ++ tailWord_7564641).sum := by decide
  have hdescent : baseEnd_7564641 < baseStart_7564641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564645 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 4, 2, 2]
def baseStart_7564645 : Nat := 118140960795 + 7564645 * 2 ^ 59
def prefixEnd_7564645 : Nat := 4983230072969 + 3 ^ 40 * 7564645 * 2
def baseEnd_7564645 : Nat := 3884298865630661025348337

theorem tailTrace_7564645 : CollatzResearch.WordTrace tailWord_7564645 prefixEnd_7564645 3884298865630661025348337 := by
  unfold tailWord_7564645
  simp only [CollatzResearch.WordTrace]
  refine ⟨275905269679590578354631389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183936846453060385569754259 275905269679590578354631389)
  ·
    refine ⟨103464476129846466882986771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275905269679590578354631389 103464476129846466882986771)
    ·
      refine ⟨155196714194769700324480157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103464476129846466882986771 155196714194769700324480157)
      ·
        refine ⟨58198767823038637621680059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155196714194769700324480157 58198767823038637621680059)
        ·
          refine ⟨87298151734557956432520089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58198767823038637621680059 87298151734557956432520089)
          ·
            refine ⟨65473613800918467324390067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87298151734557956432520089 65473613800918467324390067)
            ·
              refine ⟨98210420701377700986585101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65473613800918467324390067 98210420701377700986585101)
              ·
                refine ⟨36828907763016637869969413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98210420701377700986585101 36828907763016637869969413)
                ·
                  refine ⟨6905420205565619600619265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36828907763016637869969413 6905420205565619600619265)
                  ·
                    refine ⟨5179065154174214700464449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905420205565619600619265 5179065154174214700464449)
                    ·
                      refine ⟨3884298865630661025348337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179065154174214700464449 3884298865630661025348337)
                      ·
                        rfl

theorem cell23_7564645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_7564645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564645 prefixEnd_7564645 := by exact prefixLift 7564645
  have htrace : WordTrace (prefixWord ++ tailWord_7564645) baseStart_7564645 baseEnd_7564645 := by
    simpa [prefixWord, tailWord_7564645, baseEnd_7564645] using wordTrace_append hprefix tailTrace_7564645
  have hstable : (prefixWord ++ tailWord_7564645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564645).length < 2 ^ (prefixWord ++ tailWord_7564645).sum := by decide
  have hdescent : baseEnd_7564645 < baseStart_7564645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564698 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_7564698 : Nat := 118140960795 + 7564698 * 2 ^ 59
def prefixEnd_7564698 : Nat := 4983230072969 + 3 ^ 40 * 7564698 * 2
def baseEnd_7564698 : Nat := 1294775360035116439328531

theorem tailTrace_7564698 : CollatzResearch.WordTrace tailWord_7564698 prefixEnd_7564698 1294775360035116439328531 := by
  unfold tailWord_7564698
  simp only [CollatzResearch.WordTrace]
  refine ⟨68976800687099642101577687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183938135165599045604207165 68976800687099642101577687)
  ·
    refine ⟨103465201030649463152366531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68976800687099642101577687 103465201030649463152366531)
    ·
      refine ⟨155197801545974194728549797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103465201030649463152366531 155197801545974194728549797)
      ·
        refine ⟨29099587789870161511603087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155197801545974194728549797 29099587789870161511603087)
        ·
          refine ⟨43649381684805242267404631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29099587789870161511603087 43649381684805242267404631)
          ·
            refine ⟨65474072527207863401106947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43649381684805242267404631 65474072527207863401106947)
            ·
              refine ⟨98211108790811795101660421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65474072527207863401106947 98211108790811795101660421)
              ·
                refine ⟨18414582898277211581561329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98211108790811795101660421 18414582898277211581561329)
                ·
                  refine ⟨13810937173707908686170997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18414582898277211581561329 13810937173707908686170997)
                  ·
                    refine ⟨1294775360035116439328531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13810937173707908686170997 1294775360035116439328531)
                    ·
                      rfl

theorem cell23_7564698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_7564698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564698 prefixEnd_7564698 := by exact prefixLift 7564698
  have htrace : WordTrace (prefixWord ++ tailWord_7564698) baseStart_7564698 baseEnd_7564698 := by
    simpa [prefixWord, tailWord_7564698, baseEnd_7564698] using wordTrace_append hprefix tailTrace_7564698
  have hstable : (prefixWord ++ tailWord_7564698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564698).length < 2 ^ (prefixWord ++ tailWord_7564698).sum := by decide
  have hdescent : baseEnd_7564698 < baseStart_7564698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564712 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_7564712 : Nat := 118140960795 + 7564712 * 2 ^ 59
def prefixEnd_7564712 : Nat := 4983230072969 + 3 ^ 40 * 7564712 * 2
def baseEnd_7564712 : Nat := 3884333268834512263210529

theorem tailTrace_7564712 : CollatzResearch.WordTrace tailWord_7564712 prefixEnd_7564712 3884333268834512263210529 := by
  unfold tailWord_7564712
  simp only [CollatzResearch.WordTrace]
  refine ⟨137953856685173924398660195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183938475580231899198213593 137953856685173924398660195)
  ·
    refine ⟨206930785027760886597990293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137953856685173924398660195 206930785027760886597990293)
    ·
      refine ⟨9699880548176291559280795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206930785027760886597990293 9699880548176291559280795)
      ·
        refine ⟨14549820822264437338921193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9699880548176291559280795 14549820822264437338921193)
        ·
          refine ⟨10912365616698328004190895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14549820822264437338921193 10912365616698328004190895)
          ·
            refine ⟨16368548425047492006286343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10912365616698328004190895 16368548425047492006286343)
            ·
              refine ⟨24552822637571238009429515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16368548425047492006286343 24552822637571238009429515)
              ·
                refine ⟨36829233956356857014144273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24552822637571238009429515 36829233956356857014144273)
                ·
                  refine ⟨27621925467267642760608205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36829233956356857014144273 27621925467267642760608205)
                  ·
                    refine ⟨10358222050225366035228077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27621925467267642760608205 10358222050225366035228077)
                    ·
                      refine ⟨3884333268834512263210529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10358222050225366035228077 3884333268834512263210529)
                      ·
                        rfl

theorem cell23_7564712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_7564712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564712 prefixEnd_7564712 := by exact prefixLift 7564712
  have htrace : WordTrace (prefixWord ++ tailWord_7564712) baseStart_7564712 baseEnd_7564712 := by
    simpa [prefixWord, tailWord_7564712, baseEnd_7564712] using wordTrace_append hprefix tailTrace_7564712
  have hstable : (prefixWord ++ tailWord_7564712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564712).length < 2 ^ (prefixWord ++ tailWord_7564712).sum := by decide
  have hdescent : baseEnd_7564712 < baseStart_7564712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564728 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 5, 4]
def baseStart_7564728 : Nat := 118140960795 + 7564728 * 2 ^ 59
def prefixEnd_7564728 : Nat := 4983230072969 + 3 ^ 40 * 7564728 * 2
def baseEnd_7564728 : Nat := 1294780494841661400203485

theorem tailTrace_7564728 : CollatzResearch.WordTrace tailWord_7564728 prefixEnd_7564728 1294780494841661400203485 := by
  unfold tailWord_7564728
  simp only [CollatzResearch.WordTrace]
  refine ⟨137954148469144941764951419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183938864625526589019935225 137954148469144941764951419)
  ·
    refine ⟨206931222703717412647427129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137954148469144941764951419 206931222703717412647427129)
    ·
      refine ⟨155198417027788059485570347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206931222703717412647427129 155198417027788059485570347)
      ·
        refine ⟨232797625541682089228355521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155198417027788059485570347 232797625541682089228355521)
        ·
          refine ⟨174598219156261566921266641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232797625541682089228355521 174598219156261566921266641)
          ·
            refine ⟨130948664367196175190949981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174598219156261566921266641 130948664367196175190949981)
            ·
              refine ⟨49105749137698565696606243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130948664367196175190949981 49105749137698565696606243)
              ·
                refine ⟨73658623706547848544909365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49105749137698565696606243 73658623706547848544909365)
                ·
                  refine ⟨6905495972488860801085253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73658623706547848544909365 6905495972488860801085253)
                  ·
                    refine ⟨1294780494841661400203485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6905495972488860801085253 1294780494841661400203485)
                    ·
                      rfl

theorem cell23_7564728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_7564728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564728 prefixEnd_7564728 := by exact prefixLift 7564728
  have htrace : WordTrace (prefixWord ++ tailWord_7564728) baseStart_7564728 baseEnd_7564728 := by
    simpa [prefixWord, tailWord_7564728, baseEnd_7564728] using wordTrace_append hprefix tailTrace_7564728
  have hstable : (prefixWord ++ tailWord_7564728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564728).length < 2 ^ (prefixWord ++ tailWord_7564728).sum := by decide
  have hdescent : baseEnd_7564728 < baseStart_7564728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564732 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_7564732 : Nat := 118140960795 + 7564732 * 2 ^ 59
def prefixEnd_7564732 : Nat := 4983230072969 + 3 ^ 40 * 7564732 * 2
def baseEnd_7564732 : Nat := 1294781179482534061653479

theorem tailTrace_7564732 : CollatzResearch.WordTrace tailWord_7564732 prefixEnd_7564732 1294781179482534061653479 := by
  unfold tailWord_7564732
  simp only [CollatzResearch.WordTrace]
  refine ⟨137954221415137696106524225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183938961886850261475365633 137954221415137696106524225)
  ·
    refine ⟨103465666061353272079893169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137954221415137696106524225 103465666061353272079893169)
    ·
      refine ⟨77599249546014954059919877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103465666061353272079893169 77599249546014954059919877)
      ·
        refine ⟨14549859289877803886234977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77599249546014954059919877 14549859289877803886234977)
        ·
          refine ⟨10912394467408352914676233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14549859289877803886234977 10912394467408352914676233)
          ·
            refine ⟨8184295850556264686007175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10912394467408352914676233 8184295850556264686007175)
            ·
              refine ⟨12276443775834397029010763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8184295850556264686007175 12276443775834397029010763)
              ·
                refine ⟨18414665663751595543516145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276443775834397029010763 18414665663751595543516145)
                ·
                  refine ⟨13810999247813696657637109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18414665663751595543516145 13810999247813696657637109)
                  ·
                    refine ⟨1294781179482534061653479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13810999247813696657637109 1294781179482534061653479)
                    ·
                      rfl

theorem cell23_7564732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_7564732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564732 prefixEnd_7564732 := by exact prefixLift 7564732
  have htrace : WordTrace (prefixWord ++ tailWord_7564732) baseStart_7564732 baseEnd_7564732 := by
    simpa [prefixWord, tailWord_7564732, baseEnd_7564732] using wordTrace_append hprefix tailTrace_7564732
  have hstable : (prefixWord ++ tailWord_7564732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564732).length < 2 ^ (prefixWord ++ tailWord_7564732).sum := by decide
  have hdescent : baseEnd_7564732 < baseStart_7564732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564748 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7564748 : Nat := 118140960795 + 7564748 * 2 ^ 59
def prefixEnd_7564748 : Nat := 4983230072969 + 3 ^ 40 * 7564748 * 2
def baseEnd_7564748 : Nat := 3884351754138074122360363

theorem tailTrace_7564748 : CollatzResearch.WordTrace tailWord_7564748 prefixEnd_7564748 3884351754138074122360363 := by
  unfold tailWord_7564748
  simp only [CollatzResearch.WordTrace]
  refine ⟨137954513199108713472815449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183939350932144951297087265 137954513199108713472815449)
  ·
    refine ⟨103465884899331535104611587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137954513199108713472815449 103465884899331535104611587)
    ·
      refine ⟨155198827348997302656917381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103465884899331535104611587 155198827348997302656917381)
      ·
        refine ⟨29099780127936994248172009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155198827348997302656917381 29099780127936994248172009)
        ·
          refine ⟨21824835095952745686129007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29099780127936994248172009 21824835095952745686129007)
          ·
            refine ⟨32737252643929118529193511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21824835095952745686129007 32737252643929118529193511)
            ·
              refine ⟨49105878965893677793790267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32737252643929118529193511 49105878965893677793790267)
              ·
                refine ⟨73658818448840516690685401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49105878965893677793790267 73658818448840516690685401)
                ·
                  refine ⟨55244113836630387518014051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73658818448840516690685401 55244113836630387518014051)
                  ·
                    refine ⟨82866170754945581277021077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55244113836630387518014051 82866170754945581277021077)
                    ·
                      refine ⟨3884351754138074122360363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82866170754945581277021077 3884351754138074122360363)
                      ·
                        rfl

theorem cell23_7564748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7564748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564748 prefixEnd_7564748 := by exact prefixLift 7564748
  have htrace : WordTrace (prefixWord ++ tailWord_7564748) baseStart_7564748 baseEnd_7564748 := by
    simpa [prefixWord, tailWord_7564748, baseEnd_7564748] using wordTrace_append hprefix tailTrace_7564748
  have hstable : (prefixWord ++ tailWord_7564748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564748).length < 2 ^ (prefixWord ++ tailWord_7564748).sum := by decide
  have hdescent : baseEnd_7564748 < baseStart_7564748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564762 : List Nat := [3, 1, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_7564762 : Nat := 118140960795 + 7564762 * 2 ^ 59
def prefixEnd_7564762 : Nat := 4983230072969 + 3 ^ 40 * 7564762 * 2
def baseEnd_7564762 : Nat := 1294786314289079022528433

theorem tailTrace_7564762 : CollatzResearch.WordTrace tailWord_7564762 prefixEnd_7564762 1294786314289079022528433 := by
  unfold tailWord_7564762
  simp only [CollatzResearch.WordTrace]
  refine ⟨68977384255041676834160135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183939691346777804891093693 68977384255041676834160135)
  ·
    refine ⟨103466076382562515251240203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68977384255041676834160135 103466076382562515251240203)
    ·
      refine ⟨155199114573843772876860305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103466076382562515251240203 155199114573843772876860305)
      ·
        refine ⟨116399335930382829657645229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155199114573843772876860305 116399335930382829657645229)
        ·
          refine ⟨43649750973893561121616961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116399335930382829657645229 43649750973893561121616961)
          ·
            refine ⟨32737313230420170841212721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43649750973893561121616961 32737313230420170841212721)
            ·
              refine ⟨24552984922815128130909541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32737313230420170841212721 24552984922815128130909541)
              ·
                refine ⟨4603684673027836524545539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24552984922815128130909541 4603684673027836524545539)
                ·
                  refine ⟨6905527009541754786818309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603684673027836524545539 6905527009541754786818309)
                  ·
                    refine ⟨1294786314289079022528433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6905527009541754786818309 1294786314289079022528433)
                    ·
                      rfl

theorem cell23_7564762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_7564762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564762 prefixEnd_7564762 := by exact prefixLift 7564762
  have htrace : WordTrace (prefixWord ++ tailWord_7564762) baseStart_7564762 baseEnd_7564762 := by
    simpa [prefixWord, tailWord_7564762, baseEnd_7564762] using wordTrace_append hprefix tailTrace_7564762
  have hstable : (prefixWord ++ tailWord_7564762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564762).length < 2 ^ (prefixWord ++ tailWord_7564762).sum := by decide
  have hdescent : baseEnd_7564762 < baseStart_7564762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564813 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7564813 : Nat := 118140960795 + 7564813 * 2 ^ 59
def prefixEnd_7564813 : Nat := 4983230072969 + 3 ^ 40 * 7564813 * 2
def baseEnd_7564813 : Nat := 1294795043460205456015855

theorem tailTrace_7564813 : CollatzResearch.WordTrace tailWord_7564813 prefixEnd_7564813 1294795043460205456015855 := by
  unfold tailWord_7564813
  simp only [CollatzResearch.WordTrace]
  refine ⟨275911397142981943046747093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183940931428654628697831395 275911397142981943046747093)
  ·
    refine ⟨6466673370538639290158135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 275911397142981943046747093 6466673370538639290158135)
    ·
      refine ⟨9700010055807958935237203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6466673370538639290158135 9700010055807958935237203)
      ·
        refine ⟨14550015083711938402855805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9700010055807958935237203 14550015083711938402855805)
        ·
          refine ⟨5456255656391976901070927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14550015083711938402855805 5456255656391976901070927)
          ·
            refine ⟨8184383484587965351606391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456255656391976901070927 8184383484587965351606391)
            ·
              refine ⟨12276575226881948027409587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8184383484587965351606391 12276575226881948027409587)
              ·
                refine ⟨18414862840322922041114381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276575226881948027409587 18414862840322922041114381)
                ·
                  refine ⟨6905573565121095765417893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18414862840322922041114381 6905573565121095765417893)
                  ·
                    refine ⟨1294795043460205456015855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6905573565121095765417893 1294795043460205456015855)
                    ·
                      rfl

theorem cell23_7564813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7564813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564813 prefixEnd_7564813 := by exact prefixLift 7564813
  have htrace : WordTrace (prefixWord ++ tailWord_7564813) baseStart_7564813 baseEnd_7564813 := by
    simpa [prefixWord, tailWord_7564813, baseEnd_7564813] using wordTrace_append hprefix tailTrace_7564813
  have hstable : (prefixWord ++ tailWord_7564813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564813).length < 2 ^ (prefixWord ++ tailWord_7564813).sum := by decide
  have hdescent : baseEnd_7564813 < baseStart_7564813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564855 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_7564855 : Nat := 118140960795 + 7564855 * 2 ^ 59
def prefixEnd_7564855 : Nat := 4983230072969 + 3 ^ 40 * 7564855 * 2
def baseEnd_7564855 : Nat := 3884406696568105203722371

theorem tailTrace_7564855 : CollatzResearch.WordTrace tailWord_7564855 prefixEnd_7564855 3884406696568105203722371 := by
  unfold tailWord_7564855
  simp only [CollatzResearch.WordTrace]
  refine ⟨275912929008829784219776019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183941952672553189479850679 275912929008829784219776019)
  ·
    refine ⟨413869393513244676329664029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275912929008829784219776019 413869393513244676329664029)
    ·
      refine ⟨155201022567466753623624011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413869393513244676329664029 155201022567466753623624011)
      ·
        refine ⟨232801533851200130435436017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155201022567466753623624011 232801533851200130435436017)
        ·
          refine ⟨174601150388400097826577013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232801533851200130435436017 174601150388400097826577013)
          ·
            refine ⟨16368857848912509171241595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174601150388400097826577013 16368857848912509171241595)
            ·
              refine ⟨24553286773368763756862393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16368857848912509171241595 24553286773368763756862393)
              ·
                refine ⟨18414965080026572817646795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24553286773368763756862393 18414965080026572817646795)
                ·
                  refine ⟨27622447620039859226470193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18414965080026572817646795 27622447620039859226470193)
                  ·
                    refine ⟨20716835715029894419852645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27622447620039859226470193 20716835715029894419852645)
                    ·
                      refine ⟨3884406696568105203722371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20716835715029894419852645 3884406696568105203722371)
                      ·
                        rfl

theorem cell23_7564855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_7564855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564855 prefixEnd_7564855 := by exact prefixLift 7564855
  have htrace : WordTrace (prefixWord ++ tailWord_7564855) baseStart_7564855 baseEnd_7564855 := by
    simpa [prefixWord, tailWord_7564855, baseEnd_7564855] using wordTrace_append hprefix tailTrace_7564855
  have hstable : (prefixWord ++ tailWord_7564855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564855).length < 2 ^ (prefixWord ++ tailWord_7564855).sum := by decide
  have hdescent : baseEnd_7564855 < baseStart_7564855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564876 : List Nat := [2, 2, 1, 3, 1, 4, 1, 4, 1, 2, 2]
def baseStart_7564876 : Nat := 118140960795 + 7564876 * 2 ^ 59
def prefixEnd_7564876 : Nat := 4983230072969 + 3 ^ 40 * 7564876 * 2
def baseEnd_7564876 : Nat := 3884417479661849621559775

theorem tailTrace_7564876 : CollatzResearch.WordTrace tailWord_7564876 prefixEnd_7564876 3884417479661849621559775 := by
  unfold tailWord_7564876
  simp only [CollatzResearch.WordTrace]
  refine ⟨137956847470876852403145241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183942463294502469870860321 137956847470876852403145241)
  ·
    refine ⟨103467635603157639302358931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137956847470876852403145241 103467635603157639302358931)
    ·
      refine ⟨155201453404736458953538397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103467635603157639302358931 155201453404736458953538397)
      ·
        refine ⟨58200545026776172107576899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155201453404736458953538397 58200545026776172107576899)
        ·
          refine ⟨87300817540164258161365349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58200545026776172107576899 87300817540164258161365349)
          ·
            refine ⟨16368903288780798405256003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87300817540164258161365349 16368903288780798405256003)
            ·
              refine ⟨24553354933171197607884005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16368903288780798405256003 24553354933171197607884005)
              ·
                refine ⟨4603754049969599551478251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24553354933171197607884005 4603754049969599551478251)
                ·
                  refine ⟨6905631074954399327217377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603754049969599551478251 6905631074954399327217377)
                  ·
                    refine ⟨5179223306215799495413033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905631074954399327217377 5179223306215799495413033)
                    ·
                      refine ⟨3884417479661849621559775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179223306215799495413033 3884417479661849621559775)
                      ·
                        rfl

theorem cell23_7564876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_7564876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564876 prefixEnd_7564876 := by exact prefixLift 7564876
  have htrace : WordTrace (prefixWord ++ tailWord_7564876) baseStart_7564876 baseEnd_7564876 := by
    simpa [prefixWord, tailWord_7564876, baseEnd_7564876] using wordTrace_append hprefix tailTrace_7564876
  have hstable : (prefixWord ++ tailWord_7564876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564876).length < 2 ^ (prefixWord ++ tailWord_7564876).sum := by decide
  have hdescent : baseEnd_7564876 < baseStart_7564876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564886 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_7564886 : Nat := 118140960795 + 7564886 * 2 ^ 59
def prefixEnd_7564886 : Nat := 4983230072969 + 3 ^ 40 * 7564886 * 2
def baseEnd_7564886 : Nat := 1294807538156131527478243

theorem tailTrace_7564886 : CollatzResearch.WordTrace tailWord_7564886 prefixEnd_7564886 1294807538156131527478243 := by
  unfold tailWord_7564886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17244628729482342282134657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183942706447811651009436341 17244628729482342282134657)
  ·
    refine ⟨12933471547111756711600993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17244628729482342282134657 12933471547111756711600993)
    ·
      refine ⟨9700103660333817533700745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12933471547111756711600993 9700103660333817533700745)
      ·
        refine ⟨7275077745250363150275559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9700103660333817533700745 7275077745250363150275559)
        ·
          refine ⟨10912616617875544725413339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7275077745250363150275559 10912616617875544725413339)
          ·
            refine ⟨16368924926813317088120009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10912616617875544725413339 16368924926813317088120009)
            ·
              refine ⟨12276693695109987816090007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16368924926813317088120009 12276693695109987816090007)
              ·
                refine ⟨18415040542664981724135011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276693695109987816090007 18415040542664981724135011)
                ·
                  refine ⟨27622560813997472586202517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18415040542664981724135011 27622560813997472586202517)
                  ·
                    refine ⟨1294807538156131527478243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27622560813997472586202517 1294807538156131527478243)
                    ·
                      rfl

theorem cell23_7564886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_7564886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564886 prefixEnd_7564886 := by exact prefixLift 7564886
  have htrace : WordTrace (prefixWord ++ tailWord_7564886) baseStart_7564886 baseEnd_7564886 := by
    simpa [prefixWord, tailWord_7564886, baseEnd_7564886] using wordTrace_append hprefix tailTrace_7564886
  have hstable : (prefixWord ++ tailWord_7564886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564886).length < 2 ^ (prefixWord ++ tailWord_7564886).sum := by decide
  have hdescent : baseEnd_7564886 < baseStart_7564886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564888 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_7564888 : Nat := 118140960795 + 7564888 * 2 ^ 59
def prefixEnd_7564888 : Nat := 4983230072969 + 3 ^ 40 * 7564888 * 2
def baseEnd_7564888 : Nat := 3884423641429703574609719

theorem tailTrace_7564888 : CollatzResearch.WordTrace tailWord_7564888 prefixEnd_7564888 3884423641429703574609719 := by
  unfold tailWord_7564888
  simp only [CollatzResearch.WordTrace]
  refine ⟨137957066308855115427863659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183942755078473487237151545 137957066308855115427863659)
  ·
    refine ⟨206935599463282673141795489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137957066308855115427863659 206935599463282673141795489)
    ·
      refine ⟨155201699597462004856346617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206935599463282673141795489 155201699597462004856346617)
      ·
        refine ⟨116401274698096503642259963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155201699597462004856346617 116401274698096503642259963)
        ·
          refine ⟨174601912047144755463389945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116401274698096503642259963 174601912047144755463389945)
          ·
            refine ⟨130951434035358566597542459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174601912047144755463389945 130951434035358566597542459)
            ·
              refine ⟨196427151053037849896313689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130951434035358566597542459 196427151053037849896313689)
              ·
                refine ⟨147320363289778387422235267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196427151053037849896313689 147320363289778387422235267)
                ·
                  refine ⟨220980544934667581133352901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147320363289778387422235267 220980544934667581133352901)
                  ·
                    refine ⟨41433852175250171462503669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220980544934667581133352901 41433852175250171462503669)
                    ·
                      refine ⟨3884423641429703574609719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41433852175250171462503669 3884423641429703574609719)
                      ·
                        rfl

theorem cell23_7564888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_7564888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564888 prefixEnd_7564888 := by exact prefixLift 7564888
  have htrace : WordTrace (prefixWord ++ tailWord_7564888) baseStart_7564888 baseEnd_7564888 := by
    simpa [prefixWord, tailWord_7564888, baseEnd_7564888] using wordTrace_append hprefix tailTrace_7564888
  have hstable : (prefixWord ++ tailWord_7564888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564888).length < 2 ^ (prefixWord ++ tailWord_7564888).sum := by decide
  have hdescent : baseEnd_7564888 < baseStart_7564888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564892 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_7564892 : Nat := 118140960795 + 7564892 * 2 ^ 59
def prefixEnd_7564892 : Nat := 4983230072969 + 3 ^ 40 * 7564892 * 2
def baseEnd_7564892 : Nat := 3884425695352321558959701

theorem tailTrace_7564892 : CollatzResearch.WordTrace tailWord_7564892 prefixEnd_7564892 3884425695352321558959701 := by
  unfold tailWord_7564892
  simp only [CollatzResearch.WordTrace]
  refine ⟨137957139254847869769436465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183942852339797159692581953 137957139254847869769436465)
  ·
    refine ⟨103467854441135902327077349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137957139254847869769436465 103467854441135902327077349)
    ·
      refine ⟨19400222707712981686327003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103467854441135902327077349 19400222707712981686327003)
      ·
        refine ⟨29100334061569472529490505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19400222707712981686327003 29100334061569472529490505)
        ·
          refine ⟨21825250546177104397117879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29100334061569472529490505 21825250546177104397117879)
          ·
            refine ⟨32737875819265656595676819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21825250546177104397117879 32737875819265656595676819)
            ·
              refine ⟨49106813728898484893515229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32737875819265656595676819 49106813728898484893515229)
              ·
                refine ⟨18415055148336931835068211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49106813728898484893515229 18415055148336931835068211)
                ·
                  refine ⟨27622582722505397752602317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18415055148336931835068211 27622582722505397752602317)
                  ·
                    refine ⟨10358468520939524157225869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27622582722505397752602317 10358468520939524157225869)
                    ·
                      refine ⟨3884425695352321558959701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10358468520939524157225869 3884425695352321558959701)
                      ·
                        rfl

theorem cell23_7564892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_7564892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564892 prefixEnd_7564892 := by exact prefixLift 7564892
  have htrace : WordTrace (prefixWord ++ tailWord_7564892) baseStart_7564892 baseEnd_7564892 := by
    simpa [prefixWord, tailWord_7564892, baseEnd_7564892] using wordTrace_append hprefix tailTrace_7564892
  have hstable : (prefixWord ++ tailWord_7564892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564892).length < 2 ^ (prefixWord ++ tailWord_7564892).sum := by decide
  have hdescent : baseEnd_7564892 < baseStart_7564892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564893 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7564893 : Nat := 118140960795 + 7564893 * 2 ^ 59
def prefixEnd_7564893 : Nat := 4983230072969 + 3 ^ 40 * 7564893 * 2
def baseEnd_7564893 : Nat := 3884426208832976055047197

theorem tailTrace_7564893 : CollatzResearch.WordTrace tailWord_7564893 prefixEnd_7564893 3884426208832976055047197 := by
  unfold tailWord_7564893
  simp only [CollatzResearch.WordTrace]
  refine ⟨275914314982692116709659333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183942876655128077806439555 275914314982692116709659333)
  ·
    refine ⟨51733934059254771883061125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275914314982692116709659333 51733934059254771883061125)
    ·
      refine ⟨9700112636110269728073961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51733934059254771883061125 9700112636110269728073961)
      ·
        refine ⟨7275084477082702296055471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9700112636110269728073961 7275084477082702296055471)
        ·
          refine ⟨10912626715624053444083207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7275084477082702296055471 10912626715624053444083207)
          ·
            refine ⟨16368940073436080166124811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10912626715624053444083207 16368940073436080166124811)
            ·
              refine ⟨24553410110154120249187217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16368940073436080166124811 24553410110154120249187217)
              ·
                refine ⟨18415057582615590186890413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24553410110154120249187217 18415057582615590186890413)
                ·
                  refine ⟨6905646593480846320083905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18415057582615590186890413 6905646593480846320083905)
                  ·
                    refine ⟨5179234945110634740062929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905646593480846320083905 5179234945110634740062929)
                    ·
                      refine ⟨3884426208832976055047197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179234945110634740062929 3884426208832976055047197)
                      ·
                        rfl

theorem cell23_7564893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7564893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564893 prefixEnd_7564893 := by exact prefixLift 7564893
  have htrace : WordTrace (prefixWord ++ tailWord_7564893) baseStart_7564893 baseEnd_7564893 := by
    simpa [prefixWord, tailWord_7564893, baseEnd_7564893] using wordTrace_append hprefix tailTrace_7564893
  have hstable : (prefixWord ++ tailWord_7564893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564893).length < 2 ^ (prefixWord ++ tailWord_7564893).sum := by decide
  have hdescent : baseEnd_7564893 < baseStart_7564893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564908 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_7564908 : Nat := 118140960795 + 7564908 * 2 ^ 59
def prefixEnd_7564908 : Nat := 4983230072969 + 3 ^ 40 * 7564908 * 2
def baseEnd_7564908 : Nat := 1294811303680931165453209

theorem tailTrace_7564908 : CollatzResearch.WordTrace tailWord_7564908 prefixEnd_7564908 1294811303680931165453209 := by
  unfold tailWord_7564908
  simp only [CollatzResearch.WordTrace]
  refine ⟨137957431038818887135727689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183943241385091849514303585 137957431038818887135727689)
  ·
    refine ⟨103468073279114165351795767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137957431038818887135727689 103468073279114165351795767)
    ·
      refine ⟨155202109918671248027693651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103468073279114165351795767 155202109918671248027693651)
      ·
        refine ⟨232803164878006872041540477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155202109918671248027693651 232803164878006872041540477)
        ·
          refine ⟨87301186829252577015577679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232803164878006872041540477 87301186829252577015577679)
          ·
            refine ⟨130951780243878865523366519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87301186829252577015577679 130951780243878865523366519)
            ·
              refine ⟨196427670365818298285049779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130951780243878865523366519 196427670365818298285049779)
              ·
                refine ⟨294641505548727447427574669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196427670365818298285049779 294641505548727447427574669)
                ·
                  refine ⟨110490564580772792785340501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294641505548727447427574669 110490564580772792785340501)
                  ·
                    refine ⟨1294811303680931165453209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110490564580772792785340501 1294811303680931165453209)
                    ·
                      rfl

theorem cell23_7564908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_7564908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564908 prefixEnd_7564908 := by exact prefixLift 7564908
  have htrace : WordTrace (prefixWord ++ tailWord_7564908) baseStart_7564908 baseEnd_7564908 := by
    simpa [prefixWord, tailWord_7564908, baseEnd_7564908] using wordTrace_append hprefix tailTrace_7564908
  have hstable : (prefixWord ++ tailWord_7564908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564908).length < 2 ^ (prefixWord ++ tailWord_7564908).sum := by decide
  have hdescent : baseEnd_7564908 < baseStart_7564908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564915 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 8, 2]
def baseStart_7564915 : Nat := 118140960795 + 7564915 * 2 ^ 59
def prefixEnd_7564915 : Nat := 4983230072969 + 3 ^ 40 * 7564915 * 2
def baseEnd_7564915 : Nat := 3884437505407374968972095

theorem tailTrace_7564915 : CollatzResearch.WordTrace tailWord_7564915 prefixEnd_7564915 3884437505407374968972095 := by
  unfold tailWord_7564915
  simp only [CollatzResearch.WordTrace]
  refine ⟨275915117388612414466960199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183943411592408276311306799 275915117388612414466960199)
  ·
    refine ⟨413872676082918621700440299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275915117388612414466960199 413872676082918621700440299)
    ·
      refine ⟨620809014124377932550660449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413872676082918621700440299 620809014124377932550660449)
      ·
        refine ⟨465606760593283449412995337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620809014124377932550660449 465606760593283449412995337)
        ·
          refine ⟨349205070444962587059746503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465606760593283449412995337 349205070444962587059746503)
          ·
            refine ⟨523807605667443880589619755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349205070444962587059746503 523807605667443880589619755)
            ·
              refine ⟨785711408501165820884429633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523807605667443880589619755 785711408501165820884429633)
              ·
                refine ⟨589283556375874365663322225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785711408501165820884429633 589283556375874365663322225)
                ·
                  refine ⟨441962667281905774247491669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589283556375874365663322225 441962667281905774247491669)
                  ·
                    refine ⟨5179250007209833291962793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 441962667281905774247491669 5179250007209833291962793)
                    ·
                      refine ⟨3884437505407374968972095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179250007209833291962793 3884437505407374968972095)
                      ·
                        rfl

theorem cell23_7564915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 8, 2].length) (baseStart_7564915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564915 prefixEnd_7564915 := by exact prefixLift 7564915
  have htrace : WordTrace (prefixWord ++ tailWord_7564915) baseStart_7564915 baseEnd_7564915 := by
    simpa [prefixWord, tailWord_7564915, baseEnd_7564915] using wordTrace_append hprefix tailTrace_7564915
  have hstable : (prefixWord ++ tailWord_7564915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564915).length < 2 ^ (prefixWord ++ tailWord_7564915).sum := by decide
  have hdescent : baseEnd_7564915 < baseStart_7564915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564925 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_7564925 : Nat := 118140960795 + 7564925 * 2 ^ 59
def prefixEnd_7564925 : Nat := 4983230072969 + 3 ^ 40 * 7564925 * 2
def baseEnd_7564925 : Nat := 1294814213404639976615683

theorem tailTrace_7564925 : CollatzResearch.WordTrace tailWord_7564925 prefixEnd_7564925 1294814213404639976615683 := by
  unfold tailWord_7564925
  simp only [CollatzResearch.WordTrace]
  refine ⟨275915482118576186174824229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183943654745717457449882819 275915482118576186174824229)
  ·
    refine ⟨51734152897233034907779543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275915482118576186174824229 51734152897233034907779543)
    ·
      refine ⟨77601229345849552361669315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51734152897233034907779543 77601229345849552361669315)
      ·
        refine ⟨116401844018774328542503973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77601229345849552361669315 116401844018774328542503973)
        ·
          refine ⟨21825345753520186601719495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116401844018774328542503973 21825345753520186601719495)
          ·
            refine ⟨32738018630280279902579243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21825345753520186601719495 32738018630280279902579243)
            ·
              refine ⟨49107027945420419853868865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32738018630280279902579243 49107027945420419853868865)
              ·
                refine ⟨36830270959065314890401649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49107027945420419853868865 36830270959065314890401649)
                ·
                  refine ⟨27622703219298986167801237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36830270959065314890401649 27622703219298986167801237)
                  ·
                    refine ⟨1294814213404639976615683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27622703219298986167801237 1294814213404639976615683)
                    ·
                      rfl

theorem cell23_7564925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_7564925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564925 prefixEnd_7564925 := by exact prefixLift 7564925
  have htrace : WordTrace (prefixWord ++ tailWord_7564925) baseStart_7564925 baseEnd_7564925 := by
    simpa [prefixWord, tailWord_7564925, baseEnd_7564925] using wordTrace_append hprefix tailTrace_7564925
  have hstable : (prefixWord ++ tailWord_7564925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564925).length < 2 ^ (prefixWord ++ tailWord_7564925).sum := by decide
  have hdescent : baseEnd_7564925 < baseStart_7564925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564949 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_7564949 : Nat := 118140960795 + 7564949 * 2 ^ 59
def prefixEnd_7564949 : Nat := 4983230072969 + 3 ^ 40 * 7564949 * 2
def baseEnd_7564949 : Nat := 3884454963749627835946939

theorem tailTrace_7564949 : CollatzResearch.WordTrace tailWord_7564949 prefixEnd_7564949 3884454963749627835946939 := by
  unfold tailWord_7564949
  simp only [CollatzResearch.WordTrace]
  refine ⟨275916357470489238273697901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183944238313659492182465267 275916357470489238273697901)
  ·
    refine ⟨103468634051433464352636713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275916357470489238273697901 103468634051433464352636713)
    ·
      refine ⟨77601475538575098264477535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103468634051433464352636713 77601475538575098264477535)
      ·
        refine ⟨116402213307862647396716303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77601475538575098264477535 116402213307862647396716303)
        ·
          refine ⟨174603319961793971095074455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116402213307862647396716303 174603319961793971095074455)
          ·
            refine ⟨261904979942690956642611683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174603319961793971095074455 261904979942690956642611683)
            ·
              refine ⟨392857469914036434963917525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261904979942690956642611683 392857469914036434963917525)
              ·
                refine ⟨9207596951110228944466817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 392857469914036434963917525 9207596951110228944466817)
                ·
                  refine ⟨6905697713332671708350113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9207596951110228944466817 6905697713332671708350113)
                  ·
                    refine ⟨5179273284999503781262585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905697713332671708350113 5179273284999503781262585)
                    ·
                      refine ⟨3884454963749627835946939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179273284999503781262585 3884454963749627835946939)
                      ·
                        rfl

theorem cell23_7564949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_7564949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564949 prefixEnd_7564949 := by exact prefixLift 7564949
  have htrace : WordTrace (prefixWord ++ tailWord_7564949) baseStart_7564949 baseEnd_7564949 := by
    simpa [prefixWord, tailWord_7564949, baseEnd_7564949] using wordTrace_append hprefix tailTrace_7564949
  have hstable : (prefixWord ++ tailWord_7564949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564949).length < 2 ^ (prefixWord ++ tailWord_7564949).sum := by decide
  have hdescent : baseEnd_7564949 < baseStart_7564949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564965 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_7564965 : Nat := 118140960795 + 7564965 * 2 ^ 59
def prefixEnd_7564965 : Nat := 4983230072969 + 3 ^ 40 * 7564965 * 2
def baseEnd_7564965 : Nat := 3884463179440099773346865

theorem tailTrace_7564965 : CollatzResearch.WordTrace tailWord_7564965 prefixEnd_7564965 3884463179440099773346865 := by
  unfold tailWord_7564965
  simp only [CollatzResearch.WordTrace]
  refine ⟨275916941038431273006280349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183944627358954182004186899 275916941038431273006280349)
  ·
    refine ⟨103468852889411727377355131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275916941038431273006280349 103468852889411727377355131)
    ·
      refine ⟨155203279334117591066032697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103468852889411727377355131 155203279334117591066032697)
      ·
        refine ⟨116402459500588193299524523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155203279334117591066032697 116402459500588193299524523)
        ·
          refine ⟨174603689250882289949286785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116402459500588193299524523 174603689250882289949286785)
          ·
            refine ⟨130952766938161717461965089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174603689250882289949286785 130952766938161717461965089)
            ·
              refine ⟨98214575203621288096473817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130952766938161717461965089 98214575203621288096473817)
              ·
                refine ⟨73660931402715966072355363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98214575203621288096473817 73660931402715966072355363)
                ·
                  refine ⟨110491397104073949108533045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73660931402715966072355363 110491397104073949108533045)
                  ·
                    refine ⟨10358568478506932728924973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110491397104073949108533045 10358568478506932728924973)
                    ·
                      refine ⟨3884463179440099773346865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10358568478506932728924973 3884463179440099773346865)
                      ·
                        rfl

theorem cell23_7564965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_7564965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564965 prefixEnd_7564965 := by exact prefixLift 7564965
  have htrace : WordTrace (prefixWord ++ tailWord_7564965) baseStart_7564965 baseEnd_7564965 := by
    simpa [prefixWord, tailWord_7564965, baseEnd_7564965] using wordTrace_append hprefix tailTrace_7564965
  have hstable : (prefixWord ++ tailWord_7564965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564965).length < 2 ^ (prefixWord ++ tailWord_7564965).sum := by decide
  have hdescent : baseEnd_7564965 < baseStart_7564965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564985 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 4, 5]
def baseStart_7564985 : Nat := 118140960795 + 7564985 * 2 ^ 59
def prefixEnd_7564985 : Nat := 4983230072969 + 3 ^ 40 * 7564985 * 2
def baseEnd_7564985 : Nat := 1294824483017729898365591

theorem tailTrace_7564985 : CollatzResearch.WordTrace tailWord_7564985 prefixEnd_7564985 1294824483017729898365591 := by
  unfold tailWord_7564985
  simp only [CollatzResearch.WordTrace]
  refine ⟨275917670498358816422008409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183945113665572544281338939 275917670498358816422008409)
  ·
    refine ⟨206938252873769112316506307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275917670498358816422008409 206938252873769112316506307)
    ·
      refine ⟨310407379310653668474759461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206938252873769112316506307 310407379310653668474759461)
      ·
        refine ⟨58201383620747562839017399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310407379310653668474759461 58201383620747562839017399)
        ·
          refine ⟨87302075431121344258526099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58201383620747562839017399 87302075431121344258526099)
          ·
            refine ⟨130953113146682016387789149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87302075431121344258526099 130953113146682016387789149)
            ·
              refine ⟨49107417430005756145420931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130953113146682016387789149 49107417430005756145420931)
              ·
                refine ⟨73661126145008634218131397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49107417430005756145420931 73661126145008634218131397)
                ·
                  refine ⟨13811461152189118915899637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73661126145008634218131397 13811461152189118915899637)
                  ·
                    refine ⟨1294824483017729898365591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13811461152189118915899637 1294824483017729898365591)
                    ·
                      rfl

theorem cell23_7564985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_7564985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564985 prefixEnd_7564985 := by exact prefixLift 7564985
  have htrace : WordTrace (prefixWord ++ tailWord_7564985) baseStart_7564985 baseEnd_7564985 := by
    simpa [prefixWord, tailWord_7564985, baseEnd_7564985] using wordTrace_append hprefix tailTrace_7564985
  have hstable : (prefixWord ++ tailWord_7564985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564985).length < 2 ^ (prefixWord ++ tailWord_7564985).sum := by decide
  have hdescent : baseEnd_7564985 < baseStart_7564985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564989 : List Nat := [1, 4, 1, 2, 1, 2, 5, 2, 5]
def baseStart_7564989 : Nat := 118140960795 + 7564989 * 2 ^ 59
def prefixEnd_7564989 : Nat := 4983230072969 + 3 ^ 40 * 7564989 * 2
def baseEnd_7564989 : Nat := 431608389219534186605195

theorem tailTrace_7564989 : CollatzResearch.WordTrace tailWord_7564989 prefixEnd_7564989 431608389219534186605195 := by
  unfold tailWord_7564989
  simp only [CollatzResearch.WordTrace]
  refine ⟨275917816390344325105154021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183945210926896216736769347 275917816390344325105154021)
  ·
    refine ⟨51734590573189560957216379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275917816390344325105154021 51734590573189560957216379)
    ·
      refine ⟨77601885859784341435824569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51734590573189560957216379 77601885859784341435824569)
      ·
        refine ⟨58201414394838256076868427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77601885859784341435824569 58201414394838256076868427)
        ·
          refine ⟨87302121592257384115302641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58201414394838256076868427 87302121592257384115302641)
          ·
            refine ⟨65476591194193038086476981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87302121592257384115302641 65476591194193038086476981)
            ·
              refine ⟨6138430424455597320607217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65476591194193038086476981 6138430424455597320607217)
              ·
                refine ⟨4603822818341697990455413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6138430424455597320607217 4603822818341697990455413)
                ·
                  refine ⟨431608389219534186605195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4603822818341697990455413 431608389219534186605195)
                  ·
                    rfl

theorem cell23_7564989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_7564989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564989 prefixEnd_7564989 := by exact prefixLift 7564989
  have htrace : WordTrace (prefixWord ++ tailWord_7564989) baseStart_7564989 baseEnd_7564989 := by
    simpa [prefixWord, tailWord_7564989, baseEnd_7564989] using wordTrace_append hprefix tailTrace_7564989
  have hstable : (prefixWord ++ tailWord_7564989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564989).length < 2 ^ (prefixWord ++ tailWord_7564989).sum := by decide
  have hdescent : baseEnd_7564989 < baseStart_7564989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564992 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 2, 5, 2]
def baseStart_7564992 : Nat := 118140960795 + 7564992 * 2 ^ 59
def prefixEnd_7564992 : Nat := 4983230072969 + 3 ^ 40 * 7564992 * 2
def baseEnd_7564992 : Nat := 3884477043417771167709241

theorem tailTrace_7564992 : CollatzResearch.WordTrace tailWord_7564992 prefixEnd_7564992 3884477043417771167709241 := by
  unfold tailWord_7564992
  simp only [CollatzResearch.WordTrace]
  refine ⟨137958962904666728308756615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183945283872888971078342153 137958962904666728308756615)
  ·
    refine ⟨206938444357000092463134923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137958962904666728308756615 206938444357000092463134923)
    ·
      refine ⟨310407666535500138694702385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206938444357000092463134923 310407666535500138694702385)
      ·
        refine ⟨232805749901625104021026789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310407666535500138694702385 232805749901625104021026789)
        ·
          refine ⟨43651078106554707003942523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232805749901625104021026789 43651078106554707003942523)
          ·
            refine ⟨65476617159832060505913785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43651078106554707003942523 65476617159832060505913785)
            ·
              refine ⟨49107462869874045379435339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65476617159832060505913785 49107462869874045379435339)
              ·
                refine ⟨73661194304811068069153009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49107462869874045379435339 73661194304811068069153009)
                ·
                  refine ⟨55245895728608301051864757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73661194304811068069153009 55245895728608301051864757)
                  ·
                    refine ⟨5179302724557028223612321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55245895728608301051864757 5179302724557028223612321)
                    ·
                      refine ⟨3884477043417771167709241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179302724557028223612321 3884477043417771167709241)
                      ·
                        rfl

theorem cell23_7564992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_7564992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564992 prefixEnd_7564992 := by exact prefixLift 7564992
  have htrace : WordTrace (prefixWord ++ tailWord_7564992) baseStart_7564992 baseEnd_7564992 := by
    simpa [prefixWord, tailWord_7564992, baseEnd_7564992] using wordTrace_append hprefix tailTrace_7564992
  have hstable : (prefixWord ++ tailWord_7564992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564992).length < 2 ^ (prefixWord ++ tailWord_7564992).sum := by decide
  have hdescent : baseEnd_7564992 < baseStart_7564992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564994 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7564994 : Nat := 118140960795 + 7564994 * 2 ^ 59
def prefixEnd_7564994 : Nat := 4983230072969 + 3 ^ 40 * 7564994 * 2
def baseEnd_7564994 : Nat := 3884478070379080159884233

theorem tailTrace_7564994 : CollatzResearch.WordTrace tailWord_7564994 prefixEnd_7564994 3884478070379080159884233 := by
  unfold tailWord_7564994
  simp only [CollatzResearch.WordTrace]
  refine ⟨68979499688831552739771509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183945332503550807306057357 68979499688831552739771509)
  ·
    refine ⟨6466828095827958069353579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68979499688831552739771509 6466828095827958069353579)
    ·
      refine ⟨9700242143741937104030369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6466828095827958069353579 9700242143741937104030369)
      ·
        refine ⟨7275181607806452828022777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9700242143741937104030369 7275181607806452828022777)
        ·
          refine ⟨5456386205854839621017083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7275181607806452828022777 5456386205854839621017083)
          ·
            refine ⟨8184579308782259431525625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456386205854839621017083 8184579308782259431525625)
            ·
              refine ⟨6138434481586694573644219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8184579308782259431525625 6138434481586694573644219)
              ·
                refine ⟨9207651722380041860466329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138434481586694573644219 9207651722380041860466329)
                ·
                  refine ⟨6905738791785031395349747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9207651722380041860466329 6905738791785031395349747)
                  ·
                    refine ⟨10358608187677547093024621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6905738791785031395349747 10358608187677547093024621)
                    ·
                      refine ⟨3884478070379080159884233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10358608187677547093024621 3884478070379080159884233)
                      ·
                        rfl

theorem cell23_7564994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7564994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7564994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7564994 prefixEnd_7564994 := by exact prefixLift 7564994
  have htrace : WordTrace (prefixWord ++ tailWord_7564994) baseStart_7564994 baseEnd_7564994 := by
    simpa [prefixWord, tailWord_7564994, baseEnd_7564994] using wordTrace_append hprefix tailTrace_7564994
  have hstable : (prefixWord ++ tailWord_7564994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564994).length < 2 ^ (prefixWord ++ tailWord_7564994).sum := by decide
  have hdescent : baseEnd_7564994 < baseStart_7564994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565106 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_7565106 : Nat := 118140960795 + 7565106 * 2 ^ 59
def prefixEnd_7565106 : Nat := 4983230072969 + 3 ^ 40 * 7565106 * 2
def baseEnd_7565106 : Nat := 3884535580212383721683717

theorem tailTrace_7565106 : CollatzResearch.WordTrace tailWord_7565106 prefixEnd_7565106 3884535580212383721683717 := by
  unfold tailWord_7565106
  simp only [CollatzResearch.WordTrace]
  refine ⟨68980520932730113521790793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183948055820613636058108781 68980520932730113521790793)
  ·
    refine ⟨51735390699547585141343095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68980520932730113521790793 51735390699547585141343095)
    ·
      refine ⟨77603086049321377712014643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51735390699547585141343095 77603086049321377712014643)
      ·
        refine ⟨116404629073982066568021965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77603086049321377712014643 116404629073982066568021965)
        ·
          refine ⟨43651735902743274963008237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116404629073982066568021965 43651735902743274963008237)
          ·
            refine ⟨16369400963528728111128089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43651735902743274963008237 16369400963528728111128089)
            ·
              refine ⟨12277050722646546083346067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16369400963528728111128089 12277050722646546083346067)
              ·
                refine ⟨18415576083969819125019101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12277050722646546083346067 18415576083969819125019101)
                ·
                  refine ⟨6905841031488682171882163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18415576083969819125019101 6905841031488682171882163)
                  ·
                    refine ⟨10358761547233023257823245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6905841031488682171882163 10358761547233023257823245)
                    ·
                      refine ⟨3884535580212383721683717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10358761547233023257823245 3884535580212383721683717)
                      ·
                        rfl

theorem cell23_7565106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_7565106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565106 prefixEnd_7565106 := by exact prefixLift 7565106
  have htrace : WordTrace (prefixWord ++ tailWord_7565106) baseStart_7565106 baseEnd_7565106 := by
    simpa [prefixWord, tailWord_7565106, baseEnd_7565106] using wordTrace_append hprefix tailTrace_7565106
  have hstable : (prefixWord ++ tailWord_7565106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565106).length < 2 ^ (prefixWord ++ tailWord_7565106).sum := by decide
  have hdescent : baseEnd_7565106 < baseStart_7565106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565129 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 4]
def baseStart_7565129 : Nat := 118140960795 + 7565129 * 2 ^ 59
def prefixEnd_7565129 : Nat := 4983230072969 + 3 ^ 40 * 7565129 * 2
def baseEnd_7565129 : Nat := 3884547390267437131696111

theorem tailTrace_7565129 : CollatzResearch.WordTrace tailWord_7565129 prefixEnd_7565129 3884547390267437131696111 := by
  unfold tailWord_7565129
  simp only [CollatzResearch.WordTrace]
  refine ⟨275922922609837129015250441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183948615073224752676833627 275922922609837129015250441)
  ·
    refine ⟨206942191957377846761437831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275922922609837129015250441 206942191957377846761437831)
    ·
      refine ⟨310413287936066770142156747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206942191957377846761437831 310413287936066770142156747)
      ·
        refine ⟨465619931904100155213235121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310413287936066770142156747 465619931904100155213235121)
        ·
          refine ⟨349214948928075116409926341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465619931904100155213235121 349214948928075116409926341)
          ·
            refine ⟨65477802924014084326861189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349214948928075116409926341 65477802924014084326861189)
            ·
              refine ⟨12277088048252640811286473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65477802924014084326861189 12277088048252640811286473)
              ·
                refine ⟨9207816036189480608464855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277088048252640811286473 9207816036189480608464855)
                ·
                  refine ⟨13811724054284220912697283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9207816036189480608464855 13811724054284220912697283)
                  ·
                    refine ⟨20717586081426331369045925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13811724054284220912697283 20717586081426331369045925)
                    ·
                      refine ⟨3884547390267437131696111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20717586081426331369045925 3884547390267437131696111)
                      ·
                        rfl

theorem cell23_7565129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 4].length) (baseStart_7565129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565129 prefixEnd_7565129 := by exact prefixLift 7565129
  have htrace : WordTrace (prefixWord ++ tailWord_7565129) baseStart_7565129 baseEnd_7565129 := by
    simpa [prefixWord, tailWord_7565129, baseEnd_7565129] using wordTrace_append hprefix tailTrace_7565129
  have hstable : (prefixWord ++ tailWord_7565129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565129).length < 2 ^ (prefixWord ++ tailWord_7565129).sum := by decide
  have hdescent : baseEnd_7565129 < baseStart_7565129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565140 : List Nat := [2, 4, 1, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_7565140 : Nat := 118140960795 + 7565140 * 2 ^ 59
def prefixEnd_7565140 : Nat := 4983230072969 + 3 ^ 40 * 7565140 * 2
def baseEnd_7565140 : Nat := 3884553038554636588658561

theorem tailTrace_7565140 : CollatzResearch.WordTrace tailWord_7565140 prefixEnd_7565140 3884553038554636588658561 := by
  unfold tailWord_7565140
  simp only [CollatzResearch.WordTrace]
  refine ⟨137961661906398638946950437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183948882541864851929267249 137961661906398638946950437)
  ·
    refine ⟨25867811607449744802553207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137961661906398638946950437 25867811607449744802553207)
    ·
      refine ⟨38801717411174617203829811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25867811607449744802553207 38801717411174617203829811)
      ·
        refine ⟨58202576116761925805744717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38801717411174617203829811 58202576116761925805744717)
        ·
          refine ⟨21825966043785722177154269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58202576116761925805744717 21825966043785722177154269)
          ·
            refine ⟨8184737266419645816432851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21825966043785722177154269 8184737266419645816432851)
            ·
              refine ⟨12277105899629468724649277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8184737266419645816432851 12277105899629468724649277)
              ·
                refine ⟨4603914712361050771743479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12277105899629468724649277 4603914712361050771743479)
                ·
                  refine ⟨6905872068541576157615219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603914712361050771743479 6905872068541576157615219)
                  ·
                    refine ⟨10358808102812364236422829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6905872068541576157615219 10358808102812364236422829)
                    ·
                      refine ⟨3884553038554636588658561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10358808102812364236422829 3884553038554636588658561)
                      ·
                        rfl

theorem cell23_7565140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_7565140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565140 prefixEnd_7565140 := by exact prefixLift 7565140
  have htrace : WordTrace (prefixWord ++ tailWord_7565140) baseStart_7565140 baseEnd_7565140 := by
    simpa [prefixWord, tailWord_7565140, baseEnd_7565140] using wordTrace_append hprefix tailTrace_7565140
  have hstable : (prefixWord ++ tailWord_7565140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565140).length < 2 ^ (prefixWord ++ tailWord_7565140).sum := by decide
  have hdescent : baseEnd_7565140 < baseStart_7565140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565152 : List Nat := [2, 1, 1, 3, 3, 4, 9]
def baseStart_7565152 : Nat := 118140960795 + 7565152 * 2 ^ 59
def prefixEnd_7565152 : Nat := 4983230072969 + 3 ^ 40 * 7565152 * 2
def baseEnd_7565152 : Nat := 47957520991635685700105

theorem tailTrace_7565152 : CollatzResearch.WordTrace tailWord_7565152 prefixEnd_7565152 47957520991635685700105 := by
  unfold tailWord_7565152
  simp only [CollatzResearch.WordTrace]
  refine ⟨137961880744376901971668855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183949174325835869295558473 137961880744376901971668855)
  ·
    refine ⟨206942821116565352957503283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137961880744376901971668855 206942821116565352957503283)
    ·
      refine ⟨310414231674848029436254925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206942821116565352957503283 310414231674848029436254925)
      ·
        refine ⟨116405336878068011038595597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310414231674848029436254925 116405336878068011038595597)
        ·
          refine ⟨43652001329275504139473349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116405336878068011038595597 43652001329275504139473349)
          ·
            refine ⟨8184750249239157026151253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43652001329275504139473349 8184750249239157026151253)
            ·
              refine ⟨47957520991635685700105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8184750249239157026151253 47957520991635685700105)
              ·
                rfl

theorem cell23_7565152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 9].length) (baseStart_7565152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565152 prefixEnd_7565152 := by exact prefixLift 7565152
  have htrace : WordTrace (prefixWord ++ tailWord_7565152) baseStart_7565152 baseEnd_7565152 := by
    simpa [prefixWord, tailWord_7565152, baseEnd_7565152] using wordTrace_append hprefix tailTrace_7565152
  have hstable : (prefixWord ++ tailWord_7565152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565152).length < 2 ^ (prefixWord ++ tailWord_7565152).sum := by decide
  have hdescent : baseEnd_7565152 < baseStart_7565152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565213 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_7565213 : Nat := 118140960795 + 7565213 * 2 ^ 59
def prefixEnd_7565213 : Nat := 4983230072969 + 3 ^ 40 * 7565213 * 2
def baseEnd_7565213 : Nat := 3884590522642414803045725

theorem tailTrace_7565213 : CollatzResearch.WordTrace tailWord_7565213 prefixEnd_7565213 3884590522642414803045725 := by
  unfold tailWord_7565213
  simp only [CollatzResearch.WordTrace]
  refine ⟨275925986341532811361308293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183950657561021874240872195 275925986341532811361308293)
  ·
    refine ⟨51736122439037402130245305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275925986341532811361308293 51736122439037402130245305)
    ·
      refine ⟨38802091829278051597683979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51736122439037402130245305 38802091829278051597683979)
      ·
        refine ⟨58203137743917077396525969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38802091829278051597683979 58203137743917077396525969)
        ·
          refine ⟨43652353307937808047394477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58203137743917077396525969 43652353307937808047394477)
          ·
            refine ⟨16369632490476678017772929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43652353307937808047394477 16369632490476678017772929)
            ·
              refine ⟨12277224367857508513329697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16369632490476678017772929 12277224367857508513329697)
              ·
                refine ⟨9207918275893131384997273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277224367857508513329697 9207918275893131384997273)
                ·
                  refine ⟨6905938706919848538747955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9207918275893131384997273 6905938706919848538747955)
                  ·
                    refine ⟨10358908060379772808121933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6905938706919848538747955 10358908060379772808121933)
                    ·
                      refine ⟨3884590522642414803045725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10358908060379772808121933 3884590522642414803045725)
                      ·
                        rfl

theorem cell23_7565213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_7565213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565213 prefixEnd_7565213 := by exact prefixLift 7565213
  have htrace : WordTrace (prefixWord ++ tailWord_7565213) baseStart_7565213 baseEnd_7565213 := by
    simpa [prefixWord, tailWord_7565213, baseEnd_7565213] using wordTrace_append hprefix tailTrace_7565213
  have hstable : (prefixWord ++ tailWord_7565213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565213).length < 2 ^ (prefixWord ++ tailWord_7565213).sum := by decide
  have hdescent : baseEnd_7565213 < baseStart_7565213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565214 : List Nat := [4, 3, 1, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7565214 : Nat := 118140960795 + 7565214 * 2 ^ 59
def prefixEnd_7565214 : Nat := 4983230072969 + 3 ^ 40 * 7565214 * 2
def baseEnd_7565214 : Nat := 3884591036123069299133221

theorem tailTrace_7565214 : CollatzResearch.WordTrace tailWord_7565214 prefixEnd_7565214 3884591036123069299133221 := by
  unfold tailWord_7565214
  simp only [CollatzResearch.WordTrace]
  refine ⟨34490752851816148566511837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183950681876352792354729797 34490752851816148566511837)
  ·
    refine ⟨12934032319431055712441939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34490752851816148566511837 12934032319431055712441939)
    ·
      refine ⟨19401048479146583568662909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12934032319431055712441939 19401048479146583568662909)
      ·
        refine ⟨7275393179679968838248591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19401048479146583568662909 7275393179679968838248591)
        ·
          refine ⟨10913089769519953257372887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7275393179679968838248591 10913089769519953257372887)
          ·
            refine ⟨16369634654279929886059331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10913089769519953257372887 16369634654279929886059331)
            ·
              refine ⟨24554451981419894829088997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16369634654279929886059331 24554451981419894829088997)
              ·
                refine ⟨4603959746516230280454187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24554451981419894829088997 4603959746516230280454187)
                ·
                  refine ⟨6905939619774345420681281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603959746516230280454187 6905939619774345420681281)
                  ·
                    refine ⟨5179454714830759065510961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905939619774345420681281 5179454714830759065510961)
                    ·
                      refine ⟨3884591036123069299133221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179454714830759065510961 3884591036123069299133221)
                      ·
                        rfl

theorem cell23_7565214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7565214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565214 prefixEnd_7565214 := by exact prefixLift 7565214
  have htrace : WordTrace (prefixWord ++ tailWord_7565214) baseStart_7565214 baseEnd_7565214 := by
    simpa [prefixWord, tailWord_7565214, baseEnd_7565214] using wordTrace_append hprefix tailTrace_7565214
  have hstable : (prefixWord ++ tailWord_7565214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565214).length < 2 ^ (prefixWord ++ tailWord_7565214).sum := by decide
  have hdescent : baseEnd_7565214 < baseStart_7565214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565219 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 5, 4, 2]
def baseStart_7565219 : Nat := 118140960795 + 7565219 * 2 ^ 59
def prefixEnd_7565219 : Nat := 4983230072969 + 3 ^ 40 * 7565219 * 2
def baseEnd_7565219 : Nat := 3884593603526341779570697

theorem tailTrace_7565219 : CollatzResearch.WordTrace tailWord_7565219 prefixEnd_7565219 3884593603526341779570697 := by
  unfold tailWord_7565219
  simp only [CollatzResearch.WordTrace]
  refine ⟨275926205179511074386026711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183950803453007382924017807 275926205179511074386026711)
  ·
    refine ⟨413889307769266611579040067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275926205179511074386026711 413889307769266611579040067)
    ·
      refine ⟨620833961653899917368560101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413889307769266611579040067 620833961653899917368560101)
      ·
        refine ⟨116406367810106234506605019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 620833961653899917368560101 116406367810106234506605019)
        ·
          refine ⟨174609551715159351759907529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116406367810106234506605019 174609551715159351759907529)
          ·
            refine ⟨130957163786369513819930647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174609551715159351759907529 130957163786369513819930647)
            ·
              refine ⟨196435745679554270729895971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130957163786369513819930647 196435745679554270729895971)
              ·
                refine ⟨294653618519331406094843957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196435745679554270729895971 294653618519331406094843957)
                ·
                  refine ⟨27623776736187319321391621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294653618519331406094843957 27623776736187319321391621)
                  ·
                    refine ⟨5179458138035122372760929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27623776736187319321391621 5179458138035122372760929)
                    ·
                      refine ⟨3884593603526341779570697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179458138035122372760929 3884593603526341779570697)
                      ·
                        rfl

theorem cell23_7565219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_7565219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565219 prefixEnd_7565219 := by exact prefixLift 7565219
  have htrace : WordTrace (prefixWord ++ tailWord_7565219) baseStart_7565219 baseEnd_7565219 := by
    simpa [prefixWord, tailWord_7565219, baseEnd_7565219] using wordTrace_append hprefix tailTrace_7565219
  have hstable : (prefixWord ++ tailWord_7565219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565219).length < 2 ^ (prefixWord ++ tailWord_7565219).sum := by decide
  have hdescent : baseEnd_7565219 < baseStart_7565219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565287 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_7565287 : Nat := 118140960795 + 7565287 * 2 ^ 59
def prefixEnd_7565287 : Nat := 4983230072969 + 3 ^ 40 * 7565287 * 2
def baseEnd_7565287 : Nat := 3884628520210847513520385

theorem tailTrace_7565287 : CollatzResearch.WordTrace tailWord_7565287 prefixEnd_7565287 3884628520210847513520385 := by
  unfold tailWord_7565287
  simp only [CollatzResearch.WordTrace]
  refine ⟨275928685343264721999502115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183952456895509814666334743 275928685343264721999502115)
  ·
    refine ⟨413893028014897082999253173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275928685343264721999502115 413893028014897082999253173)
    ·
      refine ⟨38802471376396601531179985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 413893028014897082999253173 38802471376396601531179985)
      ·
        refine ⟨29101853532297451148384989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38802471376396601531179985 29101853532297451148384989)
        ·
          refine ⟨10913195074611544180644371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29101853532297451148384989 10913195074611544180644371)
          ·
            refine ⟨16369792611917316270966557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10913195074611544180644371 16369792611917316270966557)
            ·
              refine ⟨6138672229468993601612459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16369792611917316270966557 6138672229468993601612459)
              ·
                refine ⟨9208008344203490402418689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138672229468993601612459 9208008344203490402418689)
                ·
                  refine ⟨6906006258152617801814017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9208008344203490402418689 6906006258152617801814017)
                  ·
                    refine ⟨5179504693614463351360513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6906006258152617801814017 5179504693614463351360513)
                    ·
                      refine ⟨3884628520210847513520385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179504693614463351360513 3884628520210847513520385)
                      ·
                        rfl

theorem cell23_7565287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_7565287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565287 prefixEnd_7565287 := by exact prefixLift 7565287
  have htrace : WordTrace (prefixWord ++ tailWord_7565287) baseStart_7565287 baseEnd_7565287 := by
    simpa [prefixWord, tailWord_7565287, baseEnd_7565287] using wordTrace_append hprefix tailTrace_7565287
  have hstable : (prefixWord ++ tailWord_7565287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565287).length < 2 ^ (prefixWord ++ tailWord_7565287).sum := by decide
  have hdescent : baseEnd_7565287 < baseStart_7565287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565309 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_7565309 : Nat := 118140960795 + 7565309 * 2 ^ 59
def prefixEnd_7565309 : Nat := 4983230072969 + 3 ^ 40 * 7565309 * 2
def baseEnd_7565309 : Nat := 3884639816785246427445283

theorem tailTrace_7565309 : CollatzResearch.WordTrace tailWord_7565309 prefixEnd_7565309 3884639816785246427445283 := by
  unfold tailWord_7565309
  simp only [CollatzResearch.WordTrace]
  refine ⟨275929487749185019756802981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183952991832790013171201987 275929487749185019756802981)
  ·
    refine ⟨51736778952972191204400559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275929487749185019756802981 51736778952972191204400559)
    ·
      refine ⟨77605168429458286806600839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51736778952972191204400559 77605168429458286806600839)
      ·
        refine ⟨116407752644187430209901259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77605168429458286806600839 116407752644187430209901259)
        ·
          refine ⟨174611628966281145314851889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116407752644187430209901259 174611628966281145314851889)
          ·
            refine ⟨130958721724710858986138917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174611628966281145314851889 130958721724710858986138917)
            ·
              refine ⟨24554760323383286059901047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130958721724710858986138917 24554760323383286059901047)
              ·
                refine ⟨36832140485074929089851571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24554760323383286059901047 36832140485074929089851571)
                ·
                  refine ⟨55248210727612393634777357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36832140485074929089851571 55248210727612393634777357)
                  ·
                    refine ⟨20718079022854647613041509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55248210727612393634777357 20718079022854647613041509)
                    ·
                      refine ⟨3884639816785246427445283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20718079022854647613041509 3884639816785246427445283)
                      ·
                        rfl

theorem cell23_7565309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_7565309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565309 prefixEnd_7565309 := by exact prefixLift 7565309
  have htrace : WordTrace (prefixWord ++ tailWord_7565309) baseStart_7565309 baseEnd_7565309 := by
    simpa [prefixWord, tailWord_7565309, baseEnd_7565309] using wordTrace_append hprefix tailTrace_7565309
  have hstable : (prefixWord ++ tailWord_7565309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565309).length < 2 ^ (prefixWord ++ tailWord_7565309).sum := by decide
  have hdescent : baseEnd_7565309 < baseStart_7565309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565310 : List Nat := [4, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_7565310 : Nat := 118140960795 + 7565310 * 2 ^ 59
def prefixEnd_7565310 : Nat := 4983230072969 + 3 ^ 40 * 7565310 * 2
def baseEnd_7565310 : Nat := 431626703362877880392531

theorem tailTrace_7565310 : CollatzResearch.WordTrace tailWord_7565310 prefixEnd_7565310 431626703362877880392531 := by
  unfold tailWord_7565310
  simp only [CollatzResearch.WordTrace]
  refine ⟨34491190527772674615948673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183953016148120931285059589 34491190527772674615948673)
  ·
    refine ⟨25868392895829505961961505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34491190527772674615948673 25868392895829505961961505)
    ·
      refine ⟨19401294671872129471471129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25868392895829505961961505 19401294671872129471471129)
      ·
        refine ⟨14550971003904097103603347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19401294671872129471471129 14550971003904097103603347)
        ·
          refine ⟨21826456505856145655405021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14550971003904097103603347 21826456505856145655405021)
          ·
            refine ⟨8184921189696054620776883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21826456505856145655405021 8184921189696054620776883)
            ·
              refine ⟨12277381784544081931165325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8184921189696054620776883 12277381784544081931165325)
              ·
                refine ⟨4604018169204030724186997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12277381784544081931165325 4604018169204030724186997)
                ·
                  refine ⟨431626703362877880392531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4604018169204030724186997 431626703362877880392531)
                  ·
                    rfl

theorem cell23_7565310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_7565310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565310 prefixEnd_7565310 := by exact prefixLift 7565310
  have htrace : WordTrace (prefixWord ++ tailWord_7565310) baseStart_7565310 baseEnd_7565310 := by
    simpa [prefixWord, tailWord_7565310, baseEnd_7565310] using wordTrace_append hprefix tailTrace_7565310
  have hstable : (prefixWord ++ tailWord_7565310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565310).length < 2 ^ (prefixWord ++ tailWord_7565310).sum := by decide
  have hdescent : baseEnd_7565310 < baseStart_7565310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565326 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7565326 : Nat := 118140960795 + 7565326 * 2 ^ 59
def prefixEnd_7565326 : Nat := 4983230072969 + 3 ^ 40 * 7565326 * 2
def baseEnd_7565326 : Nat := 3884648545956372860932705

theorem tailTrace_7565326 : CollatzResearch.WordTrace tailWord_7565326 prefixEnd_7565326 3884648545956372860932705 := by
  unfold tailWord_7565326
  simp only [CollatzResearch.WordTrace]
  refine ⟨34491263473765428957521479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183953405193415621106781221 34491263473765428957521479)
  ·
    refine ⟨51736895210648143436282219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34491263473765428957521479 51736895210648143436282219)
    ·
      refine ⟨77605342815972215154423329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51736895210648143436282219 77605342815972215154423329)
      ·
        refine ⟨58204007111979161365817497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77605342815972215154423329 58204007111979161365817497)
        ·
          refine ⟨43653005333984371024363123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58204007111979161365817497 43653005333984371024363123)
          ·
            refine ⟨65479508000976556536544685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43653005333984371024363123 65479508000976556536544685)
            ·
              refine ⟨24554815500366208701204257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65479508000976556536544685 24554815500366208701204257)
              ·
                refine ⟨18416111625274656525903193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24554815500366208701204257 18416111625274656525903193)
                ·
                  refine ⟨13812083718955992394427395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18416111625274656525903193 13812083718955992394427395)
                  ·
                    refine ⟨20718125578433988591641093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13812083718955992394427395 20718125578433988591641093)
                    ·
                      refine ⟨3884648545956372860932705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20718125578433988591641093 3884648545956372860932705)
                      ·
                        rfl

theorem cell23_7565326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7565326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565326 prefixEnd_7565326 := by exact prefixLift 7565326
  have htrace : WordTrace (prefixWord ++ tailWord_7565326) baseStart_7565326 baseEnd_7565326 := by
    simpa [prefixWord, tailWord_7565326, baseEnd_7565326] using wordTrace_append hprefix tailTrace_7565326
  have hstable : (prefixWord ++ tailWord_7565326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565326).length < 2 ^ (prefixWord ++ tailWord_7565326).sum := by decide
  have hdescent : baseEnd_7565326 < baseStart_7565326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565346 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_7565346 : Nat := 118140960795 + 7565346 * 2 ^ 59
def prefixEnd_7565346 : Nat := 4983230072969 + 3 ^ 40 * 7565346 * 2
def baseEnd_7565346 : Nat := 3884658815569462782682613

theorem tailTrace_7565346 : CollatzResearch.WordTrace tailWord_7565346 prefixEnd_7565346 3884658815569462782682613 := by
  unfold tailWord_7565346
  simp only [CollatzResearch.WordTrace]
  refine ⟨68982709312512743768974973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183953891500033983383933261 68982709312512743768974973)
  ·
    refine ⟨25868515992192278913365615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68982709312512743768974973 25868515992192278913365615)
    ·
      refine ⟨38802773988288418370048423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25868515992192278913365615 38802773988288418370048423)
      ·
        refine ⟨58204160982432627555072635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38802773988288418370048423 58204160982432627555072635)
        ·
          refine ⟨87306241473648941332608953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58204160982432627555072635 87306241473648941332608953)
          ·
            refine ⟨65479681105236705999456715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87306241473648941332608953 65479681105236705999456715)
            ·
              refine ⟨98219521657855058999185073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65479681105236705999456715 98219521657855058999185073)
              ·
                refine ⟨73664641243391294249388805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98219521657855058999185073 73664641243391294249388805)
                ·
                  refine ⟨13812120233135867671760401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73664641243391294249388805 13812120233135867671760401)
                  ·
                    refine ⟨10359090174851900753820301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13812120233135867671760401 10359090174851900753820301)
                    ·
                      refine ⟨3884658815569462782682613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10359090174851900753820301 3884658815569462782682613)
                      ·
                        rfl

theorem cell23_7565346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_7565346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565346 prefixEnd_7565346 := by exact prefixLift 7565346
  have htrace : WordTrace (prefixWord ++ tailWord_7565346) baseStart_7565346 baseEnd_7565346 := by
    simpa [prefixWord, tailWord_7565346, baseEnd_7565346] using wordTrace_append hprefix tailTrace_7565346
  have hstable : (prefixWord ++ tailWord_7565346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565346).length < 2 ^ (prefixWord ++ tailWord_7565346).sum := by decide
  have hdescent : baseEnd_7565346 < baseStart_7565346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565386 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_7565386 : Nat := 118140960795 + 7565386 * 2 ^ 59
def prefixEnd_7565386 : Nat := 4983230072969 + 3 ^ 40 * 7565386 * 2
def baseEnd_7565386 : Nat := 3884679354795642626182429

theorem tailTrace_7565386 : CollatzResearch.WordTrace tailWord_7565386 prefixEnd_7565386 3884679354795642626182429 := by
  unfold tailWord_7565386
  simp only [CollatzResearch.WordTrace]
  refine ⟨68983074042476515476839003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183954864113270707938237341 68983074042476515476839003)
  ·
    refine ⟨103474611063714773215258505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68983074042476515476839003 103474611063714773215258505)
    ·
      refine ⟨77605958297786079911443879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103474611063714773215258505 77605958297786079911443879)
      ·
        refine ⟨116408937446679119867165819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77605958297786079911443879 116408937446679119867165819)
        ·
          refine ⟨174613406170018679800748729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116408937446679119867165819 174613406170018679800748729)
          ·
            refine ⟨130960054627514009850561547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174613406170018679800748729 130960054627514009850561547)
            ·
              refine ⟨196440081941271014775842321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130960054627514009850561547 196440081941271014775842321)
              ·
                refine ⟨147330061455953261081881741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196440081941271014775842321 147330061455953261081881741)
                ·
                  refine ⟨55248773045982472905705653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147330061455953261081881741 55248773045982472905705653)
                  ·
                    refine ⟨5179572473060856834909905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55248773045982472905705653 5179572473060856834909905)
                    ·
                      refine ⟨3884679354795642626182429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179572473060856834909905 3884679354795642626182429)
                      ·
                        rfl

theorem cell23_7565386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_7565386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565386 prefixEnd_7565386 := by exact prefixLift 7565386
  have htrace : WordTrace (prefixWord ++ tailWord_7565386) baseStart_7565386 baseEnd_7565386 := by
    simpa [prefixWord, tailWord_7565386, baseEnd_7565386] using wordTrace_append hprefix tailTrace_7565386
  have hstable : (prefixWord ++ tailWord_7565386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565386).length < 2 ^ (prefixWord ++ tailWord_7565386).sum := by decide
  have hdescent : baseEnd_7565386 < baseStart_7565386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565420 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 2, 3, 2]
def baseStart_7565420 : Nat := 118140960795 + 7565420 * 2 ^ 59
def prefixEnd_7565420 : Nat := 4983230072969 + 3 ^ 40 * 7565420 * 2
def baseEnd_7565420 : Nat := 3884696813137895493157273

theorem tailTrace_7565420 : CollatzResearch.WordTrace tailWord_7565420 prefixEnd_7565420 3884696813137895493157273 := by
  unfold tailWord_7565420
  simp only [CollatzResearch.WordTrace]
  refine ⟨137966768125891442857046857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183955690834521923809395809 137966768125891442857046857)
  ·
    refine ⟨103475076094418582142785143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137966768125891442857046857 103475076094418582142785143)
    ·
      refine ⟨155212614141627873214177715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103475076094418582142785143 155212614141627873214177715)
      ·
        refine ⟨232818921212441809821266573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155212614141627873214177715 232818921212441809821266573)
        ·
          refine ⟨87307095454665678682974965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232818921212441809821266573 87307095454665678682974965)
          ·
            refine ⟨8185040198874907376528903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87307095454665678682974965 8185040198874907376528903)
            ·
              refine ⟨12277560298312361064793355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8185040198874907376528903 12277560298312361064793355)
              ·
                refine ⟨18416340447468541597190033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12277560298312361064793355 18416340447468541597190033)
                ·
                  refine ⟨13812255335601406197892525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18416340447468541597190033 13812255335601406197892525)
                  ·
                    refine ⟨5179595750850527324209697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13812255335601406197892525 5179595750850527324209697)
                    ·
                      refine ⟨3884696813137895493157273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179595750850527324209697 3884696813137895493157273)
                      ·
                        rfl

theorem cell23_7565420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_7565420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565420 prefixEnd_7565420 := by exact prefixLift 7565420
  have htrace : WordTrace (prefixWord ++ tailWord_7565420) baseStart_7565420 baseEnd_7565420 := by
    simpa [prefixWord, tailWord_7565420, baseEnd_7565420] using wordTrace_append hprefix tailTrace_7565420
  have hstable : (prefixWord ++ tailWord_7565420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565420).length < 2 ^ (prefixWord ++ tailWord_7565420).sum := by decide
  have hdescent : baseEnd_7565420 < baseStart_7565420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565426 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_7565426 : Nat := 118140960795 + 7565426 * 2 ^ 59
def prefixEnd_7565426 : Nat := 4983230072969 + 3 ^ 40 * 7565426 * 2
def baseEnd_7565426 : Nat := 1294899964673940823227415

theorem tailTrace_7565426 : CollatzResearch.WordTrace tailWord_7565426 prefixEnd_7565426 1294899964673940823227415 := by
  unfold tailWord_7565426
  simp only [CollatzResearch.WordTrace]
  refine ⟨68983438772440287184703033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183955836726507432492541421 68983438772440287184703033)
  ·
    refine ⟨51737579079330215388527275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68983438772440287184703033 51737579079330215388527275)
    ·
      refine ⟨77606368618995323082790913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51737579079330215388527275 77606368618995323082790913)
      ·
        refine ⟨58204776464246492312093185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77606368618995323082790913 58204776464246492312093185)
        ·
          refine ⟨43653582348184869234069889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58204776464246492312093185 43653582348184869234069889)
          ·
            refine ⟨32740186761138651925552417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43653582348184869234069889 32740186761138651925552417)
            ·
              refine ⟨24555140070853988944164313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32740186761138651925552417 24555140070853988944164313)
              ·
                refine ⟨18416355053140491708123235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24555140070853988944164313 18416355053140491708123235)
                ·
                  refine ⟨27624532579710737562184853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18416355053140491708123235 27624532579710737562184853)
                  ·
                    refine ⟨1294899964673940823227415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27624532579710737562184853 1294899964673940823227415)
                    ·
                      rfl

theorem cell23_7565426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_7565426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565426 prefixEnd_7565426 := by exact prefixLift 7565426
  have htrace : WordTrace (prefixWord ++ tailWord_7565426) baseStart_7565426 baseEnd_7565426 := by
    simpa [prefixWord, tailWord_7565426, baseEnd_7565426] using wordTrace_append hprefix tailTrace_7565426
  have hstable : (prefixWord ++ tailWord_7565426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565426).length < 2 ^ (prefixWord ++ tailWord_7565426).sum := by decide
  have hdescent : baseEnd_7565426 < baseStart_7565426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565430 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_7565430 : Nat := 118140960795 + 7565430 * 2 ^ 59
def prefixEnd_7565430 : Nat := 4983230072969 + 3 ^ 40 * 7565430 * 2
def baseEnd_7565430 : Nat := 1294900649314813484677409

theorem tailTrace_7565430 : CollatzResearch.WordTrace tailWord_7565430 prefixEnd_7565430 1294900649314813484677409 := by
  unfold tailWord_7565430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17245868811359166088872359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183955933987831104947971829 17245868811359166088872359)
  ·
    refine ⟨25868803217038749133308539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17245868811359166088872359 25868803217038749133308539)
    ·
      refine ⟨38803204825558123699962809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25868803217038749133308539 38803204825558123699962809)
      ·
        refine ⟨29102403619168592774972107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38803204825558123699962809 29102403619168592774972107)
        ·
          refine ⟨43653605428752889162458161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29102403619168592774972107 43653605428752889162458161)
          ·
            refine ⟨32740204071564666871843621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43653605428752889162458161 32740204071564666871843621)
            ·
              refine ⟨6138788263418375038470679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32740204071564666871843621 6138788263418375038470679)
              ·
                refine ⟨9208182395127562557706019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138788263418375038470679 9208182395127562557706019)
                ·
                  refine ⟨13812273592691343836559029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9208182395127562557706019 13812273592691343836559029)
                  ·
                    refine ⟨1294900649314813484677409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13812273592691343836559029 1294900649314813484677409)
                    ·
                      rfl

theorem cell23_7565430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_7565430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565430 prefixEnd_7565430 := by exact prefixLift 7565430
  have htrace : WordTrace (prefixWord ++ tailWord_7565430) baseStart_7565430 baseEnd_7565430 := by
    simpa [prefixWord, tailWord_7565430, baseEnd_7565430] using wordTrace_append hprefix tailTrace_7565430
  have hstable : (prefixWord ++ tailWord_7565430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565430).length < 2 ^ (prefixWord ++ tailWord_7565430).sum := by decide
  have hdescent : baseEnd_7565430 < baseStart_7565430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565433 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 4]
def baseStart_7565433 : Nat := 118140960795 + 7565433 * 2 ^ 59
def prefixEnd_7565433 : Nat := 4983230072969 + 3 ^ 40 * 7565433 * 2
def baseEnd_7565433 : Nat := 3884703488386403942294713

theorem tailTrace_7565433 : CollatzResearch.WordTrace tailWord_7565433 prefixEnd_7565433 3884703488386403942294713 := by
  unfold tailWord_7565433
  simp only [CollatzResearch.WordTrace]
  refine ⟨275934010400735788934316953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183956006933823859289544635 275934010400735788934316953)
  ·
    refine ⟨206950507800551841700737715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275934010400735788934316953 206950507800551841700737715)
    ·
      refine ⟨310425761700827762551106573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206950507800551841700737715 310425761700827762551106573)
      ·
        refine ⟨116409660637810410956664965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310425761700827762551106573 116409660637810410956664965)
        ·
          refine ⟨21826811369589452054374681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116409660637810410956664965 21826811369589452054374681)
          ·
            refine ⟨16370108527192089040781011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21826811369589452054374681 16370108527192089040781011)
            ·
              refine ⟨24555162790788133561171517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16370108527192089040781011 24555162790788133561171517)
              ·
                refine ⟨9208186046545550085439319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24555162790788133561171517 9208186046545550085439319)
                ·
                  refine ⟨13812279069818325128158979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9208186046545550085439319 13812279069818325128158979)
                  ·
                    refine ⟨20718418604727487692238469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13812279069818325128158979 20718418604727487692238469)
                    ·
                      refine ⟨3884703488386403942294713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20718418604727487692238469 3884703488386403942294713)
                      ·
                        rfl

theorem cell23_7565433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_7565433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565433 prefixEnd_7565433 := by exact prefixLift 7565433
  have htrace : WordTrace (prefixWord ++ tailWord_7565433) baseStart_7565433 baseEnd_7565433 := by
    simpa [prefixWord, tailWord_7565433, baseEnd_7565433] using wordTrace_append hprefix tailTrace_7565433
  have hstable : (prefixWord ++ tailWord_7565433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565433).length < 2 ^ (prefixWord ++ tailWord_7565433).sum := by decide
  have hdescent : baseEnd_7565433 < baseStart_7565433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565443 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 2, 4]
def baseStart_7565443 : Nat := 118140960795 + 7565443 * 2 ^ 59
def prefixEnd_7565443 : Nat := 4983230072969 + 3 ^ 40 * 7565443 * 2
def baseEnd_7565443 : Nat := 1294902874397649634389889

theorem tailTrace_7565443 : CollatzResearch.WordTrace tailWord_7565443 prefixEnd_7565443 1294902874397649634389889 := by
  unfold tailWord_7565443
  simp only [CollatzResearch.WordTrace]
  refine ⟨275934375130699560642180983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183956250087133040428120655 275934375130699560642180983)
  ·
    refine ⟨413901562696049340963271475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275934375130699560642180983 413901562696049340963271475)
    ·
      refine ⟨620852344044074011444907213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413901562696049340963271475 620852344044074011444907213)
      ·
        refine ⟨232819629016527754291840205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620852344044074011444907213 232819629016527754291840205)
        ·
          refine ⟨87307360881197907859440077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232819629016527754291840205 87307360881197907859440077)
          ·
            refine ⟨32740260330449215447290029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87307360881197907859440077 32740260330449215447290029)
            ·
              refine ⟨12277597623918455792733761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32740260330449215447290029 12277597623918455792733761)
              ·
                refine ⟨9208198217938841844550321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277597623918455792733761 9208198217938841844550321)
                ·
                  refine ⟨6906148663454131383412741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9208198217938841844550321 6906148663454131383412741)
                  ·
                    refine ⟨1294902874397649634389889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6906148663454131383412741 1294902874397649634389889)
                    ·
                      rfl

theorem cell23_7565443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 4].length) (baseStart_7565443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565443 prefixEnd_7565443 := by exact prefixLift 7565443
  have htrace : WordTrace (prefixWord ++ tailWord_7565443) baseStart_7565443 baseEnd_7565443 := by
    simpa [prefixWord, tailWord_7565443, baseEnd_7565443] using wordTrace_append hprefix tailTrace_7565443
  have hstable : (prefixWord ++ tailWord_7565443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565443).length < 2 ^ (prefixWord ++ tailWord_7565443).sum := by decide
  have hdescent : baseEnd_7565443 < baseStart_7565443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565450 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_7565450 : Nat := 118140960795 + 7565450 * 2 ^ 59
def prefixEnd_7565450 : Nat := 4983230072969 + 3 ^ 40 * 7565450 * 2
def baseEnd_7565450 : Nat := 3884712217557530375782135

theorem tailTrace_7565450 : CollatzResearch.WordTrace tailWord_7565450 prefixEnd_7565450 3884712217557530375782135 := by
  unfold tailWord_7565450
  simp only [CollatzResearch.WordTrace]
  refine ⟨68983657610418550209421451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183956420294449467225123869 68983657610418550209421451)
  ·
    refine ⟨103475486415627825314132177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68983657610418550209421451 103475486415627825314132177)
    ·
      refine ⟨77606614811720868985599133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103475486415627825314132177 77606614811720868985599133)
      ·
        refine ⟨29102480554395325869599675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77606614811720868985599133 29102480554395325869599675)
        ·
          refine ⟨43653720831592988804399513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29102480554395325869599675 43653720831592988804399513)
          ·
            refine ⟨32740290623694741603299635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43653720831592988804399513 32740290623694741603299635)
            ·
              refine ⟨49110435935542112404949453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32740290623694741603299635 49110435935542112404949453)
              ·
                refine ⟨18416413475828292151856045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49110435935542112404949453 18416413475828292151856045)
                ·
                  refine ⟨6906155053435609556946017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18416413475828292151856045 6906155053435609556946017)
                  ·
                    refine ⟨5179616290076707167709513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6906155053435609556946017 5179616290076707167709513)
                    ·
                      refine ⟨3884712217557530375782135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179616290076707167709513 3884712217557530375782135)
                      ·
                        rfl

theorem cell23_7565450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_7565450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565450 prefixEnd_7565450 := by exact prefixLift 7565450
  have htrace : WordTrace (prefixWord ++ tailWord_7565450) baseStart_7565450 baseEnd_7565450 := by
    simpa [prefixWord, tailWord_7565450, baseEnd_7565450] using wordTrace_append hprefix tailTrace_7565450
  have hstable : (prefixWord ++ tailWord_7565450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565450).length < 2 ^ (prefixWord ++ tailWord_7565450).sum := by decide
  have hdescent : baseEnd_7565450 < baseStart_7565450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565473 : List Nat := [1, 2, 3, 3, 1, 4, 2, 7]
def baseStart_7565473 : Nat := 118140960795 + 7565473 * 2 ^ 59
def prefixEnd_7565473 : Nat := 4983230072969 + 3 ^ 40 * 7565473 * 2
def baseEnd_7565473 : Nat := 143878667689354955029427

theorem tailTrace_7565473 : CollatzResearch.WordTrace tailWord_7565473 prefixEnd_7565473 143878667689354955029427 := by
  unfold tailWord_7565473
  simp only [CollatzResearch.WordTrace]
  refine ⟨275935469320590875765773073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183956979547060583843848715 275935469320590875765773073)
  ·
    refine ⟨206951601990443156824329805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275935469320590875765773073 206951601990443156824329805)
    ·
      refine ⟨77606850746416183809123677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206951601990443156824329805 77606850746416183809123677)
      ·
        refine ⟨29102569029906068928421379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77606850746416183809123677 29102569029906068928421379)
        ·
          refine ⟨43653853544859103392632069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29102569029906068928421379 43653853544859103392632069)
          ·
            refine ⟨8185097539661081886118513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43653853544859103392632069 8185097539661081886118513)
            ·
              refine ⟨6138823154745811414588885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8185097539661081886118513 6138823154745811414588885)
              ·
                refine ⟨143878667689354955029427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6138823154745811414588885 143878667689354955029427)
                ·
                  rfl

theorem cell23_7565473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 7].length) (baseStart_7565473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565473 prefixEnd_7565473 := by exact prefixLift 7565473
  have htrace : WordTrace (prefixWord ++ tailWord_7565473) baseStart_7565473 baseEnd_7565473 := by
    simpa [prefixWord, tailWord_7565473, baseEnd_7565473] using wordTrace_append hprefix tailTrace_7565473
  have hstable : (prefixWord ++ tailWord_7565473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565473).length < 2 ^ (prefixWord ++ tailWord_7565473).sum := by decide
  have hdescent : baseEnd_7565473 < baseStart_7565473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565543 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7565543 : Nat := 118140960795 + 7565543 * 2 ^ 59
def prefixEnd_7565543 : Nat := 4983230072969 + 3 ^ 40 * 7565543 * 2
def baseEnd_7565543 : Nat := 3884759971258398511919207

theorem tailTrace_7565543 : CollatzResearch.WordTrace tailWord_7565543 prefixEnd_7565543 3884759971258398511919207 := by
  unfold tailWord_7565543
  simp only [CollatzResearch.WordTrace]
  refine ⟨275938022430337277720821283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183958681620224851813880855 275938022430337277720821283)
  ·
    refine ⟨413907033645505916581231925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275938022430337277720821283 413907033645505916581231925)
    ·
      refine ⟨38803784404266179679490493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 413907033645505916581231925 38803784404266179679490493)
      ·
        refine ⟨14551419151599817379808935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38803784404266179679490493 14551419151599817379808935)
        ·
          refine ⟨21827128727399726069713403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14551419151599817379808935 21827128727399726069713403)
          ·
            refine ⟨32740693091099589104570105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21827128727399726069713403 32740693091099589104570105)
            ·
              refine ⟨24555519818324691828427579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32740693091099589104570105 24555519818324691828427579)
              ·
                refine ⟨36833279727487037742641369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24555519818324691828427579 36833279727487037742641369)
                ·
                  refine ⟨27624959795615278306981027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36833279727487037742641369 27624959795615278306981027)
                  ·
                    refine ⟨41437439693422917460471541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27624959795615278306981027 41437439693422917460471541)
                    ·
                      refine ⟨3884759971258398511919207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41437439693422917460471541 3884759971258398511919207)
                      ·
                        rfl

theorem cell23_7565543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7565543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565543 prefixEnd_7565543 := by exact prefixLift 7565543
  have htrace : WordTrace (prefixWord ++ tailWord_7565543) baseStart_7565543 baseEnd_7565543 := by
    simpa [prefixWord, tailWord_7565543, baseEnd_7565543] using wordTrace_append hprefix tailTrace_7565543
  have hstable : (prefixWord ++ tailWord_7565543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565543).length < 2 ^ (prefixWord ++ tailWord_7565543).sum := by decide
  have hdescent : baseEnd_7565543 < baseStart_7565543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565570 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_7565570 : Nat := 118140960795 + 7565570 * 2 ^ 59
def prefixEnd_7565570 : Nat := 4983230072969 + 3 ^ 40 * 7565570 * 2
def baseEnd_7565570 : Nat := 3884773835236069906281583

theorem tailTrace_7565570 : CollatzResearch.WordTrace tailWord_7565570 prefixEnd_7565570 3884773835236069906281583 := by
  unfold tailWord_7565570
  simp only [CollatzResearch.WordTrace]
  refine ⟨68984751800309865333013541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183959338134159640888036109 68984751800309865333013541)
  ·
    refine ⟨12934640962558099749940039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68984751800309865333013541 12934640962558099749940039)
    ·
      refine ⟨19401961443837149624910059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12934640962558099749940039 19401961443837149624910059)
      ·
        refine ⟨29102942165755724437365089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19401961443837149624910059 29102942165755724437365089)
        ·
          refine ⟨21827206624316793328023817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29102942165755724437365089 21827206624316793328023817)
          ·
            refine ⟨16370404968237594996017863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21827206624316793328023817 16370404968237594996017863)
            ·
              refine ⟨24555607452356392494026795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16370404968237594996017863 24555607452356392494026795)
              ·
                refine ⟨36833411178534588741040193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24555607452356392494026795 36833411178534588741040193)
                ·
                  refine ⟨27625058383900941555780145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36833411178534588741040193 27625058383900941555780145)
                  ·
                    refine ⟨20718793787925706166835109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27625058383900941555780145 20718793787925706166835109)
                    ·
                      refine ⟨3884773835236069906281583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20718793787925706166835109 3884773835236069906281583)
                      ·
                        rfl

theorem cell23_7565570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_7565570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565570 prefixEnd_7565570 := by exact prefixLift 7565570
  have htrace : WordTrace (prefixWord ++ tailWord_7565570) baseStart_7565570 baseEnd_7565570 := by
    simpa [prefixWord, tailWord_7565570, baseEnd_7565570] using wordTrace_append hprefix tailTrace_7565570
  have hstable : (prefixWord ++ tailWord_7565570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565570).length < 2 ^ (prefixWord ++ tailWord_7565570).sum := by decide
  have hdescent : baseEnd_7565570 < baseStart_7565570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565597 : List Nat := [1, 4, 2, 3, 2, 1, 2, 3, 5]
def baseStart_7565597 : Nat := 118140960795 + 7565597 * 2 ^ 59
def prefixEnd_7565597 : Nat := 4983230072969 + 3 ^ 40 * 7565597 * 2
def baseEnd_7565597 : Nat := 431643077690415700071551

theorem tailTrace_7565597 : CollatzResearch.WordTrace tailWord_7565597 prefixEnd_7565597 431643077690415700071551 := by
  unfold tailWord_7565597
  simp only [CollatzResearch.WordTrace]
  refine ⟨275939991972141644943287045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183959994648094429962191363 275939991972141644943287045)
  ·
    refine ⟨51738748494776558426866321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275939991972141644943287045 51738748494776558426866321)
    ·
      refine ⟨38804061371082418820149741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51738748494776558426866321 38804061371082418820149741)
      ·
        refine ⟨14551523014155907057556153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38804061371082418820149741 14551523014155907057556153)
        ·
          refine ⟨10913642260616930293167115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14551523014155907057556153 10913642260616930293167115)
          ·
            refine ⟨16370463390925395439750673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10913642260616930293167115 16370463390925395439750673)
            ·
              refine ⟨12277847543194046579813005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16370463390925395439750673 12277847543194046579813005)
              ·
                refine ⟨4604192828697767467429877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12277847543194046579813005 4604192828697767467429877)
                ·
                  refine ⟨431643077690415700071551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4604192828697767467429877 431643077690415700071551)
                  ·
                    rfl

theorem cell23_7565597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_7565597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565597 prefixEnd_7565597 := by exact prefixLift 7565597
  have htrace : WordTrace (prefixWord ++ tailWord_7565597) baseStart_7565597 baseEnd_7565597 := by
    simpa [prefixWord, tailWord_7565597, baseEnd_7565597] using wordTrace_append hprefix tailTrace_7565597
  have hstable : (prefixWord ++ tailWord_7565597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565597).length < 2 ^ (prefixWord ++ tailWord_7565597).sum := by decide
  have hdescent : baseEnd_7565597 < baseStart_7565597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565656 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_7565656 : Nat := 118140960795 + 7565656 * 2 ^ 59
def prefixEnd_7565656 : Nat := 4983230072969 + 3 ^ 40 * 7565656 * 2
def baseEnd_7565656 : Nat := 3884817994572356569806187

theorem tailTrace_7565656 : CollatzResearch.WordTrace tailWord_7565656 prefixEnd_7565656 3884817994572356569806187 := by
  unfold tailWord_7565656
  simp only [CollatzResearch.WordTrace]
  refine ⟨137971071939463949009842411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183961429252618598679789881 137971071939463949009842411)
  ·
    refine ⟨206956607909195923514763617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137971071939463949009842411 206956607909195923514763617)
    ·
      refine ⟨155217455931896942636072713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206956607909195923514763617 155217455931896942636072713)
      ·
        refine ⟨116413091948922706977054535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155217455931896942636072713 116413091948922706977054535)
        ·
          refine ⟨174619637923384060465581803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116413091948922706977054535 174619637923384060465581803)
          ·
            refine ⟨261929456885076090698372705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174619637923384060465581803 261929456885076090698372705)
            ·
              refine ⟨196447092663807068023779529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261929456885076090698372705 196447092663807068023779529)
              ·
                refine ⟨147335319497855301017834647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196447092663807068023779529 147335319497855301017834647)
                ·
                  refine ⟨221002979246782951526751971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147335319497855301017834647 221002979246782951526751971)
                  ·
                    refine ⟨331504468870174427290127957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221002979246782951526751971 331504468870174427290127957)
                    ·
                      refine ⟨3884817994572356569806187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 331504468870174427290127957 3884817994572356569806187)
                      ·
                        rfl

theorem cell23_7565656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_7565656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565656 prefixEnd_7565656 := by exact prefixLift 7565656
  have htrace : WordTrace (prefixWord ++ tailWord_7565656) baseStart_7565656 baseEnd_7565656 := by
    simpa [prefixWord, tailWord_7565656, baseEnd_7565656] using wordTrace_append hprefix tailTrace_7565656
  have hstable : (prefixWord ++ tailWord_7565656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565656).length < 2 ^ (prefixWord ++ tailWord_7565656).sum := by decide
  have hdescent : baseEnd_7565656 < baseStart_7565656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565707 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 2, 3, 2]
def baseStart_7565707 : Nat := 118140960795 + 7565707 * 2 ^ 59
def prefixEnd_7565707 : Nat := 4983230072969 + 3 ^ 40 * 7565707 * 2
def baseEnd_7565707 : Nat := 3884844182085735870268453

theorem tailTrace_7565707 : CollatzResearch.WordTrace tailWord_7565707 prefixEnd_7565707 3884844182085735870268453 := by
  unfold tailWord_7565707
  simp only [CollatzResearch.WordTrace]
  refine ⟨275944004001743133729791375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183962669334495422486527583 275944004001743133729791375)
  ·
    refine ⟨413916006002614700594687063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275944004001743133729791375 413916006002614700594687063)
    ·
      refine ⟨620874009003922050892030595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413916006002614700594687063 620874009003922050892030595)
      ·
        refine ⟨931311013505883076338045893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620874009003922050892030595 931311013505883076338045893)
        ·
          refine ⟨174620815032353076813383605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 931311013505883076338045893 174620815032353076813383605)
          ·
            refine ⟨16370701409283100951254713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174620815032353076813383605 16370701409283100951254713)
            ·
              refine ⟨12278026056962325713441035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16370701409283100951254713 12278026056962325713441035)
              ·
                refine ⟨18417039085443488570161553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12278026056962325713441035 18417039085443488570161553)
                ·
                  refine ⟨13812779314082616427621165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18417039085443488570161553 13812779314082616427621165)
                  ·
                    refine ⟨5179792242780981160357937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13812779314082616427621165 5179792242780981160357937)
                    ·
                      refine ⟨3884844182085735870268453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179792242780981160357937 3884844182085735870268453)
                      ·
                        rfl

theorem cell23_7565707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 3, 2].length) (baseStart_7565707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565707 prefixEnd_7565707 := by exact prefixLift 7565707
  have htrace : WordTrace (prefixWord ++ tailWord_7565707) baseStart_7565707 baseEnd_7565707 := by
    simpa [prefixWord, tailWord_7565707, baseEnd_7565707] using wordTrace_append hprefix tailTrace_7565707
  have hstable : (prefixWord ++ tailWord_7565707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565707).length < 2 ^ (prefixWord ++ tailWord_7565707).sum := by decide
  have hdescent : baseEnd_7565707 < baseStart_7565707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565731 : List Nat := [1, 1, 1, 4, 1, 6, 2, 2, 1, 1, 3]
def baseStart_7565731 : Nat := 118140960795 + 7565731 * 2 ^ 59
def prefixEnd_7565731 : Nat := 4983230072969 + 3 ^ 40 * 7565731 * 2
def baseEnd_7565731 : Nat := 3884856505621443776368343

theorem tailTrace_7565731 : CollatzResearch.WordTrace tailWord_7565731 prefixEnd_7565731 3884856505621443776368343 := by
  unfold tailWord_7565731
  simp only [CollatzResearch.WordTrace]
  refine ⟨275944879353656185828665047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183963252902437457219110031 275944879353656185828665047)
  ·
    refine ⟨413917319030484278742997571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275944879353656185828665047 413917319030484278742997571)
    ·
      refine ⟨620875978545726418114496357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413917319030484278742997571 620875978545726418114496357)
      ·
        refine ⟨116414245977323703396468067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 620875978545726418114496357 116414245977323703396468067)
        ·
          refine ⟨174621368965985555094702101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116414245977323703396468067 174621368965985555094702101)
          ·
            refine ⟨8185376670280572895064161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174621368965985555094702101 8185376670280572895064161)
            ·
              refine ⟨6139032502710429671298121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8185376670280572895064161 6139032502710429671298121)
              ·
                refine ⟨4604274377032822253473591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139032502710429671298121 4604274377032822253473591)
                ·
                  refine ⟨6906411565549233380210387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604274377032822253473591 6906411565549233380210387)
                  ·
                    refine ⟨10359617348323850070315581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6906411565549233380210387 10359617348323850070315581)
                    ·
                      refine ⟨3884856505621443776368343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10359617348323850070315581 3884856505621443776368343)
                      ·
                        rfl

theorem cell23_7565731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_7565731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565731 prefixEnd_7565731 := by exact prefixLift 7565731
  have htrace : WordTrace (prefixWord ++ tailWord_7565731) baseStart_7565731 baseEnd_7565731 := by
    simpa [prefixWord, tailWord_7565731, baseEnd_7565731] using wordTrace_append hprefix tailTrace_7565731
  have hstable : (prefixWord ++ tailWord_7565731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565731).length < 2 ^ (prefixWord ++ tailWord_7565731).sum := by decide
  have hdescent : baseEnd_7565731 < baseStart_7565731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565733 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_7565733 : Nat := 118140960795 + 7565733 * 2 ^ 59
def prefixEnd_7565733 : Nat := 4983230072969 + 3 ^ 40 * 7565733 * 2
def baseEnd_7565733 : Nat := 3884857532582752768543333

theorem tailTrace_7565733 : CollatzResearch.WordTrace tailWord_7565733 prefixEnd_7565733 3884857532582752768543333 := by
  unfold tailWord_7565733
  simp only [CollatzResearch.WordTrace]
  refine ⟨275944952299648940170237853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183963301533099293446825235 275944952299648940170237853)
  ·
    refine ⟨103479357112368352563839195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275944952299648940170237853 103479357112368352563839195)
    ·
      refine ⟨155219035668552528845758793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103479357112368352563839195 155219035668552528845758793)
      ·
        refine ⟨116414276751414396634319095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155219035668552528845758793 116414276751414396634319095)
        ·
          refine ⟨174621415127121594951478643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116414276751414396634319095 174621415127121594951478643)
          ·
            refine ⟨261932122690682392427217965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174621415127121594951478643 261932122690682392427217965)
            ·
              refine ⟨98224546009005897160206737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261932122690682392427217965 98224546009005897160206737)
              ·
                refine ⟨73668409506754422870155053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98224546009005897160206737 73668409506754422870155053)
                ·
                  refine ⟨27625653565032908576308145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73668409506754422870155053 27625653565032908576308145)
                  ·
                    refine ⟨20719240173774681432231109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27625653565032908576308145 20719240173774681432231109)
                    ·
                      refine ⟨3884857532582752768543333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20719240173774681432231109 3884857532582752768543333)
                      ·
                        rfl

theorem cell23_7565733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_7565733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565733 prefixEnd_7565733 := by exact prefixLift 7565733
  have htrace : WordTrace (prefixWord ++ tailWord_7565733) baseStart_7565733 baseEnd_7565733 := by
    simpa [prefixWord, tailWord_7565733, baseEnd_7565733] using wordTrace_append hprefix tailTrace_7565733
  have hstable : (prefixWord ++ tailWord_7565733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565733).length < 2 ^ (prefixWord ++ tailWord_7565733).sum := by decide
  have hdescent : baseEnd_7565733 < baseStart_7565733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565770 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_7565770 : Nat := 118140960795 + 7565770 * 2 ^ 59
def prefixEnd_7565770 : Nat := 4983230072969 + 3 ^ 40 * 7565770 * 2
def baseEnd_7565770 : Nat := 3884876531366969123780663

theorem tailTrace_7565770 : CollatzResearch.WordTrace tailWord_7565770 prefixEnd_7565770 3884876531366969123780663 := by
  unfold tailWord_7565770
  simp only [CollatzResearch.WordTrace]
  refine ⟨68986575450128723872333691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183964201200343263659556509 68986575450128723872333691)
  ·
    refine ⟨103479863175193085808500537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68986575450128723872333691 103479863175193085808500537)
    ·
      refine ⟨77609897381394814356375403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103479863175193085808500537 77609897381394814356375403)
      ·
        refine ⟨116414846072092221534563105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77609897381394814356375403 116414846072092221534563105)
        ·
          refine ⟨87311134554069166150922329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116414846072092221534563105 87311134554069166150922329)
          ·
            refine ⟨65483350915551874613191747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87311134554069166150922329 65483350915551874613191747)
            ·
              refine ⟨98225026373327811919787621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65483350915551874613191747 98225026373327811919787621)
              ·
                refine ⟨18417192444998964734960179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98225026373327811919787621 18417192444998964734960179)
                ·
                  refine ⟨27625788667498447102440269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18417192444998964734960179 27625788667498447102440269)
                  ·
                    refine ⟨10359670750311917663415101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27625788667498447102440269 10359670750311917663415101)
                    ·
                      refine ⟨3884876531366969123780663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10359670750311917663415101 3884876531366969123780663)
                      ·
                        rfl

theorem cell23_7565770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_7565770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565770 prefixEnd_7565770 := by exact prefixLift 7565770
  have htrace : WordTrace (prefixWord ++ tailWord_7565770) baseStart_7565770 baseEnd_7565770 := by
    simpa [prefixWord, tailWord_7565770, baseEnd_7565770] using wordTrace_append hprefix tailTrace_7565770
  have hstable : (prefixWord ++ tailWord_7565770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565770).length < 2 ^ (prefixWord ++ tailWord_7565770).sum := by decide
  have hdescent : baseEnd_7565770 < baseStart_7565770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565803 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 2, 6]
def baseStart_7565803 : Nat := 118140960795 + 7565803 * 2 ^ 59
def prefixEnd_7565803 : Nat := 4983230072969 + 3 ^ 40 * 7565803 * 2
def baseEnd_7565803 : Nat := 1294964492076189164889337

theorem tailTrace_7565803 : CollatzResearch.WordTrace tailWord_7565803 prefixEnd_7565803 1294964492076189164889337 := by
  unfold tailWord_7565803
  simp only [CollatzResearch.WordTrace]
  refine ⟨275947505409395342125286063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183965003606263561416857375 275947505409395342125286063)
  ·
    refine ⟨413921258114093013187929095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275947505409395342125286063 413921258114093013187929095)
    ·
      refine ⟨620881887171139519781893643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413921258114093013187929095 620881887171139519781893643)
      ·
        refine ⟨931322830756709279672840465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620881887171139519781893643 931322830756709279672840465)
        ·
          refine ⟨698492123067531959754630349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931322830756709279672840465 698492123067531959754630349)
          ·
            refine ⟨261934546150324484907986381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 698492123067531959754630349 261934546150324484907986381)
            ·
              refine ⟨98225454806371681840494893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261934546150324484907986381 98225454806371681840494893)
              ·
                refine ⟨36834545552389380690185585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98225454806371681840494893 36834545552389380690185585)
                ·
                  refine ⟨27625909164292035517639189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36834545552389380690185585 27625909164292035517639189)
                  ·
                    refine ⟨1294964492076189164889337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27625909164292035517639189 1294964492076189164889337)
                    ·
                      rfl

theorem cell23_7565803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 6].length) (baseStart_7565803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565803 prefixEnd_7565803 := by exact prefixLift 7565803
  have htrace : WordTrace (prefixWord ++ tailWord_7565803) baseStart_7565803 baseEnd_7565803 := by
    simpa [prefixWord, tailWord_7565803, baseEnd_7565803] using wordTrace_append hprefix tailTrace_7565803
  have hstable : (prefixWord ++ tailWord_7565803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565803).length < 2 ^ (prefixWord ++ tailWord_7565803).sum := by decide
  have hdescent : baseEnd_7565803 < baseStart_7565803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565804 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 3]
def baseStart_7565804 : Nat := 118140960795 + 7565804 * 2 ^ 59
def prefixEnd_7565804 : Nat := 4983230072969 + 3 ^ 40 * 7565804 * 2
def baseEnd_7565804 : Nat := 3884893989709221990755507

theorem tailTrace_7565804 : CollatzResearch.WordTrace tailWord_7565804 prefixEnd_7565804 3884893989709221990755507 := by
  unfold tailWord_7565804
  simp only [CollatzResearch.WordTrace]
  refine ⟨137973770941195859648036233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183965027921594479530714977 137973770941195859648036233)
  ·
    refine ⟨103480328205896894736027175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137973770941195859648036233 103480328205896894736027175)
    ·
      refine ⟨155220492308845342104040763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103480328205896894736027175 155220492308845342104040763)
      ·
        refine ⟨232830738463268013156061145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155220492308845342104040763 232830738463268013156061145)
        ·
          refine ⟨174623053847451009867045859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232830738463268013156061145 174623053847451009867045859)
          ·
            refine ⟨261934580771176514800568789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174623053847451009867045859 261934580771176514800568789)
            ·
              refine ⟨6139091736824449565638331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 261934580771176514800568789 6139091736824449565638331)
              ·
                refine ⟨9208637605236674348457497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139091736824449565638331 9208637605236674348457497)
                ·
                  refine ⟨6906478203927505761343123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9208637605236674348457497 6906478203927505761343123)
                  ·
                    refine ⟨10359717305891258642014685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6906478203927505761343123 10359717305891258642014685)
                    ·
                      refine ⟨3884893989709221990755507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10359717305891258642014685 3884893989709221990755507)
                      ·
                        rfl

theorem cell23_7565804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_7565804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565804 prefixEnd_7565804 := by exact prefixLift 7565804
  have htrace : WordTrace (prefixWord ++ tailWord_7565804) baseStart_7565804 baseEnd_7565804 := by
    simpa [prefixWord, tailWord_7565804, baseEnd_7565804] using wordTrace_append hprefix tailTrace_7565804
  have hstable : (prefixWord ++ tailWord_7565804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565804).length < 2 ^ (prefixWord ++ tailWord_7565804).sum := by decide
  have hdescent : baseEnd_7565804 < baseStart_7565804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565827 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 6, 2, 2]
def baseStart_7565827 : Nat := 118140960795 + 7565827 * 2 ^ 59
def prefixEnd_7565827 : Nat := 4983230072969 + 3 ^ 40 * 7565827 * 2
def baseEnd_7565827 : Nat := 3884905799764275400767901

theorem tailTrace_7565827 : CollatzResearch.WordTrace tailWord_7565827 prefixEnd_7565827 3884905799764275400767901 := by
  unfold tailWord_7565827
  simp only [CollatzResearch.WordTrace]
  refine ⟨275948380761308394224159735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183965587174205596149439823 275948380761308394224159735)
  ·
    refine ⟨413922571141962591336239603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275948380761308394224159735 413922571141962591336239603)
    ·
      refine ⟨620883856712943887004359405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413922571141962591336239603 620883856712943887004359405)
      ·
        refine ⟨232831446267353957626634777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620883856712943887004359405 232831446267353957626634777)
        ·
          refine ⟨174623584700515468219976083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232831446267353957626634777 174623584700515468219976083)
          ·
            refine ⟨261935377050773202329964125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174623584700515468219976083 261935377050773202329964125)
            ·
              refine ⟨98225766394039950873736547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261935377050773202329964125 98225766394039950873736547)
              ·
                refine ⟨147338649591059926310604821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98225766394039950873736547 147338649591059926310604821)
                ·
                  refine ⟨6906499199580934045809601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147338649591059926310604821 6906499199580934045809601)
                  ·
                    refine ⟨5179874399685700534357201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6906499199580934045809601 5179874399685700534357201)
                    ·
                      refine ⟨3884905799764275400767901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5179874399685700534357201 3884905799764275400767901)
                      ·
                        rfl

theorem cell23_7565827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_7565827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565827 prefixEnd_7565827 := by exact prefixLift 7565827
  have htrace : WordTrace (prefixWord ++ tailWord_7565827) baseStart_7565827 baseEnd_7565827 := by
    simpa [prefixWord, tailWord_7565827, baseEnd_7565827] using wordTrace_append hprefix tailTrace_7565827
  have hstable : (prefixWord ++ tailWord_7565827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565827).length < 2 ^ (prefixWord ++ tailWord_7565827).sum := by decide
  have hdescent : baseEnd_7565827 < baseStart_7565827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7565843 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 7]
def baseStart_7565843 : Nat := 118140960795 + 7565843 * 2 ^ 59
def prefixEnd_7565843 : Nat := 4983230072969 + 3 ^ 40 * 7565843 * 2
def baseEnd_7565843 : Nat := 3884914015454747338167827

theorem tailTrace_7565843 : CollatzResearch.WordTrace tailWord_7565843 prefixEnd_7565843 3884914015454747338167827 := by
  unfold tailWord_7565843
  simp only [CollatzResearch.WordTrace]
  refine ⟨275948964329250428956742183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183965976219500285971161455 275948964329250428956742183)
  ·
    refine ⟨413923446493875643435113275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275948964329250428956742183 413923446493875643435113275)
    ·
      refine ⟨620885169740813465152669913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413923446493875643435113275 620885169740813465152669913)
      ·
        refine ⟨465663877305610098864502435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620885169740813465152669913 465663877305610098864502435)
        ·
          refine ⟨698495815958415148296753653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465663877305610098864502435 698495815958415148296753653)
          ·
            refine ⟨65483982746101420152820655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 698495815958415148296753653 65483982746101420152820655)
            ·
              refine ⟨98225974119152130229230983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65483982746101420152820655 98225974119152130229230983)
              ·
                refine ⟨147338961178728195343846475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98225974119152130229230983 147338961178728195343846475)
                ·
                  refine ⟨221008441768092293015769713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147338961178728195343846475 221008441768092293015769713)
                  ·
                    refine ⟨165756331326069219761827285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221008441768092293015769713 165756331326069219761827285)
                    ·
                      refine ⟨3884914015454747338167827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165756331326069219761827285 3884914015454747338167827)
                      ·
                        rfl

theorem cell23_7565843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_7565843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7565843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7565843 prefixEnd_7565843 := by exact prefixLift 7565843
  have htrace : WordTrace (prefixWord ++ tailWord_7565843) baseStart_7565843 baseEnd_7565843 := by
    simpa [prefixWord, tailWord_7565843, baseEnd_7565843] using wordTrace_append hprefix tailTrace_7565843
  have hstable : (prefixWord ++ tailWord_7565843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7565843).length < 2 ^ (prefixWord ++ tailWord_7565843).sum := by decide
  have hdescent : baseEnd_7565843 < baseStart_7565843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7565843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
