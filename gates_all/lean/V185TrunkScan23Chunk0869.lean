import V185TrunkScan23Chunk0868

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5142774 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_5142774 : Nat := 118140960795 + 5142774 * 2 ^ 59
def prefixEnd_5142774 : Nat := 4983230072969 + 3 ^ 40 * 5142774 * 2
def baseEnd_5142774 : Nat := 880238319815189035591273

theorem tailTrace_5142774 : CollatzResearch.WordTrace tailWord_5142774 prefixEnd_5142774 880238319815189035591273 := by
  unfold tailWord_5142774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11723273591913474294875711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125048251647077059145340917 11723273591913474294875711)
  ·
    refine ⟨17584910387870211442313567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11723273591913474294875711 17584910387870211442313567)
    ·
      refine ⟨26377365581805317163470351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17584910387870211442313567 26377365581805317163470351)
      ·
        refine ⟨39566048372707975745205527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26377365581805317163470351 39566048372707975745205527)
        ·
          refine ⟨59349072559061963617808291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39566048372707975745205527 59349072559061963617808291)
          ·
            refine ⟨89023608838592945426712437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59349072559061963617808291 89023608838592945426712437)
            ·
              refine ⟨8345963328618088633754291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89023608838592945426712437 8345963328618088633754291)
              ·
                refine ⟨12518944992927132950631437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8345963328618088633754291 12518944992927132950631437)
                ·
                  refine ⟨4694604372347674856486789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12518944992927132950631437 4694604372347674856486789)
                  ·
                    refine ⟨880238319815189035591273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694604372347674856486789 880238319815189035591273)
                    ·
                      rfl

theorem cell23_5142774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_5142774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142774 prefixEnd_5142774 := by exact prefixLift 5142774
  have htrace : WordTrace (prefixWord ++ tailWord_5142774) baseStart_5142774 baseEnd_5142774 := by
    simpa [prefixWord, tailWord_5142774, baseEnd_5142774] using wordTrace_append hprefix tailTrace_5142774
  have hstable : (prefixWord ++ tailWord_5142774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142774).length < 2 ^ (prefixWord ++ tailWord_5142774).sum := by decide
  have hdescent : baseEnd_5142774 < baseStart_5142774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142817 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 1, 5]
def baseStart_5142817 : Nat := 118140960795 + 5142817 * 2 ^ 59
def prefixEnd_5142817 : Nat := 4983230072969 + 3 ^ 40 * 5142817 * 2
def baseEnd_5142817 : Nat := 880245679704570146178707

theorem tailTrace_5142817 : CollatzResearch.WordTrace tailWord_5142817 prefixEnd_5142817 880245679704570146178707 := by
  unfold tailWord_5142817
  simp only [CollatzResearch.WordTrace]
  refine ⟨187573945809459807061826705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125049297206306538041217803 187573945809459807061826705)
  ·
    refine ⟨140680459357094855296370029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187573945809459807061826705 140680459357094855296370029)
    ·
      refine ⟨52755172258910570736138761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140680459357094855296370029 52755172258910570736138761)
      ·
        refine ⟨39566379194182928052104071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52755172258910570736138761 39566379194182928052104071)
        ·
          refine ⟨59349568791274392078156107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39566379194182928052104071 59349568791274392078156107)
          ·
            refine ⟨89024353186911588117234161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59349568791274392078156107 89024353186911588117234161)
            ·
              refine ⟨66768264890183691087925621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89024353186911588117234161 66768264890183691087925621)
              ·
                refine ⟨6259524833454721039493027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66768264890183691087925621 6259524833454721039493027)
                ·
                  refine ⟨9389287250182081559239541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6259524833454721039493027 9389287250182081559239541)
                  ·
                    refine ⟨880245679704570146178707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9389287250182081559239541 880245679704570146178707)
                    ·
                      rfl

theorem cell23_5142817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_5142817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142817 prefixEnd_5142817 := by exact prefixLift 5142817
  have htrace : WordTrace (prefixWord ++ tailWord_5142817) baseStart_5142817 baseEnd_5142817 := by
    simpa [prefixWord, tailWord_5142817, baseEnd_5142817] using wordTrace_append hprefix tailTrace_5142817
  have hstable : (prefixWord ++ tailWord_5142817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142817).length < 2 ^ (prefixWord ++ tailWord_5142817).sum := by decide
  have hdescent : baseEnd_5142817 < baseStart_5142817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142837 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_5142837 : Nat := 118140960795 + 5142837 * 2 ^ 59
def prefixEnd_5142837 : Nat := 4983230072969 + 3 ^ 40 * 5142837 * 2
def baseEnd_5142837 : Nat := 2640747308726800360286029

theorem tailTrace_5142837 : CollatzResearch.WordTrace tailWord_5142837 prefixEnd_5142837 2640747308726800360286029 := by
  unfold tailWord_5142837
  simp only [CollatzResearch.WordTrace]
  refine ⟨187574675269387350477554765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125049783512924900318369843 187574675269387350477554765)
  ·
    refine ⟨70340503226020256429083037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187574675269387350477554765 70340503226020256429083037)
    ·
      refine ⟨26377688709757596160906139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70340503226020256429083037 26377688709757596160906139)
      ·
        refine ⟨39566533064636394241359209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26377688709757596160906139 39566533064636394241359209)
        ·
          refine ⟨29674899798477295681019407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39566533064636394241359209 29674899798477295681019407)
          ·
            refine ⟨44512349697715943521529111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29674899798477295681019407 44512349697715943521529111)
            ·
              refine ⟨66768524546573915282293667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44512349697715943521529111 66768524546573915282293667)
              ·
                refine ⟨100152786819860872923440501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66768524546573915282293667 100152786819860872923440501)
                ·
                  refine ⟨9389323764361956836572547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100152786819860872923440501 9389323764361956836572547)
                  ·
                    refine ⟨14083985646542935254858821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9389323764361956836572547 14083985646542935254858821)
                    ·
                      refine ⟨2640747308726800360286029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14083985646542935254858821 2640747308726800360286029)
                      ·
                        rfl

theorem cell23_5142837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_5142837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142837 prefixEnd_5142837 := by exact prefixLift 5142837
  have htrace : WordTrace (prefixWord ++ tailWord_5142837) baseStart_5142837 baseEnd_5142837 := by
    simpa [prefixWord, tailWord_5142837, baseEnd_5142837] using wordTrace_append hprefix tailTrace_5142837
  have hstable : (prefixWord ++ tailWord_5142837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142837).length < 2 ^ (prefixWord ++ tailWord_5142837).sum := by decide
  have hdescent : baseEnd_5142837 < baseStart_5142837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142847 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 1, 6]
def baseStart_5142847 : Nat := 118140960795 + 5142847 * 2 ^ 59
def prefixEnd_5142847 : Nat := 4983230072969 + 3 ^ 40 * 5142847 * 2
def baseEnd_5142847 : Nat := 880250814511115107053661

theorem tailTrace_5142847 : CollatzResearch.WordTrace tailWord_5142847 prefixEnd_5142847 880250814511115107053661 := by
  unfold tailWord_5142847
  simp only [CollatzResearch.WordTrace]
  refine ⟨187575039999351122185418795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125050026666234081456945863 187575039999351122185418795)
  ·
    refine ⟨281362559999026683278128193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187575039999351122185418795 281362559999026683278128193)
    ·
      refine ⟨211021919999270012458596145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281362559999026683278128193 211021919999270012458596145)
      ·
        refine ⟨158266439999452509343947109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211021919999270012458596145 158266439999452509343947109)
        ·
          refine ⟨29674957499897345501990083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158266439999452509343947109 29674957499897345501990083)
          ·
            refine ⟨44512436249846018252985125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29674957499897345501990083 44512436249846018252985125)
            ·
              refine ⟨8346081796846128422434711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44512436249846018252985125 8346081796846128422434711)
              ·
                refine ⟨12519122695269192633652067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8346081796846128422434711 12519122695269192633652067)
                ·
                  refine ⟨18778684042903788950478101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12519122695269192633652067 18778684042903788950478101)
                  ·
                    refine ⟨880250814511115107053661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18778684042903788950478101 880250814511115107053661)
                    ·
                      rfl

theorem cell23_5142847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_5142847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142847 prefixEnd_5142847 := by exact prefixLift 5142847
  have htrace : WordTrace (prefixWord ++ tailWord_5142847) baseStart_5142847 baseEnd_5142847 := by
    simpa [prefixWord, tailWord_5142847, baseEnd_5142847] using wordTrace_append hprefix tailTrace_5142847
  have hstable : (prefixWord ++ tailWord_5142847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142847).length < 2 ^ (prefixWord ++ tailWord_5142847).sum := by decide
  have hdescent : baseEnd_5142847 < baseStart_5142847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142888 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_5142888 : Nat := 118140960795 + 5142888 * 2 ^ 59
def prefixEnd_5142888 : Nat := 4983230072969 + 3 ^ 40 * 5142888 * 2
def baseEnd_5142888 : Nat := 2640773496240179660748295

theorem tailTrace_5142888 : CollatzResearch.WordTrace tailWord_5142888 prefixEnd_5142888 2640773496240179660748295 := by
  unfold tailWord_5142888
  simp only [CollatzResearch.WordTrace]
  refine ⟨93788267696101293093830659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125051023594801724125107545 93788267696101293093830659)
  ·
    refine ⟨140682401544151939640745989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93788267696101293093830659 140682401544151939640745989)
    ·
      refine ⟨26377950289528488682639873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140682401544151939640745989 26377950289528488682639873)
      ·
        refine ⟨19783462717146366511979905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26377950289528488682639873 19783462717146366511979905)
        ·
          refine ⟨14837597037859774883984929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19783462717146366511979905 14837597037859774883984929)
          ·
            refine ⟨11128197778394831162988697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14837597037859774883984929 11128197778394831162988697)
            ·
              refine ⟨8346148333796123372241523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11128197778394831162988697 8346148333796123372241523)
              ·
                refine ⟨12519222500694185058362285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8346148333796123372241523 12519222500694185058362285)
                ·
                  refine ⟨4694708437760319396885857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12519222500694185058362285 4694708437760319396885857)
                  ·
                    refine ⟨3521031328320239547664393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4694708437760319396885857 3521031328320239547664393)
                    ·
                      refine ⟨2640773496240179660748295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3521031328320239547664393 2640773496240179660748295)
                      ·
                        rfl

theorem cell23_5142888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_5142888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142888 prefixEnd_5142888 := by exact prefixLift 5142888
  have htrace : WordTrace (prefixWord ++ tailWord_5142888) baseStart_5142888 baseEnd_5142888 := by
    simpa [prefixWord, tailWord_5142888, baseEnd_5142888] using wordTrace_append hprefix tailTrace_5142888
  have hstable : (prefixWord ++ tailWord_5142888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142888).length < 2 ^ (prefixWord ++ tailWord_5142888).sum := by decide
  have hdescent : baseEnd_5142888 < baseStart_5142888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142901 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_5142901 : Nat := 118140960795 + 5142901 * 2 ^ 59
def prefixEnd_5142901 : Nat := 4983230072969 + 3 ^ 40 * 5142901 * 2
def baseEnd_5142901 : Nat := 2640780171488688109885735

theorem tailTrace_5142901 : CollatzResearch.WordTrace tailWord_5142901 prefixEnd_5142901 2640780171488688109885735 := by
  unfold tailWord_5142901
  simp only [CollatzResearch.WordTrace]
  refine ⟨187577009541155489407884557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125051339694103659605256371 187577009541155489407884557)
  ·
    refine ⟨70341378577933308527956709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187577009541155489407884557 70341378577933308527956709)
    ·
      refine ⟨13189008483362495348991883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70341378577933308527956709 13189008483362495348991883)
      ·
        refine ⟨19783512725043743023487825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13189008483362495348991883 19783512725043743023487825)
        ·
          refine ⟨14837634543782807267615869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19783512725043743023487825 14837634543782807267615869)
          ·
            refine ⟨5564112953918552725355951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14837634543782807267615869 5564112953918552725355951)
            ·
              refine ⟨8346169430877829088033927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5564112953918552725355951 8346169430877829088033927)
              ·
                refine ⟨12519254146316743632050891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8346169430877829088033927 12519254146316743632050891)
                ·
                  refine ⟨18778881219475115448076337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12519254146316743632050891 18778881219475115448076337)
                  ·
                    refine ⟨14084160914606336586057253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18778881219475115448076337 14084160914606336586057253)
                    ·
                      refine ⟨2640780171488688109885735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14084160914606336586057253 2640780171488688109885735)
                      ·
                        rfl

theorem cell23_5142901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_5142901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142901 prefixEnd_5142901 := by exact prefixLift 5142901
  have htrace : WordTrace (prefixWord ++ tailWord_5142901) baseStart_5142901 baseEnd_5142901 := by
    simpa [prefixWord, tailWord_5142901, baseEnd_5142901] using wordTrace_append hprefix tailTrace_5142901
  have hstable : (prefixWord ++ tailWord_5142901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142901).length < 2 ^ (prefixWord ++ tailWord_5142901).sum := by decide
  have hdescent : baseEnd_5142901 < baseStart_5142901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142965 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_5142965 : Nat := 118140960795 + 5142965 * 2 ^ 59
def prefixEnd_5142965 : Nat := 4983230072969 + 3 ^ 40 * 5142965 * 2
def baseEnd_5142965 : Nat := 2640813034250575859485441

theorem tailTrace_5142965 : CollatzResearch.WordTrace tailWord_5142965 prefixEnd_5142965 2640813034250575859485441 := by
  unfold tailWord_5142965
  simp only [CollatzResearch.WordTrace]
  refine ⟨187579343812923628338214349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125052895875282418892142899 187579343812923628338214349)
  ·
    refine ⟨70342253929846360626830381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187579343812923628338214349 70342253929846360626830381)
    ·
      refine ⟨26378345223692385235061393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70342253929846360626830381 26378345223692385235061393)
      ·
        refine ⟨19783758917769288926296045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26378345223692385235061393 19783758917769288926296045)
        ·
          refine ⟨7418909594163483347361017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19783758917769288926296045 7418909594163483347361017)
          ·
            refine ⟨5564182195622612510520763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7418909594163483347361017 5564182195622612510520763)
            ·
              refine ⟨8346273293433918765781145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5564182195622612510520763 8346273293433918765781145)
              ·
                refine ⟨6259704970075439074335859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8346273293433918765781145 6259704970075439074335859)
                ·
                  refine ⟨9389557455113158611503789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6259704970075439074335859 9389557455113158611503789)
                  ·
                    refine ⟨3521084045667434479313921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9389557455113158611503789 3521084045667434479313921)
                    ·
                      refine ⟨2640813034250575859485441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3521084045667434479313921 2640813034250575859485441)
                      ·
                        rfl

theorem cell23_5142965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_5142965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142965 prefixEnd_5142965 := by exact prefixLift 5142965
  have htrace : WordTrace (prefixWord ++ tailWord_5142965) baseStart_5142965 baseEnd_5142965 := by
    simpa [prefixWord, tailWord_5142965, baseEnd_5142965] using wordTrace_append hprefix tailTrace_5142965
  have hstable : (prefixWord ++ tailWord_5142965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142965).length < 2 ^ (prefixWord ++ tailWord_5142965).sum := by decide
  have hdescent : baseEnd_5142965 < baseStart_5142965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143011 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 3]
def baseStart_5143011 : Nat := 118140960795 + 5143011 * 2 ^ 59
def prefixEnd_5143011 : Nat := 4983230072969 + 3 ^ 40 * 5143011 * 2
def baseEnd_5143011 : Nat := 2640836654360682679510229

theorem tailTrace_5143011 : CollatzResearch.WordTrace tailWord_5143011 prefixEnd_5143011 2640836654360682679510229 := by
  unfold tailWord_5143011
  simp only [CollatzResearch.WordTrace]
  refine ⟨187581021570756978194388887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125054014380504652129592591 187581021570756978194388887)
  ·
    refine ⟨281371532356135467291583331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187581021570756978194388887 281371532356135467291583331)
    ·
      refine ⟨422057298534203200937374997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281371532356135467291583331 422057298534203200937374997)
      ·
        refine ⟨19783935868790775043939453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 422057298534203200937374997 19783935868790775043939453)
        ·
          refine ⟨7418975950796540641477295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19783935868790775043939453 7418975950796540641477295)
          ·
            refine ⟨11128463926194810962215943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7418975950796540641477295 11128463926194810962215943)
            ·
              refine ⟨16692695889292216443323915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11128463926194810962215943 16692695889292216443323915)
              ·
                refine ⟨25039043833938324664985873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16692695889292216443323915 25039043833938324664985873)
                ·
                  refine ⟨18779282875453743498739405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25039043833938324664985873 18779282875453743498739405)
                  ·
                    refine ⟨7042231078295153812027277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18779282875453743498739405 7042231078295153812027277)
                    ·
                      refine ⟨2640836654360682679510229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7042231078295153812027277 2640836654360682679510229)
                      ·
                        rfl

theorem cell23_5143011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_5143011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143011 prefixEnd_5143011 := by exact prefixLift 5143011
  have htrace : WordTrace (prefixWord ++ tailWord_5143011) baseStart_5143011 baseEnd_5143011 := by
    simpa [prefixWord, tailWord_5143011, baseEnd_5143011] using wordTrace_append hprefix tailTrace_5143011
  have hstable : (prefixWord ++ tailWord_5143011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143011).length < 2 ^ (prefixWord ++ tailWord_5143011).sum := by decide
  have hdescent : baseEnd_5143011 < baseStart_5143011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143034 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_5143034 : Nat := 118140960795 + 5143034 * 2 ^ 59
def prefixEnd_5143034 : Nat := 4983230072969 + 3 ^ 40 * 5143034 * 2
def baseEnd_5143034 : Nat := 2640848464415736089522623

theorem tailTrace_5143034 : CollatzResearch.WordTrace tailWord_5143034 prefixEnd_5143034 2640848464415736089522623 := by
  unfold tailWord_5143034
  simp only [CollatzResearch.WordTrace]
  refine ⟨46895465112418413280619039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125054573633115768748317437 46895465112418413280619039)
  ·
    refine ⟨70343197668627619920928559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46895465112418413280619039 70343197668627619920928559)
    ·
      refine ⟨105514796502941429881392839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70343197668627619920928559 105514796502941429881392839)
      ·
        refine ⟨158272194754412144822089259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105514796502941429881392839 158272194754412144822089259)
        ·
          refine ⟨237408292131618217233133889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158272194754412144822089259 237408292131618217233133889)
          ·
            refine ⟨178056219098713662924850417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237408292131618217233133889 178056219098713662924850417)
            ·
              refine ⟨133542164324035247193637813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178056219098713662924850417 133542164324035247193637813)
              ·
                refine ⟨12519577905378304424403545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133542164324035247193637813 12519577905378304424403545)
                ·
                  refine ⟨9389683429033728318302659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12519577905378304424403545 9389683429033728318302659)
                  ·
                    refine ⟨14084525143550592477453989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9389683429033728318302659 14084525143550592477453989)
                    ·
                      refine ⟨2640848464415736089522623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14084525143550592477453989 2640848464415736089522623)
                      ·
                        rfl

theorem cell23_5143034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_5143034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143034 prefixEnd_5143034 := by exact prefixLift 5143034
  have htrace : WordTrace (prefixWord ++ tailWord_5143034) baseStart_5143034 baseEnd_5143034 := by
    simpa [prefixWord, tailWord_5143034, baseEnd_5143034] using wordTrace_append hprefix tailTrace_5143034
  have hstable : (prefixWord ++ tailWord_5143034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143034).length < 2 ^ (prefixWord ++ tailWord_5143034).sum := by decide
  have hdescent : baseEnd_5143034 < baseStart_5143034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143046 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_5143046 : Nat := 118140960795 + 5143046 * 2 ^ 59
def prefixEnd_5143046 : Nat := 4983230072969 + 3 ^ 40 * 5143046 * 2
def baseEnd_5143046 : Nat := 2640854626183590042572569

theorem tailTrace_5143046 : CollatzResearch.WordTrace tailWord_5143046 prefixEnd_5143046 2640854626183590042572569 := by
  unfold tailWord_5143046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861946816425943099122281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125054865417086786114608661 5861946816425943099122281)
  ·
    refine ⟨4396460112319457324341711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5861946816425943099122281 4396460112319457324341711)
    ·
      refine ⟨6594690168479185986512567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396460112319457324341711 6594690168479185986512567)
      ·
        refine ⟨9892035252718778979768851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594690168479185986512567 9892035252718778979768851)
        ·
          refine ⟨14838052879078168469653277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9892035252718778979768851 14838052879078168469653277)
          ·
            refine ⟨5564269829654313176119979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14838052879078168469653277 5564269829654313176119979)
            ·
              refine ⟨8346404744481469764179969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5564269829654313176119979 8346404744481469764179969)
              ·
                refine ⟨6259803558361102323134977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8346404744481469764179969 6259803558361102323134977)
                ·
                  refine ⟨4694852668770826742351233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6259803558361102323134977 4694852668770826742351233)
                  ·
                    refine ⟨3521139501578120056763425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4694852668770826742351233 3521139501578120056763425)
                    ·
                      refine ⟨2640854626183590042572569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3521139501578120056763425 2640854626183590042572569)
                      ·
                        rfl

theorem cell23_5143046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_5143046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143046 prefixEnd_5143046 := by exact prefixLift 5143046
  have htrace : WordTrace (prefixWord ++ tailWord_5143046) baseStart_5143046 baseEnd_5143046 := by
    simpa [prefixWord, tailWord_5143046, baseEnd_5143046] using wordTrace_append hprefix tailTrace_5143046
  have hstable : (prefixWord ++ tailWord_5143046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143046).length < 2 ^ (prefixWord ++ tailWord_5143046).sum := by decide
  have hdescent : baseEnd_5143046 < baseStart_5143046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143051 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 2, 4, 2]
def baseStart_5143051 : Nat := 118140960795 + 5143051 * 2 ^ 59
def prefixEnd_5143051 : Nat := 4983230072969 + 3 ^ 40 * 5143051 * 2
def baseEnd_5143051 : Nat := 2640857193586862523010045

theorem tailTrace_5143051 : CollatzResearch.WordTrace tailWord_5143051 prefixEnd_5143051 2640857193586862523010045 := by
  unfold tailWord_5143051
  simp only [CollatzResearch.WordTrace]
  refine ⟨187582480490612065025845007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125054986993741376683896671 187582480490612065025845007)
  ·
    refine ⟨281373720735918097538767511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187582480490612065025845007 281373720735918097538767511)
    ·
      refine ⟨422060581103877146308151267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281373720735918097538767511 422060581103877146308151267)
      ·
        refine ⟨633090871655815719462226901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422060581103877146308151267 633090871655815719462226901)
        ·
          refine ⟨14838067304433180924895943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 633090871655815719462226901 14838067304433180924895943)
          ·
            refine ⟨22257100956649771387343915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14838067304433180924895943 22257100956649771387343915)
            ·
              refine ⟨33385651434974657081015873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22257100956649771387343915 33385651434974657081015873)
              ·
                refine ⟨25039238576230992810761905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33385651434974657081015873 25039238576230992810761905)
                ·
                  refine ⟨18779428932173244608071429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25039238576230992810761905 18779428932173244608071429)
                  ·
                    refine ⟨3521142924782483364013393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18779428932173244608071429 3521142924782483364013393)
                    ·
                      refine ⟨2640857193586862523010045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3521142924782483364013393 2640857193586862523010045)
                      ·
                        rfl

theorem cell23_5143051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 4, 2].length) (baseStart_5143051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143051 prefixEnd_5143051 := by exact prefixLift 5143051
  have htrace : WordTrace (prefixWord ++ tailWord_5143051) baseStart_5143051 baseEnd_5143051 := by
    simpa [prefixWord, tailWord_5143051, baseEnd_5143051] using wordTrace_append hprefix tailTrace_5143051
  have hstable : (prefixWord ++ tailWord_5143051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143051).length < 2 ^ (prefixWord ++ tailWord_5143051).sum := by decide
  have hdescent : baseEnd_5143051 < baseStart_5143051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143061 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_5143061 : Nat := 118140960795 + 5143061 * 2 ^ 59
def prefixEnd_5143061 : Nat := 4983230072969 + 3 ^ 40 * 5143061 * 2
def baseEnd_5143061 : Nat := 880287442797802494628333

theorem tailTrace_5143061 : CollatzResearch.WordTrace tailWord_5143061 prefixEnd_5143061 880287442797802494628333 := by
  unfold tailWord_5143061
  simp only [CollatzResearch.WordTrace]
  refine ⟨187582845220575836733709037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125055230147050557822472691 187582845220575836733709037)
  ·
    refine ⟨70343566957715938775140889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187582845220575836733709037 70343566957715938775140889)
    ·
      refine ⟨52757675218286954081355667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70343566957715938775140889 52757675218286954081355667)
      ·
        refine ⟨79136512827430431122033501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52757675218286954081355667 79136512827430431122033501)
        ·
          refine ⟨29676192310286411670762563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79136512827430431122033501 29676192310286411670762563)
          ·
            refine ⟨44514288465429617506143845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29676192310286411670762563 44514288465429617506143845)
            ·
              refine ⟨8346429087268053282401971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44514288465429617506143845 8346429087268053282401971)
              ·
                refine ⟨12519643630902079923602957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8346429087268053282401971 12519643630902079923602957)
                ·
                  refine ⟨4694866361588279971351109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12519643630902079923602957 4694866361588279971351109)
                  ·
                    refine ⟨880287442797802494628333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694866361588279971351109 880287442797802494628333)
                    ·
                      rfl

theorem cell23_5143061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_5143061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143061 prefixEnd_5143061 := by exact prefixLift 5143061
  have htrace : WordTrace (prefixWord ++ tailWord_5143061) baseStart_5143061 baseEnd_5143061 := by
    simpa [prefixWord, tailWord_5143061, baseEnd_5143061] using wordTrace_append hprefix tailTrace_5143061
  have hstable : (prefixWord ++ tailWord_5143061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143061).length < 2 ^ (prefixWord ++ tailWord_5143061).sum := by decide
  have hdescent : baseEnd_5143061 < baseStart_5143061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143087 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 4, 9]
def baseStart_5143087 : Nat := 118140960795 + 5143087 * 2 ^ 59
def prefixEnd_5143087 : Nat := 4983230072969 + 3 ^ 40 * 5143087 * 2
def baseEnd_5143087 : Nat := 880291892963474794053293

theorem tailTrace_5143087 : CollatzResearch.WordTrace tailWord_5143087 prefixEnd_5143087 880291892963474794053293 := by
  unfold tailWord_5143087
  simp only [CollatzResearch.WordTrace]
  refine ⟨187583793518481643174155515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125055862345654428782770343 187583793518481643174155515)
  ·
    refine ⟨281375690277722464761233273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187583793518481643174155515 281375690277722464761233273)
    ·
      refine ⟨211031767708291848570924955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281375690277722464761233273 211031767708291848570924955)
      ·
        refine ⟨316547651562437772856387433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211031767708291848570924955 316547651562437772856387433)
        ·
          refine ⟨237410738671828329642290575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316547651562437772856387433 237410738671828329642290575)
          ·
            refine ⟨356116108007742494463435863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237410738671828329642290575 356116108007742494463435863)
            ·
              refine ⟨534174162011613741695153795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356116108007742494463435863 534174162011613741695153795)
              ·
                refine ⟨801261243017420612542730693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534174162011613741695153795 801261243017420612542730693)
                ·
                  refine ⟨150236483065766364851762005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801261243017420612542730693 150236483065766364851762005)
                  ·
                    refine ⟨880291892963474794053293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 150236483065766364851762005 880291892963474794053293)
                    ·
                      rfl

theorem cell23_5143087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_5143087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143087 prefixEnd_5143087 := by exact prefixLift 5143087
  have htrace : WordTrace (prefixWord ++ tailWord_5143087) baseStart_5143087 baseEnd_5143087 := by
    simpa [prefixWord, tailWord_5143087, baseEnd_5143087] using wordTrace_append hprefix tailTrace_5143087
  have hstable : (prefixWord ++ tailWord_5143087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143087).length < 2 ^ (prefixWord ++ tailWord_5143087).sum := by decide
  have hdescent : baseEnd_5143087 < baseStart_5143087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143118 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_5143118 : Nat := 118140960795 + 5143118 * 2 ^ 59
def prefixEnd_5143118 : Nat := 4983230072969 + 3 ^ 40 * 5143118 * 2
def baseEnd_5143118 : Nat := 2640891596790713760872237

theorem tailTrace_5143118 : CollatzResearch.WordTrace tailWord_5143118 prefixEnd_5143118 2640891596790713760872237 := by
  unfold tailWord_5143118
  simp only [CollatzResearch.WordTrace]
  refine ⟨23448115522671166933566751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125056616120912890312356005 23448115522671166933566751)
  ·
    refine ⟨35172173284006750400350127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23448115522671166933566751 35172173284006750400350127)
    ·
      refine ⟨52758259926010125600525191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35172173284006750400350127 52758259926010125600525191)
      ·
        refine ⟨79137389889015188400787787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52758259926010125600525191 79137389889015188400787787)
        ·
          refine ⟨118706084833522782601181681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79137389889015188400787787 118706084833522782601181681)
          ·
            refine ⟨89029563625142086950886261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118706084833522782601181681 89029563625142086950886261)
            ·
              refine ⟨8346521589857070651645587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89029563625142086950886261 8346521589857070651645587)
              ·
                refine ⟨12519782384785605977468381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8346521589857070651645587 12519782384785605977468381)
                ·
                  refine ⟨4694918394294602241550643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12519782384785605977468381 4694918394294602241550643)
                  ·
                    refine ⟨7042377591441903362325965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4694918394294602241550643 7042377591441903362325965)
                    ·
                      refine ⟨2640891596790713760872237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7042377591441903362325965 2640891596790713760872237)
                      ·
                        rfl

theorem cell23_5143118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_5143118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143118 prefixEnd_5143118 := by exact prefixLift 5143118
  have htrace : WordTrace (prefixWord ++ tailWord_5143118) baseStart_5143118 baseEnd_5143118 := by
    simpa [prefixWord, tailWord_5143118, baseEnd_5143118] using wordTrace_append hprefix tailTrace_5143118
  have hstable : (prefixWord ++ tailWord_5143118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143118).length < 2 ^ (prefixWord ++ tailWord_5143118).sum := by decide
  have hdescent : baseEnd_5143118 < baseStart_5143118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143161 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 5]
def baseStart_5143161 : Nat := 118140960795 + 5143161 * 2 ^ 59
def prefixEnd_5143161 : Nat := 4983230072969 + 3 ^ 40 * 5143161 * 2
def baseEnd_5143161 : Nat := 2640913676458857092634539

theorem tailTrace_5143161 : CollatzResearch.WordTrace tailWord_5143161 prefixEnd_5143161 2640913676458857092634539 := by
  unfold tailWord_5143161
  simp only [CollatzResearch.WordTrace]
  refine ⟨187586492520213553812349337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125057661680142369208232891 187586492520213553812349337)
  ·
    refine ⟨140689869390160165359262003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187586492520213553812349337 140689869390160165359262003)
    ·
      refine ⟨211034804085240248038893005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140689869390160165359262003 211034804085240248038893005)
      ·
        refine ⟨79138051531965093014584877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211034804085240248038893005 79138051531965093014584877)
        ·
          refine ⟨29676769324486909880469329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79138051531965093014584877 29676769324486909880469329)
          ·
            refine ⟨22257576993365182410351997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29676769324486909880469329 22257576993365182410351997)
            ·
              refine ⟨8346591372511943403881999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22257576993365182410351997 8346591372511943403881999)
              ·
                refine ⟨12519887058767915105822999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8346591372511943403881999 12519887058767915105822999)
                ·
                  refine ⟨18779830588151872658734499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12519887058767915105822999 18779830588151872658734499)
                  ·
                    refine ⟨28169745882227808988101749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18779830588151872658734499 28169745882227808988101749)
                    ·
                      refine ⟨2640913676458857092634539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28169745882227808988101749 2640913676458857092634539)
                      ·
                        rfl

theorem cell23_5143161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_5143161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143161 prefixEnd_5143161 := by exact prefixLift 5143161
  have htrace : WordTrace (prefixWord ++ tailWord_5143161) baseStart_5143161 baseEnd_5143161 := by
    simpa [prefixWord, tailWord_5143161, baseEnd_5143161] using wordTrace_append hprefix tailTrace_5143161
  have hstable : (prefixWord ++ tailWord_5143161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143161).length < 2 ^ (prefixWord ++ tailWord_5143161).sum := by decide
  have hdescent : baseEnd_5143161 < baseStart_5143161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143168 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 2, 4]
def baseStart_5143168 : Nat := 118140960795 + 5143168 * 2 ^ 59
def prefixEnd_5143168 : Nat := 4983230072969 + 3 ^ 40 * 5143168 * 2
def baseEnd_5143168 : Nat := 880305756941146188415669

theorem tailTrace_5143168 : CollatzResearch.WordTrace tailWord_5143168 prefixEnd_5143168 880305756941146188415669 := by
  unfold tailWord_5143168
  simp only [CollatzResearch.WordTrace]
  refine ⟨93793373915594097003927079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125057831887458796005236105 93793373915594097003927079)
  ·
    refine ⟨140690060873391145505890619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93793373915594097003927079 140690060873391145505890619)
    ·
      refine ⟨211035091310086718258835929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140690060873391145505890619 211035091310086718258835929)
      ·
        refine ⟨158276318482565038694126947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211035091310086718258835929 158276318482565038694126947)
        ·
          refine ⟨237414477723847558041190421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158276318482565038694126947 237414477723847558041190421)
          ·
            refine ⟨11128803643305354283180801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 237414477723847558041190421 11128803643305354283180801)
            ·
              refine ⟨8346602732479015712385601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11128803643305354283180801 8346602732479015712385601)
              ·
                refine ⟨6259952049359261784289201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8346602732479015712385601 6259952049359261784289201)
                ·
                  refine ⟨4694964037019446338216901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6259952049359261784289201 4694964037019446338216901)
                  ·
                    refine ⟨880305756941146188415669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694964037019446338216901 880305756941146188415669)
                    ·
                      rfl

theorem cell23_5143168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 4].length) (baseStart_5143168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143168 prefixEnd_5143168 := by exact prefixLift 5143168
  have htrace : WordTrace (prefixWord ++ tailWord_5143168) baseStart_5143168 baseEnd_5143168 := by
    simpa [prefixWord, tailWord_5143168, baseEnd_5143168] using wordTrace_append hprefix tailTrace_5143168
  have hstable : (prefixWord ++ tailWord_5143168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143168).length < 2 ^ (prefixWord ++ tailWord_5143168).sum := by decide
  have hdescent : baseEnd_5143168 < baseStart_5143168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143188 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_5143188 : Nat := 118140960795 + 5143188 * 2 ^ 59
def prefixEnd_5143188 : Nat := 4983230072969 + 3 ^ 40 * 5143188 * 2
def baseEnd_5143188 : Nat := 2640927540436528486996915

theorem tailTrace_5143188 : CollatzResearch.WordTrace tailWord_5143188 prefixEnd_5143188 2640927540436528486996915 := by
  unfold tailWord_5143188
  simp only [CollatzResearch.WordTrace]
  refine ⟨93793738645557868711791109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125058318194077158282388145 93793738645557868711791109)
  ·
    refine ⟨17586325996042100383460833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93793738645557868711791109 17586325996042100383460833)
    ·
      refine ⟨13189744497031575287595625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17586325996042100383460833 13189744497031575287595625)
      ·
        refine ⟨9892308372773681465696719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13189744497031575287595625 9892308372773681465696719)
        ·
          refine ⟨14838462559160522198545079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9892308372773681465696719 14838462559160522198545079)
          ·
            refine ⟨22257693838740783297817619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14838462559160522198545079 22257693838740783297817619)
            ·
              refine ⟨33386540758111174946726429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22257693838740783297817619 33386540758111174946726429)
              ·
                refine ⟨12519952784291690605022411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33386540758111174946726429 12519952784291690605022411)
                ·
                  refine ⟨18779929176437535907533617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12519952784291690605022411 18779929176437535907533617)
                  ·
                    refine ⟨14084946882328151930650213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18779929176437535907533617 14084946882328151930650213)
                    ·
                      refine ⟨2640927540436528486996915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14084946882328151930650213 2640927540436528486996915)
                      ·
                        rfl

theorem cell23_5143188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_5143188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143188 prefixEnd_5143188 := by exact prefixLift 5143188
  have htrace : WordTrace (prefixWord ++ tailWord_5143188) baseStart_5143188 baseEnd_5143188 := by
    simpa [prefixWord, tailWord_5143188, baseEnd_5143188] using wordTrace_append hprefix tailTrace_5143188
  have hstable : (prefixWord ++ tailWord_5143188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143188).length < 2 ^ (prefixWord ++ tailWord_5143188).sum := by decide
  have hdescent : baseEnd_5143188 < baseStart_5143188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143198 : List Nat := [4, 3, 1, 1, 1, 1, 5, 7]
def baseStart_5143198 : Nat := 118140960795 + 5143198 * 2 ^ 59
def prefixEnd_5143198 : Nat := 4983230072969 + 3 ^ 40 * 5143198 * 2
def baseEnd_5143198 : Nat := 97812321305299016587847

theorem tailTrace_5143198 : CollatzResearch.WordTrace tailWord_5143198 prefixEnd_5143198 97812321305299016587847 := by
  unfold tailWord_5143198
  simp only [CollatzResearch.WordTrace]
  refine ⟨23448480252634938641430781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125058561347386339420964165 23448480252634938641430781)
  ·
    refine ⟨8793180094738101990536543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23448480252634938641430781 8793180094738101990536543)
    ·
      refine ⟨13189770142107152985804815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8793180094738101990536543 13189770142107152985804815)
      ·
        refine ⟨19784655213160729478707223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13189770142107152985804815 19784655213160729478707223)
        ·
          refine ⟨29676982819741094218060835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19784655213160729478707223 29676982819741094218060835)
          ·
            refine ⟨44515474229611641327091253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29676982819741094218060835 44515474229611641327091253)
            ·
              refine ⟨4173325709026091374414805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44515474229611641327091253 4173325709026091374414805)
              ·
                refine ⟨97812321305299016587847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4173325709026091374414805 97812321305299016587847)
                ·
                  rfl

theorem cell23_5143198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_5143198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143198 prefixEnd_5143198 := by exact prefixLift 5143198
  have htrace : WordTrace (prefixWord ++ tailWord_5143198) baseStart_5143198 baseEnd_5143198 := by
    simpa [prefixWord, tailWord_5143198, baseEnd_5143198] using wordTrace_append hprefix tailTrace_5143198
  have hstable : (prefixWord ++ tailWord_5143198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143198).length < 2 ^ (prefixWord ++ tailWord_5143198).sum := by decide
  have hdescent : baseEnd_5143198 < baseStart_5143198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143242 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_5143242 : Nat := 118140960795 + 5143242 * 2 ^ 59
def prefixEnd_5143242 : Nat := 4983230072969 + 3 ^ 40 * 5143242 * 2
def baseEnd_5143242 : Nat := 2640955268391871275721667

theorem tailTrace_5143242 : CollatzResearch.WordTrace tailWord_5143242 prefixEnd_5143242 2640955268391871275721667 := by
  unfold tailWord_5143242
  simp only [CollatzResearch.WordTrace]
  refine ⟨46897361708230026161511995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125059631221946736430698653 46897361708230026161511995)
  ·
    refine ⟨70346042562345039242267993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46897361708230026161511995 70346042562345039242267993)
    ·
      refine ⟨52759531921758779431700995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70346042562345039242267993 52759531921758779431700995)
      ·
        refine ⟨79139297882638169147551493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52759531921758779431700995 79139297882638169147551493)
        ·
          refine ⟨14838618352994656715165905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79139297882638169147551493 14838618352994656715165905)
          ·
            refine ⟨11128963764745992536374429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14838618352994656715165905 11128963764745992536374429)
            ·
              refine ⟨4173361411779747201140411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11128963764745992536374429 4173361411779747201140411)
              ·
                refine ⟨6260042117669620801710617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173361411779747201140411 6260042117669620801710617)
                ·
                  refine ⟨4695031588252215601282963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6260042117669620801710617 4695031588252215601282963)
                  ·
                    refine ⟨7042547382378323401924445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4695031588252215601282963 7042547382378323401924445)
                    ·
                      refine ⟨2640955268391871275721667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7042547382378323401924445 2640955268391871275721667)
                      ·
                        rfl

theorem cell23_5143242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_5143242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143242 prefixEnd_5143242 := by exact prefixLift 5143242
  have htrace : WordTrace (prefixWord ++ tailWord_5143242) baseStart_5143242 baseEnd_5143242 := by
    simpa [prefixWord, tailWord_5143242, baseEnd_5143242] using wordTrace_append hprefix tailTrace_5143242
  have hstable : (prefixWord ++ tailWord_5143242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143242).length < 2 ^ (prefixWord ++ tailWord_5143242).sum := by decide
  have hdescent : baseEnd_5143242 < baseStart_5143242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143265 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_5143265 : Nat := 118140960795 + 5143265 * 2 ^ 59
def prefixEnd_5143265 : Nat := 4983230072969 + 3 ^ 40 * 5143265 * 2
def baseEnd_5143265 : Nat := 2640967078446924685734061

theorem tailTrace_5143265 : CollatzResearch.WordTrace tailWord_5143265 prefixEnd_5143265 2640967078446924685734061 := by
  unfold tailWord_5143265
  simp only [CollatzResearch.WordTrace]
  refine ⟨187590285711836779574135249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125060190474557853049423499 187590285711836779574135249)
  ·
    refine ⟨140692714283877584680601437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187590285711836779574135249 140692714283877584680601437)
    ·
      refine ⟨52759767856454094255225539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140692714283877584680601437 52759767856454094255225539)
      ·
        refine ⟨79139651784681141382838309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52759767856454094255225539 79139651784681141382838309)
        ·
          refine ⟨14838684709627714009282183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79139651784681141382838309 14838684709627714009282183)
          ·
            refine ⟨22258027064441571013923275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14838684709627714009282183 22258027064441571013923275)
            ·
              refine ⟨33387040596662356520884913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22258027064441571013923275 33387040596662356520884913)
              ·
                refine ⟨25040280447496767390663685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33387040596662356520884913 25040280447496767390663685)
                ·
                  refine ⟨4695052583905643885749441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25040280447496767390663685 4695052583905643885749441)
                  ·
                    refine ⟨3521289437929232914312081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4695052583905643885749441 3521289437929232914312081)
                    ·
                      refine ⟨2640967078446924685734061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3521289437929232914312081 2640967078446924685734061)
                      ·
                        rfl

theorem cell23_5143265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_5143265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143265 prefixEnd_5143265 := by exact prefixLift 5143265
  have htrace : WordTrace (prefixWord ++ tailWord_5143265) baseStart_5143265 baseEnd_5143265 := by
    simpa [prefixWord, tailWord_5143265, baseEnd_5143265] using wordTrace_append hprefix tailTrace_5143265
  have hstable : (prefixWord ++ tailWord_5143265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143265).length < 2 ^ (prefixWord ++ tailWord_5143265).sum := by decide
  have hdescent : baseEnd_5143265 < baseStart_5143265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143395 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 6]
def baseStart_5143395 : Nat := 118140960795 + 5143395 * 2 ^ 59
def prefixEnd_5143395 : Nat := 4983230072969 + 3 ^ 40 * 5143395 * 2
def baseEnd_5143395 : Nat := 293448203436889908567607

theorem tailTrace_5143395 : CollatzResearch.WordTrace tailWord_5143395 prefixEnd_5143395 293448203436889908567607 := by
  unfold tailWord_5143395
  simp only [CollatzResearch.WordTrace]
  refine ⟨187595027201365811776367639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125063351467577207850911759 187595027201365811776367639)
  ·
    refine ⟨281392540802048717664551459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187595027201365811776367639 281392540802048717664551459)
    ·
      refine ⟨422088811203073076496827189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281392540802048717664551459 422088811203073076496827189)
      ·
        refine ⟨39570826050288100921577549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 422088811203073076496827189 39570826050288100921577549)
        ·
          refine ⟨14839059768858037845591581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39570826050288100921577549 14839059768858037845591581)
          ·
            refine ⟨5564647413321764192096843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14839059768858037845591581 5564647413321764192096843)
            ·
              refine ⟨8346971119982646288145265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5564647413321764192096843 8346971119982646288145265)
              ·
                refine ⟨6260228339986984716108949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8346971119982646288145265 6260228339986984716108949)
                ·
                  refine ⟨293448203436889908567607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6260228339986984716108949 293448203436889908567607)
                  ·
                    rfl

theorem cell23_5143395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 6].length) (baseStart_5143395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143395 prefixEnd_5143395 := by exact prefixLift 5143395
  have htrace : WordTrace (prefixWord ++ tailWord_5143395) baseStart_5143395 baseEnd_5143395 := by
    simpa [prefixWord, tailWord_5143395, baseEnd_5143395] using wordTrace_append hprefix tailTrace_5143395
  have hstable : (prefixWord ++ tailWord_5143395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143395).length < 2 ^ (prefixWord ++ tailWord_5143395).sum := by decide
  have hdescent : baseEnd_5143395 < baseStart_5143395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143445 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_5143445 : Nat := 118140960795 + 5143445 * 2 ^ 59
def prefixEnd_5143445 : Nat := 4983230072969 + 3 ^ 40 * 5143445 * 2
def baseEnd_5143445 : Nat := 2641059504964733981483233

theorem tailTrace_5143445 : CollatzResearch.WordTrace tailWord_5143445 prefixEnd_5143445 2641059504964733981483233 := by
  unfold tailWord_5143445
  simp only [CollatzResearch.WordTrace]
  refine ⟨187596850851184670315687789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125064567234123113543791859 187596850851184670315687789)
  ·
    refine ⟨70348819069194251368382921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187596850851184670315687789 70348819069194251368382921)
    ·
      refine ⟨52761614301895688526287191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70348819069194251368382921 52761614301895688526287191)
      ·
        refine ⟨79142421452843532789430787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52761614301895688526287191 79142421452843532789430787)
        ·
          refine ⟨118713632179265299184146181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79142421452843532789430787 118713632179265299184146181)
          ·
            refine ⟨22258806033612243597027409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118713632179265299184146181 22258806033612243597027409)
            ·
              refine ⟨16694104525209182697770557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22258806033612243597027409 16694104525209182697770557)
              ·
                refine ⟨6260289196953443511663959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16694104525209182697770557 6260289196953443511663959)
                ·
                  refine ⟨9390433795430165267495939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6260289196953443511663959 9390433795430165267495939)
                  ·
                    refine ⟨14085650693145247901243909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9390433795430165267495939 14085650693145247901243909)
                    ·
                      refine ⟨2641059504964733981483233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14085650693145247901243909 2641059504964733981483233)
                      ·
                        rfl

theorem cell23_5143445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_5143445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143445 prefixEnd_5143445 := by exact prefixLift 5143445
  have htrace : WordTrace (prefixWord ++ tailWord_5143445) baseStart_5143445 baseEnd_5143445 := by
    simpa [prefixWord, tailWord_5143445, baseEnd_5143445] using wordTrace_append hprefix tailTrace_5143445
  have hstable : (prefixWord ++ tailWord_5143445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143445).length < 2 ^ (prefixWord ++ tailWord_5143445).sum := by decide
  have hdescent : baseEnd_5143445 < baseStart_5143445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143455 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 4, 4]
def baseStart_5143455 : Nat := 118140960795 + 5143455 * 2 ^ 59
def prefixEnd_5143455 : Nat := 4983230072969 + 3 ^ 40 * 5143455 * 2
def baseEnd_5143455 : Nat := 880354879923759647452729

theorem tailTrace_5143455 : CollatzResearch.WordTrace tailWord_5143455 prefixEnd_5143455 880354879923759647452729 := by
  unfold tailWord_5143455
  simp only [CollatzResearch.WordTrace]
  refine ⟨187597215581148442023551819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125064810387432294682367879 187597215581148442023551819)
  ·
    refine ⟨281395823371722663035327729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187597215581148442023551819 281395823371722663035327729)
    ·
      refine ⟨211046867528791997276495797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281395823371722663035327729 211046867528791997276495797)
      ·
        refine ⟨19785643830824249744671481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211046867528791997276495797 19785643830824249744671481)
        ·
          refine ⟨14839232873118187308503611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19785643830824249744671481 14839232873118187308503611)
          ·
            refine ⟨22258849309677280962755417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14839232873118187308503611 22258849309677280962755417)
            ·
              refine ⟨16694136982257960722066563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22258849309677280962755417 16694136982257960722066563)
              ·
                refine ⟨25041205473386941083099845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16694136982257960722066563 25041205473386941083099845)
                ·
                  refine ⟨4695226026260051453081221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25041205473386941083099845 4695226026260051453081221)
                  ·
                    refine ⟨880354879923759647452729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4695226026260051453081221 880354879923759647452729)
                    ·
                      rfl

theorem cell23_5143455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 4].length) (baseStart_5143455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143455 prefixEnd_5143455 := by exact prefixLift 5143455
  have htrace : WordTrace (prefixWord ++ tailWord_5143455) baseStart_5143455 baseEnd_5143455 := by
    simpa [prefixWord, tailWord_5143455, baseEnd_5143455] using wordTrace_append hprefix tailTrace_5143455
  have hstable : (prefixWord ++ tailWord_5143455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143455).length < 2 ^ (prefixWord ++ tailWord_5143455).sum := by decide
  have hdescent : baseEnd_5143455 < baseStart_5143455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143495 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_5143495 : Nat := 118140960795 + 5143495 * 2 ^ 59
def prefixEnd_5143495 : Nat := 4983230072969 + 3 ^ 40 * 5143495 * 2
def baseEnd_5143495 : Nat := 2641085178997458785858003

theorem tailTrace_5143495 : CollatzResearch.WordTrace tailWord_5143495 prefixEnd_5143495 2641085178997458785858003 := by
  unfold tailWord_5143495
  simp only [CollatzResearch.WordTrace]
  refine ⟨187598674501003528855007939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125065783000669019236671959 187598674501003528855007939)
  ·
    refine ⟨281398011751505293282511909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187598674501003528855007939 281398011751505293282511909)
    ·
      refine ⟨52762127203407242490470983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281398011751505293282511909 52762127203407242490470983)
      ·
        refine ⟨79143190805110863735706475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52762127203407242490470983 79143190805110863735706475)
        ·
          refine ⟨118714786207666295603559713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79143190805110863735706475 118714786207666295603559713)
          ·
            refine ⟨89036089655749721702669785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118714786207666295603559713 89036089655749721702669785)
            ·
              refine ⟨66777067241812291277002339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89036089655749721702669785 66777067241812291277002339)
              ·
                refine ⟨100165600862718436915503509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66777067241812291277002339 100165600862718436915503509)
                ·
                  refine ⟨4695262540439926730414227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100165600862718436915503509 4695262540439926730414227)
                  ·
                    refine ⟨7042893810659890095621341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4695262540439926730414227 7042893810659890095621341)
                    ·
                      refine ⟨2641085178997458785858003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7042893810659890095621341 2641085178997458785858003)
                      ·
                        rfl

theorem cell23_5143495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_5143495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143495 prefixEnd_5143495 := by exact prefixLift 5143495
  have htrace : WordTrace (prefixWord ++ tailWord_5143495) baseStart_5143495 baseEnd_5143495 := by
    simpa [prefixWord, tailWord_5143495, baseEnd_5143495] using wordTrace_append hprefix tailTrace_5143495
  have hstable : (prefixWord ++ tailWord_5143495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143495).length < 2 ^ (prefixWord ++ tailWord_5143495).sum := by decide
  have hdescent : baseEnd_5143495 < baseStart_5143495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143512 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_5143512 : Nat := 118140960795 + 5143512 * 2 ^ 59
def prefixEnd_5143512 : Nat := 4983230072969 + 3 ^ 40 * 5143512 * 2
def baseEnd_5143512 : Nat := 2641093908168585219345425

theorem tailTrace_5143512 : CollatzResearch.WordTrace tailWord_5143512 prefixEnd_5143512 2641093908168585219345425 := by
  unfold tailWord_5143512
  simp only [CollatzResearch.WordTrace]
  refine ⟨93799647270970970379188395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125066196361294627172251193 93799647270970970379188395)
  ·
    refine ⟨140699470906456455568782593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93799647270970970379188395 140699470906456455568782593)
    ·
      refine ⟨105524603179842341676586945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140699470906456455568782593 105524603179842341676586945)
      ·
        refine ⟨79143452384881756257440209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105524603179842341676586945 79143452384881756257440209)
        ·
          refine ⟨59357589288661317193080157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79143452384881756257440209 59357589288661317193080157)
          ·
            refine ⟨22259095983247993947405059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59357589288661317193080157 22259095983247993947405059)
            ·
              refine ⟨33388643974871990921107589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22259095983247993947405059 33388643974871990921107589)
              ·
                refine ⟨6260370745288498297707673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33388643974871990921107589 6260370745288498297707673)
                ·
                  refine ⟨4695278058966373723280755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6260370745288498297707673 4695278058966373723280755)
                  ·
                    refine ⟨7042917088449560584921133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4695278058966373723280755 7042917088449560584921133)
                    ·
                      refine ⟨2641093908168585219345425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7042917088449560584921133 2641093908168585219345425)
                      ·
                        rfl

theorem cell23_5143512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_5143512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143512 prefixEnd_5143512 := by exact prefixLift 5143512
  have htrace : WordTrace (prefixWord ++ tailWord_5143512) baseStart_5143512 baseEnd_5143512 := by
    simpa [prefixWord, tailWord_5143512, baseEnd_5143512] using wordTrace_append hprefix tailTrace_5143512
  have hstable : (prefixWord ++ tailWord_5143512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143512).length < 2 ^ (prefixWord ++ tailWord_5143512).sum := by decide
  have hdescent : baseEnd_5143512 < baseStart_5143512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143513 : List Nat := [1, 2, 1, 2, 5, 3, 2, 2, 1, 2, 2]
def baseStart_5143513 : Nat := 118140960795 + 5143513 * 2 ^ 59
def prefixEnd_5143513 : Nat := 4983230072969 + 3 ^ 40 * 5143513 * 2
def baseEnd_5143513 : Nat := 2641094421649239715432921

theorem tailTrace_5143513 : CollatzResearch.WordTrace tailWord_5143513 prefixEnd_5143513 2641094421649239715432921 := by
  unfold tailWord_5143513
  simp only [CollatzResearch.WordTrace]
  refine ⟨187599331014938317929163193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125066220676625545286108795 187599331014938317929163193)
  ·
    refine ⟨140699498261203738446872395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187599331014938317929163193 140699498261203738446872395)
    ·
      refine ⟨211049247391805607670308593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140699498261203738446872395 211049247391805607670308593)
      ·
        refine ⟨158286935543854205752731445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211049247391805607670308593 158286935543854205752731445)
        ·
          refine ⟨14839400207236331789318573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158286935543854205752731445 14839400207236331789318573)
          ·
            refine ⟨5564775077713624420994465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14839400207236331789318573 5564775077713624420994465)
            ·
              refine ⟨4173581308285218315745849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5564775077713624420994465 4173581308285218315745849)
              ·
                refine ⟨3130185981213913736809387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4173581308285218315745849 3130185981213913736809387)
                ·
                  refine ⟨4695278971820870605214081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130185981213913736809387 4695278971820870605214081)
                  ·
                    refine ⟨3521459228865652953910561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4695278971820870605214081 3521459228865652953910561)
                    ·
                      refine ⟨2641094421649239715432921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3521459228865652953910561 2641094421649239715432921)
                      ·
                        rfl

theorem cell23_5143513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_5143513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143513 prefixEnd_5143513 := by exact prefixLift 5143513
  have htrace : WordTrace (prefixWord ++ tailWord_5143513) baseStart_5143513 baseEnd_5143513 := by
    simpa [prefixWord, tailWord_5143513, baseEnd_5143513] using wordTrace_append hprefix tailTrace_5143513
  have hstable : (prefixWord ++ tailWord_5143513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143513).length < 2 ^ (prefixWord ++ tailWord_5143513).sum := by decide
  have hdescent : baseEnd_5143513 < baseStart_5143513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143528 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 1, 8]
def baseStart_5143528 : Nat := 118140960795 + 5143528 * 2 ^ 59
def prefixEnd_5143528 : Nat := 4983230072969 + 3 ^ 40 * 5143528 * 2
def baseEnd_5143528 : Nat := 880367374619685718915117

theorem tailTrace_5143528 : CollatzResearch.WordTrace tailWord_5143528 prefixEnd_5143528 880367374619685718915117 := by
  unfold tailWord_5143528
  simp only [CollatzResearch.WordTrace]
  refine ⟨93799939054941987745479619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125066585406589316993972825 93799939054941987745479619)
  ·
    refine ⟨140699908582412981618219429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93799939054941987745479619 140699908582412981618219429)
    ·
      refine ⟨26381232859202434053416143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140699908582412981618219429 26381232859202434053416143)
      ·
        refine ⟨39571849288803651080124215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26381232859202434053416143 39571849288803651080124215)
        ·
          refine ⟨59357773933205476620186323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39571849288803651080124215 59357773933205476620186323)
          ·
            refine ⟨89036660899808214930279485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59357773933205476620186323 89036660899808214930279485)
            ·
              refine ⟨33388747837428080598854807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89036660899808214930279485 33388747837428080598854807)
              ·
                refine ⟨50083121756142120898282211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33388747837428080598854807 50083121756142120898282211)
                ·
                  refine ⟨75124682634213181347423317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50083121756142120898282211 75124682634213181347423317)
                  ·
                    refine ⟨880367374619685718915117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75124682634213181347423317 880367374619685718915117)
                    ·
                      rfl

theorem cell23_5143528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_5143528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143528 prefixEnd_5143528 := by exact prefixLift 5143528
  have htrace : WordTrace (prefixWord ++ tailWord_5143528) baseStart_5143528 baseEnd_5143528 := by
    simpa [prefixWord, tailWord_5143528, baseEnd_5143528] using wordTrace_append hprefix tailTrace_5143528
  have hstable : (prefixWord ++ tailWord_5143528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143528).length < 2 ^ (prefixWord ++ tailWord_5143528).sum := by decide
  have hdescent : baseEnd_5143528 < baseStart_5143528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143575 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 7]
def baseStart_5143575 : Nat := 118140960795 + 5143575 * 2 ^ 59
def prefixEnd_5143575 : Nat := 4983230072969 + 3 ^ 40 * 5143575 * 2
def baseEnd_5143575 : Nat := 293458473049979830317515

theorem tailTrace_5143575 : CollatzResearch.WordTrace tailWord_5143575 prefixEnd_5143575 293458473049979830317515 := by
  unfold tailWord_5143575
  simp only [CollatzResearch.WordTrace]
  refine ⟨187601592340713702517920179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125067728227142468345280119 187601592340713702517920179)
  ·
    refine ⟨281402388511070553776880269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187601592340713702517920179 281402388511070553776880269)
    ·
      refine ⟨105525895691651457666330101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281402388511070553776880269 105525895691651457666330101)
      ·
        refine ⟨9893052721092324156218447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105525895691651457666330101 9893052721092324156218447)
        ·
          refine ⟨14839579081638486234327671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9893052721092324156218447 14839579081638486234327671)
          ·
            refine ⟨22259368622457729351491507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14839579081638486234327671 22259368622457729351491507)
            ·
              refine ⟨33389052933686594027237261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22259368622457729351491507 33389052933686594027237261)
              ·
                refine ⟨12520894850132472760213973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33389052933686594027237261 12520894850132472760213973)
                ·
                  refine ⟨293458473049979830317515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12520894850132472760213973 293458473049979830317515)
                  ·
                    rfl

theorem cell23_5143575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 7].length) (baseStart_5143575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143575 prefixEnd_5143575 := by exact prefixLift 5143575
  have htrace : WordTrace (prefixWord ++ tailWord_5143575) baseStart_5143575 baseEnd_5143575 := by
    simpa [prefixWord, tailWord_5143575, baseEnd_5143575] using wordTrace_append hprefix tailTrace_5143575
  have hstable : (prefixWord ++ tailWord_5143575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143575).length < 2 ^ (prefixWord ++ tailWord_5143575).sum := by decide
  have hdescent : baseEnd_5143575 < baseStart_5143575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143605 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_5143605 : Nat := 118140960795 + 5143605 * 2 ^ 59
def prefixEnd_5143605 : Nat := 4983230072969 + 3 ^ 40 * 5143605 * 2
def baseEnd_5143605 : Nat := 880380553956484451827499

theorem tailTrace_5143605 : CollatzResearch.WordTrace tailWord_5143605 prefixEnd_5143605 880380553956484451827499 := by
  unfold tailWord_5143605
  simp only [CollatzResearch.WordTrace]
  refine ⟨187602686530605017641512269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125068457687070011761008179 187602686530605017641512269)
  ·
    refine ⟨70351007448976881615567101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187602686530605017641512269 70351007448976881615567101)
    ·
      refine ⟨26381627793366330605837663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70351007448976881615567101 26381627793366330605837663)
      ·
        refine ⟨39572441690049495908756495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26381627793366330605837663 39572441690049495908756495)
        ·
          refine ⟨59358662535074243863134743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39572441690049495908756495 59358662535074243863134743)
          ·
            refine ⟨89037993802611365794702115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59358662535074243863134743 89037993802611365794702115)
            ·
              refine ⟨133556990703917048692053173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89037993802611365794702115 133556990703917048692053173)
              ·
                refine ⟨12520967878492223314879985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133556990703917048692053173 12520967878492223314879985)
                ·
                  refine ⟨9390725908869167486159989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12520967878492223314879985 9390725908869167486159989)
                  ·
                    refine ⟨880380553956484451827499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9390725908869167486159989 880380553956484451827499)
                    ·
                      rfl

theorem cell23_5143605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_5143605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143605 prefixEnd_5143605 := by exact prefixLift 5143605
  have htrace : WordTrace (prefixWord ++ tailWord_5143605) baseStart_5143605 baseEnd_5143605 := by
    simpa [prefixWord, tailWord_5143605, baseEnd_5143605] using wordTrace_append hprefix tailTrace_5143605
  have hstable : (prefixWord ++ tailWord_5143605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143605).length < 2 ^ (prefixWord ++ tailWord_5143605).sum := by decide
  have hdescent : baseEnd_5143605 < baseStart_5143605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143609 : List Nat := [1, 2, 1, 5, 2, 3, 1, 3, 5]
def baseStart_5143609 : Nat := 118140960795 + 5143609 * 2 ^ 59
def prefixEnd_5143609 : Nat := 4983230072969 + 3 ^ 40 * 5143609 * 2
def baseEnd_5143609 : Nat := 293460412865785704425831

theorem tailTrace_5143609 : CollatzResearch.WordTrace tailWord_5143609 prefixEnd_5143609 293460412865785704425831 := by
  unfold tailWord_5143609
  simp only [CollatzResearch.WordTrace]
  refine ⟨187602832422590526324657881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125068554948393684216438587 187602832422590526324657881)
  ·
    refine ⟨140702124316942894743493411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187602832422590526324657881 140702124316942894743493411)
    ·
      refine ⟨211053186475414342115240117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140702124316942894743493411 211053186475414342115240117)
      ·
        refine ⟨19786236232070094573303761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211053186475414342115240117 19786236232070094573303761)
        ·
          refine ⟨14839677174052570929977821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19786236232070094573303761 14839677174052570929977821)
          ·
            refine ⟨5564878940269714098741683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14839677174052570929977821 5564878940269714098741683)
            ·
              refine ⟨8347318410404571148112525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5564878940269714098741683 8347318410404571148112525)
              ·
                refine ⟨3130244403901714180542197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8347318410404571148112525 3130244403901714180542197)
                ·
                  refine ⟨293460412865785704425831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3130244403901714180542197 293460412865785704425831)
                  ·
                    rfl

theorem cell23_5143609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 5].length) (baseStart_5143609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143609 prefixEnd_5143609 := by exact prefixLift 5143609
  have htrace : WordTrace (prefixWord ++ tailWord_5143609) baseStart_5143609 baseEnd_5143609 := by
    simpa [prefixWord, tailWord_5143609, baseEnd_5143609] using wordTrace_append hprefix tailTrace_5143609
  have hstable : (prefixWord ++ tailWord_5143609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143609).length < 2 ^ (prefixWord ++ tailWord_5143609).sum := by decide
  have hdescent : baseEnd_5143609 < baseStart_5143609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143692 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_5143692 : Nat := 118140960795 + 5143692 * 2 ^ 59
def prefixEnd_5143692 : Nat := 4983230072969 + 3 ^ 40 * 5143692 * 2
def baseEnd_5143692 : Nat := 2641186334686394515094597

theorem tailTrace_5143692 : CollatzResearch.WordTrace tailWord_5143692 prefixEnd_5143692 2641186334686394515094597 := by
  unfold tailWord_5143692
  simp only [CollatzResearch.WordTrace]
  refine ⟨93802929840644915749964665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125070573120859887666619553 93802929840644915749964665)
  ·
    refine ⟨70352197380483686812473499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93802929840644915749964665 70352197380483686812473499)
    ·
      refine ⟨105528296070725530218710249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70352197380483686812473499 105528296070725530218710249)
      ·
        refine ⟨79146222053044147664032687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105528296070725530218710249 79146222053044147664032687)
        ·
          refine ⟨118719333079566221496049031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79146222053044147664032687 118719333079566221496049031)
          ·
            refine ⟨178078999619349332244073547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118719333079566221496049031 178078999619349332244073547)
            ·
              refine ⟨267118499429023998366110321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178078999619349332244073547 267118499429023998366110321)
              ·
                refine ⟨200338874571767998774582741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267118499429023998366110321 200338874571767998774582741)
                ·
                  refine ⟨4695442372775812471279283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 200338874571767998774582741 4695442372775812471279283)
                  ·
                    refine ⟨7043163559163718706918925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4695442372775812471279283 7043163559163718706918925)
                    ·
                      refine ⟨2641186334686394515094597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7043163559163718706918925 2641186334686394515094597)
                      ·
                        rfl

theorem cell23_5143692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_5143692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143692 prefixEnd_5143692 := by exact prefixLift 5143692
  have htrace : WordTrace (prefixWord ++ tailWord_5143692) baseStart_5143692 baseEnd_5143692 := by
    simpa [prefixWord, tailWord_5143692, baseEnd_5143692] using wordTrace_append hprefix tailTrace_5143692
  have hstable : (prefixWord ++ tailWord_5143692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143692).length < 2 ^ (prefixWord ++ tailWord_5143692).sum := by decide
  have hdescent : baseEnd_5143692 < baseStart_5143692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143709 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_5143709 : Nat := 118140960795 + 5143709 * 2 ^ 59
def prefixEnd_5143709 : Nat := 4983230072969 + 3 ^ 40 * 5143709 * 2
def baseEnd_5143709 : Nat := 2641195063857520948582019

theorem tailTrace_5143709 : CollatzResearch.WordTrace tailWord_5143709 prefixEnd_5143709 2641195063857520948582019 := by
  unfold tailWord_5143709
  simp only [CollatzResearch.WordTrace]
  refine ⟨187606479722228243403298181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125070986481485495602198787 187606479722228243403298181)
  ·
    refine ⟨35176214947917795638118409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187606479722228243403298181 35176214947917795638118409)
    ·
      refine ⟨26382161210938346728588807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35176214947917795638118409 26382161210938346728588807)
      ·
        refine ⟨39573241816407520092883211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26382161210938346728588807 39573241816407520092883211)
        ·
          refine ⟨59359862724611280139324817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39573241816407520092883211 59359862724611280139324817)
          ·
            refine ⟨44519897043458460104493613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59359862724611280139324817 44519897043458460104493613)
            ·
              refine ⟨16694961391296922539185105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44519897043458460104493613 16694961391296922539185105)
              ·
                refine ⟨12521221043472691904388829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16694961391296922539185105 12521221043472691904388829)
                ·
                  refine ⟨4695457891302259464145811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12521221043472691904388829 4695457891302259464145811)
                  ·
                    refine ⟨7043186836953389196218717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4695457891302259464145811 7043186836953389196218717)
                    ·
                      refine ⟨2641195063857520948582019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7043186836953389196218717 2641195063857520948582019)
                      ·
                        rfl

theorem cell23_5143709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_5143709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143709 prefixEnd_5143709 := by exact prefixLift 5143709
  have htrace : WordTrace (prefixWord ++ tailWord_5143709) baseStart_5143709 baseEnd_5143709 := by
    simpa [prefixWord, tailWord_5143709, baseEnd_5143709] using wordTrace_append hprefix tailTrace_5143709
  have hstable : (prefixWord ++ tailWord_5143709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143709).length < 2 ^ (prefixWord ++ tailWord_5143709).sum := by decide
  have hdescent : baseEnd_5143709 < baseStart_5143709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143712 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 1, 5]
def baseStart_5143712 : Nat := 118140960795 + 5143712 * 2 ^ 59
def prefixEnd_5143712 : Nat := 4983230072969 + 3 ^ 40 * 5143712 * 2
def baseEnd_5143712 : Nat := 880398868099828145614835

theorem tailTrace_5143712 : CollatzResearch.WordTrace tailWord_5143712 prefixEnd_5143712 880398868099828145614835 := by
  unfold tailWord_5143712
  simp only [CollatzResearch.WordTrace]
  refine ⟨93803294570608687457828695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125071059427478249943771593 93803294570608687457828695)
  ·
    refine ⟨140704941855913031186743043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93803294570608687457828695 140704941855913031186743043)
    ·
      refine ⟨211057412783869546780114565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140704941855913031186743043 211057412783869546780114565)
      ·
        refine ⟨39573264896975540021271481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211057412783869546780114565 39573264896975540021271481)
        ·
          refine ⟨29679948672731655015953611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39573264896975540021271481 29679948672731655015953611)
          ·
            refine ⟨44519923009097482523930417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29679948672731655015953611 44519923009097482523930417)
            ·
              refine ⟨33389942256823111892947813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44519923009097482523930417 33389942256823111892947813)
              ·
                refine ⟨6260614173154333479927715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33389942256823111892947813 6260614173154333479927715)
                ·
                  refine ⟨9390921259731500219891573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6260614173154333479927715 9390921259731500219891573)
                  ·
                    refine ⟨880398868099828145614835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9390921259731500219891573 880398868099828145614835)
                    ·
                      rfl

theorem cell23_5143712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_5143712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143712 prefixEnd_5143712 := by exact prefixLift 5143712
  have htrace : WordTrace (prefixWord ++ tailWord_5143712) baseStart_5143712 baseEnd_5143712 := by
    simpa [prefixWord, tailWord_5143712, baseEnd_5143712] using wordTrace_append hprefix tailTrace_5143712
  have hstable : (prefixWord ++ tailWord_5143712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143712).length < 2 ^ (prefixWord ++ tailWord_5143712).sum := by decide
  have hdescent : baseEnd_5143712 < baseStart_5143712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143729 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 1, 5]
def baseStart_5143729 : Nat := 118140960795 + 5143729 * 2 ^ 59
def prefixEnd_5143729 : Nat := 4983230072969 + 3 ^ 40 * 5143729 * 2
def baseEnd_5143729 : Nat := 880401777823536956777309

theorem tailTrace_5143729 : CollatzResearch.WordTrace tailWord_5143729 prefixEnd_5143729 880401777823536956777309 := by
  unfold tailWord_5143729
  simp only [CollatzResearch.WordTrace]
  refine ⟨187607209182155786819026241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125071472788103857879350827 187607209182155786819026241)
  ·
    refine ⟨140705406886616840114269681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187607209182155786819026241 140705406886616840114269681)
    ·
      refine ⟨105529055164962630085702261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140705406886616840114269681 105529055164962630085702261)
      ·
        refine ⟨9893348921715246570534587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105529055164962630085702261 9893348921715246570534587)
        ·
          refine ⟨14840023382572869855801881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9893348921715246570534587 14840023382572869855801881)
          ·
            refine ⟨11130017536929652391851411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14840023382572869855801881 11130017536929652391851411)
            ·
              refine ⟨16695026305394478587777117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11130017536929652391851411 16695026305394478587777117)
              ·
                refine ⟨6260634864522929470416419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16695026305394478587777117 6260634864522929470416419)
                ·
                  refine ⟨9390952296784394205624629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6260634864522929470416419 9390952296784394205624629)
                  ·
                    refine ⟨880401777823536956777309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9390952296784394205624629 880401777823536956777309)
                    ·
                      rfl

theorem cell23_5143729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_5143729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143729 prefixEnd_5143729 := by exact prefixLift 5143729
  have htrace : WordTrace (prefixWord ++ tailWord_5143729) baseStart_5143729 baseEnd_5143729 := by
    simpa [prefixWord, tailWord_5143729, baseEnd_5143729] using wordTrace_append hprefix tailTrace_5143729
  have hstable : (prefixWord ++ tailWord_5143729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143729).length < 2 ^ (prefixWord ++ tailWord_5143729).sum := by decide
  have hdescent : baseEnd_5143729 < baseStart_5143729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143750 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_5143750 : Nat := 118140960795 + 5143750 * 2 ^ 59
def prefixEnd_5143750 : Nat := 4983230072969 + 3 ^ 40 * 5143750 * 2
def baseEnd_5143750 : Nat := 293468457396039476463259

theorem tailTrace_5143750 : CollatzResearch.WordTrace tailWord_5143750 prefixEnd_5143750 293468457396039476463259 := by
  unfold tailWord_5143750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862749222346240856423147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125071983410053138270360469 5862749222346240856423147)
  ·
    refine ⟨8794123833519361284634721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5862749222346240856423147 8794123833519361284634721)
    ·
      refine ⟨6595592875139520963476041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8794123833519361284634721 6595592875139520963476041)
      ·
        refine ⟨4946694656354640722607031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6595592875139520963476041 4946694656354640722607031)
        ·
          refine ⟨7420041984531961083910547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946694656354640722607031 7420041984531961083910547)
          ·
            refine ⟨11130062976797941625865821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420041984531961083910547 11130062976797941625865821)
            ·
              refine ⟨4173773616299228109699683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11130062976797941625865821 4173773616299228109699683)
              ·
                refine ⟨6260660424448842164549525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173773616299228109699683 6260660424448842164549525)
                ·
                  refine ⟨293468457396039476463259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6260660424448842164549525 293468457396039476463259)
                  ·
                    rfl

theorem cell23_5143750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_5143750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143750 prefixEnd_5143750 := by exact prefixLift 5143750
  have htrace : WordTrace (prefixWord ++ tailWord_5143750) baseStart_5143750 baseEnd_5143750 := by
    simpa [prefixWord, tailWord_5143750, baseEnd_5143750] using wordTrace_append hprefix tailTrace_5143750
  have hstable : (prefixWord ++ tailWord_5143750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143750).length < 2 ^ (prefixWord ++ tailWord_5143750).sum := by decide
  have hdescent : baseEnd_5143750 < baseStart_5143750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143752 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_5143752 : Nat := 118140960795 + 5143752 * 2 ^ 59
def prefixEnd_5143752 : Nat := 4983230072969 + 3 ^ 40 * 5143752 * 2
def baseEnd_5143752 : Nat := 2641217143525664280344321

theorem tailTrace_5143752 : CollatzResearch.WordTrace tailWord_5143752 prefixEnd_5143752 2641217143525664280344321 := by
  unfold tailWord_5143752
  simp only [CollatzResearch.WordTrace]
  refine ⟨93804024030536230873556755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125072032040714974498075673 93804024030536230873556755)
  ·
    refine ⟨140706036045804346310335133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93804024030536230873556755 140706036045804346310335133)
    ·
      refine ⟨52764763517176629866375675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140706036045804346310335133 52764763517176629866375675)
      ·
        refine ⟨79147145275764944799563513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52764763517176629866375675 79147145275764944799563513)
        ·
          refine ⟨59360358956823708599672635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79147145275764944799563513 59360358956823708599672635)
          ·
            refine ⟨89040538435235562899508953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59360358956823708599672635 89040538435235562899508953)
            ·
              refine ⟨66780403826426672174631715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89040538435235562899508953 66780403826426672174631715)
              ·
                refine ⟨100170605739640008261947573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66780403826426672174631715 100170605739640008261947573)
                ·
                  refine ⟨9390994288091250774557585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100170605739640008261947573 9390994288091250774557585)
                  ·
                    refine ⟨7043245716068438080918189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9390994288091250774557585 7043245716068438080918189)
                    ·
                      refine ⟨2641217143525664280344321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7043245716068438080918189 2641217143525664280344321)
                      ·
                        rfl

theorem cell23_5143752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_5143752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143752 prefixEnd_5143752 := by exact prefixLift 5143752
  have htrace : WordTrace (prefixWord ++ tailWord_5143752) baseStart_5143752 baseEnd_5143752 := by
    simpa [prefixWord, tailWord_5143752, baseEnd_5143752] using wordTrace_append hprefix tailTrace_5143752
  have hstable : (prefixWord ++ tailWord_5143752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143752).length < 2 ^ (prefixWord ++ tailWord_5143752).sum := by decide
  have hdescent : baseEnd_5143752 < baseStart_5143752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143762 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_5143762 : Nat := 118140960795 + 5143762 * 2 ^ 59
def prefixEnd_5143762 : Nat := 4983230072969 + 3 ^ 40 * 5143762 * 2
def baseEnd_5143762 : Nat := 2641222278332209241219275

theorem tailTrace_5143762 : CollatzResearch.WordTrace tailWord_5143762 prefixEnd_5143762 2641222278332209241219275 := by
  unfold tailWord_5143762
  simp only [CollatzResearch.WordTrace]
  refine ⟨46902103197759058363744385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125072275194024155636651693 46902103197759058363744385)
  ·
    refine ⟨35176577398319293772808289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46902103197759058363744385 35176577398319293772808289)
    ·
      refine ⟨26382433048739470329606217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35176577398319293772808289 26382433048739470329606217)
      ·
        refine ⟨19786824786554602747204663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26382433048739470329606217 19786824786554602747204663)
        ·
          refine ⟨29680237179831904120806995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19786824786554602747204663 29680237179831904120806995)
          ·
            refine ⟨44520355769747856181210493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29680237179831904120806995 44520355769747856181210493)
            ·
              refine ⟨16695133413655446067953935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44520355769747856181210493 16695133413655446067953935)
              ·
                refine ⟨25042700120483169101930903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16695133413655446067953935 25042700120483169101930903)
                ·
                  refine ⟨37564050180724753652896355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25042700120483169101930903 37564050180724753652896355)
                  ·
                    refine ⟨56346075271087130479344533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37564050180724753652896355 56346075271087130479344533)
                    ·
                      refine ⟨2641222278332209241219275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56346075271087130479344533 2641222278332209241219275)
                      ·
                        rfl

theorem cell23_5143762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_5143762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143762 prefixEnd_5143762 := by exact prefixLift 5143762
  have htrace : WordTrace (prefixWord ++ tailWord_5143762) baseStart_5143762 baseEnd_5143762 := by
    simpa [prefixWord, tailWord_5143762, baseEnd_5143762] using wordTrace_append hprefix tailTrace_5143762
  have hstable : (prefixWord ++ tailWord_5143762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143762).length < 2 ^ (prefixWord ++ tailWord_5143762).sum := by decide
  have hdescent : baseEnd_5143762 < baseStart_5143762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143810 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5143810 : Nat := 118140960795 + 5143810 * 2 ^ 59
def prefixEnd_5143810 : Nat := 4983230072969 + 3 ^ 40 * 5143810 * 2
def baseEnd_5143810 : Nat := 880415641801208351139685

theorem tailTrace_5143810 : CollatzResearch.WordTrace tailWord_5143810 prefixEnd_5143810 880415641801208351139685 := by
  unfold tailWord_5143810
  simp only [CollatzResearch.WordTrace]
  refine ⟨46902540873715584413181221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125073442329908225101816589 46902540873715584413181221)
  ·
    refine ⟨8794226413821672077471479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46902540873715584413181221 8794226413821672077471479)
    ·
      refine ⟨13191339620732508116207219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8794226413821672077471479 13191339620732508116207219)
      ·
        refine ⟨19787009431098762174310829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13191339620732508116207219 19787009431098762174310829)
        ·
          refine ⟨7420128536662035815366561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19787009431098762174310829 7420128536662035815366561)
          ·
            refine ⟨5565096402496526861524921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7420128536662035815366561 5565096402496526861524921)
            ·
              refine ⟨4173822301872395146143691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5565096402496526861524921 4173822301872395146143691)
              ·
                refine ⟨6260733452808592719215537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173822301872395146143691 6260733452808592719215537)
                ·
                  refine ⟨4695550089606444539411653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6260733452808592719215537 4695550089606444539411653)
                  ·
                    refine ⟨880415641801208351139685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4695550089606444539411653 880415641801208351139685)
                    ·
                      rfl

theorem cell23_5143810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5143810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143810 prefixEnd_5143810 := by exact prefixLift 5143810
  have htrace : WordTrace (prefixWord ++ tailWord_5143810) baseStart_5143810 baseEnd_5143810 := by
    simpa [prefixWord, tailWord_5143810, baseEnd_5143810] using wordTrace_append hprefix tailTrace_5143810
  have hstable : (prefixWord ++ tailWord_5143810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143810).length < 2 ^ (prefixWord ++ tailWord_5143810).sum := by decide
  have hdescent : baseEnd_5143810 < baseStart_5143810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143843 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 1, 3, 2]
def baseStart_5143843 : Nat := 118140960795 + 5143843 * 2 ^ 59
def prefixEnd_5143843 : Nat := 4983230072969 + 3 ^ 40 * 5143843 * 2
def baseEnd_5143843 : Nat := 2641263870265223424306403

theorem tailTrace_5143843 : CollatzResearch.WordTrace tailWord_5143843 prefixEnd_5143843 2641263870265223424306403 := by
  unfold tailWord_5143843
  simp only [CollatzResearch.WordTrace]
  refine ⟨187611367103742784288676183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125074244735828522859117455 187611367103742784288676183)
  ·
    refine ⟨281417050655614176433014275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187611367103742784288676183 281417050655614176433014275)
    ·
      refine ⟨422125575983421264649521413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281417050655614176433014275 422125575983421264649521413)
      ·
        refine ⟨79148545496891487121785265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 422125575983421264649521413 79148545496891487121785265)
        ·
          refine ⟨59361409122668615341338949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79148545496891487121785265 59361409122668615341338949)
          ·
            refine ⟨11130264210500365376501053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59361409122668615341338949 11130264210500365376501053)
            ·
              refine ⟨4173849078937637016187895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11130264210500365376501053 4173849078937637016187895)
              ·
                refine ⟨6260773618406455524281843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173849078937637016187895 6260773618406455524281843)
                ·
                  refine ⟨9391160427609683286422765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6260773618406455524281843 9391160427609683286422765)
                  ·
                    refine ⟨3521685160353631232408537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9391160427609683286422765 3521685160353631232408537)
                    ·
                      refine ⟨2641263870265223424306403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3521685160353631232408537 2641263870265223424306403)
                      ·
                        rfl

theorem cell23_5143843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_5143843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143843 prefixEnd_5143843 := by exact prefixLift 5143843
  have htrace : WordTrace (prefixWord ++ tailWord_5143843) baseStart_5143843 baseEnd_5143843 := by
    simpa [prefixWord, tailWord_5143843, baseEnd_5143843] using wordTrace_append hprefix tailTrace_5143843
  have hstable : (prefixWord ++ tailWord_5143843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143843).length < 2 ^ (prefixWord ++ tailWord_5143843).sum := by decide
  have hdescent : baseEnd_5143843 < baseStart_5143843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143852 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_5143852 : Nat := 118140960795 + 5143852 * 2 ^ 59
def prefixEnd_5143852 : Nat := 4983230072969 + 3 ^ 40 * 5143852 * 2
def baseEnd_5143852 : Nat := 2641268491591113889093861

theorem tailTrace_5143852 : CollatzResearch.WordTrace tailWord_5143852 prefixEnd_5143852 2641268491591113889093861 := by
  unfold tailWord_5143852
  simp only [CollatzResearch.WordTrace]
  refine ⟨93805847680355089412876905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125074463573806785883835873 93805847680355089412876905)
  ·
    refine ⟨70354385760266317059657679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93805847680355089412876905 70354385760266317059657679)
    ·
      refine ⟨105531578640399475589486519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70354385760266317059657679 105531578640399475589486519)
      ·
        refine ⟨158297367960599213384229779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105531578640399475589486519 158297367960599213384229779)
        ·
          refine ⟨237446051940898820076344669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158297367960599213384229779 237446051940898820076344669)
          ·
            refine ⟨89042269477837057528629251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237446051940898820076344669 89042269477837057528629251)
            ·
              refine ⟨133563404216755586292943877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89042269477837057528629251 133563404216755586292943877)
              ·
                refine ⟨25043138290641672429926977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133563404216755586292943877 25043138290641672429926977)
                ·
                  refine ⟨18782353717981254322445233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25043138290641672429926977 18782353717981254322445233)
                  ·
                    refine ⟨14086765288485940741833925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18782353717981254322445233 14086765288485940741833925)
                    ·
                      refine ⟨2641268491591113889093861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14086765288485940741833925 2641268491591113889093861)
                      ·
                        rfl

theorem cell23_5143852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_5143852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143852 prefixEnd_5143852 := by exact prefixLift 5143852
  have htrace : WordTrace (prefixWord ++ tailWord_5143852) baseStart_5143852 baseEnd_5143852 := by
    simpa [prefixWord, tailWord_5143852, baseEnd_5143852] using wordTrace_append hprefix tailTrace_5143852
  have hstable : (prefixWord ++ tailWord_5143852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143852).length < 2 ^ (prefixWord ++ tailWord_5143852).sum := by decide
  have hdescent : baseEnd_5143852 < baseStart_5143852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143873 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5143873 : Nat := 118140960795 + 5143873 * 2 ^ 59
def prefixEnd_5143873 : Nat := 4983230072969 + 3 ^ 40 * 5143873 * 2
def baseEnd_5143873 : Nat := 2641279274684858306931265

theorem tailTrace_5143873 : CollatzResearch.WordTrace tailWord_5143873 prefixEnd_5143873 2641279274684858306931265 := by
  unfold tailWord_5143873
  simp only [CollatzResearch.WordTrace]
  refine ⟨187612461293634099412268273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125074974195756066274845515 187612461293634099412268273)
  ·
    refine ⟨140709345970225574559201205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187612461293634099412268273 140709345970225574559201205)
    ·
      refine ⟨13191501184708647614925113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140709345970225574559201205 13191501184708647614925113)
      ·
        refine ⟨9893625888531485711193835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13191501184708647614925113 9893625888531485711193835)
        ·
          refine ⟨14840438832797228566790753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9893625888531485711193835 14840438832797228566790753)
          ·
            refine ⟨11130329124597921425093065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14840438832797228566790753 11130329124597921425093065)
            ·
              refine ⟨8347746843448441068819799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11130329124597921425093065 8347746843448441068819799)
              ·
                refine ⟨12521620265172661603229699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8347746843448441068819799 12521620265172661603229699)
                ·
                  refine ⟨18782430397758992404844549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12521620265172661603229699 18782430397758992404844549)
                  ·
                    refine ⟨3521705699579811075908353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18782430397758992404844549 3521705699579811075908353)
                    ·
                      refine ⟨2641279274684858306931265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3521705699579811075908353 2641279274684858306931265)
                      ·
                        rfl

theorem cell23_5143873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5143873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143873 prefixEnd_5143873 := by exact prefixLift 5143873
  have htrace : WordTrace (prefixWord ++ tailWord_5143873) baseStart_5143873 baseEnd_5143873 := by
    simpa [prefixWord, tailWord_5143873, baseEnd_5143873] using wordTrace_append hprefix tailTrace_5143873
  have hstable : (prefixWord ++ tailWord_5143873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143873).length < 2 ^ (prefixWord ++ tailWord_5143873).sum := by decide
  have hdescent : baseEnd_5143873 < baseStart_5143873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5143894 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5143894 : Nat := 118140960795 + 5143894 * 2 ^ 59
def prefixEnd_5143894 : Nat := 4983230072969 + 3 ^ 40 * 5143894 * 2
def baseEnd_5143894 : Nat := 2641290057778602724768669

theorem tailTrace_5143894 : CollatzResearch.WordTrace tailWord_5143894 prefixEnd_5143894 2641290057778602724768669 := by
  unfold tailWord_5143894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11725826701659876249923921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125075484817705346665855157 11725826701659876249923921)
  ·
    refine ⟨8794370026244907187442941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11725826701659876249923921 8794370026244907187442941)
    ·
      refine ⟨3297888759841840195291103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8794370026244907187442941 3297888759841840195291103)
      ·
        refine ⟨4946833139762760292936655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3297888759841840195291103 4946833139762760292936655)
        ·
          refine ⟨7420249709644140439404983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946833139762760292936655 7420249709644140439404983)
          ·
            refine ⟨11130374564466210659107475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420249709644140439404983 11130374564466210659107475)
            ·
              refine ⟨16695561846699315988661213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11130374564466210659107475 16695561846699315988661213)
              ·
                refine ⟨6260835692512243495747955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16695561846699315988661213 6260835692512243495747955)
                ·
                  refine ⟨9391253538768365243621933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6260835692512243495747955 9391253538768365243621933)
                  ·
                    refine ⟨3521720077038136966358225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9391253538768365243621933 3521720077038136966358225)
                    ·
                      refine ⟨2641290057778602724768669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3521720077038136966358225 2641290057778602724768669)
                      ·
                        rfl

theorem cell23_5143894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5143894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5143894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5143894 prefixEnd_5143894 := by exact prefixLift 5143894
  have htrace : WordTrace (prefixWord ++ tailWord_5143894) baseStart_5143894 baseEnd_5143894 := by
    simpa [prefixWord, tailWord_5143894, baseEnd_5143894] using wordTrace_append hprefix tailTrace_5143894
  have hstable : (prefixWord ++ tailWord_5143894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5143894).length < 2 ^ (prefixWord ++ tailWord_5143894).sum := by decide
  have hdescent : baseEnd_5143894 < baseStart_5143894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5143894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144046 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_5144046 : Nat := 118140960795 + 5144046 * 2 ^ 59
def prefixEnd_5144046 : Nat := 4983230072969 + 3 ^ 40 * 5144046 * 2
def baseEnd_5144046 : Nat := 880456035612695376689323

theorem tailTrace_5144046 : CollatzResearch.WordTrace tailWord_5144046 prefixEnd_5144046 880456035612695376689323 := by
  unfold tailWord_5144046
  simp only [CollatzResearch.WordTrace]
  refine ⟨23452346390250918744789499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125079180748004899972210661 23452346390250918744789499)
  ·
    refine ⟨35178519585376378117184249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23452346390250918744789499 35178519585376378117184249)
    ·
      refine ⟨26383889689032283587888187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35178519585376378117184249 26383889689032283587888187)
      ·
        refine ⟨39575834533548425381832281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26383889689032283587888187 39575834533548425381832281)
        ·
          refine ⟨29681875900161319036374211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39575834533548425381832281 29681875900161319036374211)
          ·
            refine ⟨44522813850241978554561317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29681875900161319036374211 44522813850241978554561317)
            ·
              refine ⟨8348027596920370978980247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44522813850241978554561317 8348027596920370978980247)
              ·
                refine ⟨12522041395380556468470371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8348027596920370978980247 12522041395380556468470371)
                ·
                  refine ⟨18783062093070834702705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12522041395380556468470371 18783062093070834702705557)
                  ·
                    refine ⟨880456035612695376689323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18783062093070834702705557 880456035612695376689323)
                    ·
                      rfl

theorem cell23_5144046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_5144046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144046 prefixEnd_5144046 := by exact prefixLift 5144046
  have htrace : WordTrace (prefixWord ++ tailWord_5144046) baseStart_5144046 baseEnd_5144046 := by
    simpa [prefixWord, tailWord_5144046, baseEnd_5144046] using wordTrace_append hprefix tailTrace_5144046
  have hstable : (prefixWord ++ tailWord_5144046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144046).length < 2 ^ (prefixWord ++ tailWord_5144046).sum := by decide
  have hdescent : baseEnd_5144046 < baseStart_5144046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144053 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5144053 : Nat := 118140960795 + 5144053 * 2 ^ 59
def prefixEnd_5144053 : Nat := 4983230072969 + 3 ^ 40 * 5144053 * 2
def baseEnd_5144053 : Nat := 2641371701202667602680437

theorem tailTrace_5144053 : CollatzResearch.WordTrace tailWord_5144053 prefixEnd_5144053 2641371701202667602680437 := by
  unfold tailWord_5144053
  simp only [CollatzResearch.WordTrace]
  refine ⟨187619026432981990153820813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125079350955321326769213875 187619026432981990153820813)
  ·
    refine ⟨70357134912368246307682805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187619026432981990153820813 70357134912368246307682805)
    ·
      refine ⟨6595981398034523091345263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70357134912368246307682805 6595981398034523091345263)
      ·
        refine ⟨9893972097051784637017895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6595981398034523091345263 9893972097051784637017895)
        ·
          refine ⟨14840958145577676955526843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9893972097051784637017895 14840958145577676955526843)
          ·
            refine ⟨22261437218366515433290265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14840958145577676955526843 22261437218366515433290265)
            ·
              refine ⟨16696077913774886574967699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22261437218366515433290265 16696077913774886574967699)
              ·
                refine ⟨25044116870662329862451549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16696077913774886574967699 25044116870662329862451549)
                ·
                  refine ⟨9391543826498373698419331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25044116870662329862451549 9391543826498373698419331)
                  ·
                    refine ⟨14087315739747560547628997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9391543826498373698419331 14087315739747560547628997)
                    ·
                      refine ⟨2641371701202667602680437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14087315739747560547628997 2641371701202667602680437)
                      ·
                        rfl

theorem cell23_5144053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5144053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144053 prefixEnd_5144053 := by exact prefixLift 5144053
  have htrace : WordTrace (prefixWord ++ tailWord_5144053) baseStart_5144053 baseEnd_5144053 := by
    simpa [prefixWord, tailWord_5144053, baseEnd_5144053] using wordTrace_append hprefix tailTrace_5144053
  have hstable : (prefixWord ++ tailWord_5144053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144053).length < 2 ^ (prefixWord ++ tailWord_5144053).sum := by decide
  have hdescent : baseEnd_5144053 < baseStart_5144053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144056 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_5144056 : Nat := 118140960795 + 5144056 * 2 ^ 59
def prefixEnd_5144056 : Nat := 4983230072969 + 3 ^ 40 * 5144056 * 2
def baseEnd_5144056 : Nat := 2641373241644631090942923

theorem tailTrace_5144056 : CollatzResearch.WordTrace tailWord_5144056 prefixEnd_5144056 2641373241644631090942923 := by
  unfold tailWord_5144056
  simp only [CollatzResearch.WordTrace]
  refine ⟨93809567925985560833090011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125079423901314081110786681 93809567925985560833090011)
  ·
    refine ⟨140714351888978341249635017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93809567925985560833090011 140714351888978341249635017)
    ·
      refine ⟨105535763916733755937226263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140714351888978341249635017 105535763916733755937226263)
      ·
        refine ⟨158303645875100633905839395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105535763916733755937226263 158303645875100633905839395)
        ·
          refine ⟨237455468812650950858759093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158303645875100633905839395 237455468812650950858759093)
          ·
            refine ⟨22261450201186026643008665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237455468812650950858759093 22261450201186026643008665)
            ·
              refine ⟨16696087650889519982256499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22261450201186026643008665 16696087650889519982256499)
              ·
                refine ⟨25044131476334279973384749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16696087650889519982256499 25044131476334279973384749)
                ·
                  refine ⟨9391549303625354990019281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25044131476334279973384749 9391549303625354990019281)
                  ·
                    refine ⟨7043661977719016242514461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9391549303625354990019281 7043661977719016242514461)
                    ·
                      refine ⟨2641373241644631090942923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7043661977719016242514461 2641373241644631090942923)
                      ·
                        rfl

theorem cell23_5144056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_5144056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144056 prefixEnd_5144056 := by exact prefixLift 5144056
  have htrace : WordTrace (prefixWord ++ tailWord_5144056) baseStart_5144056 baseEnd_5144056 := by
    simpa [prefixWord, tailWord_5144056, baseEnd_5144056] using wordTrace_append hprefix tailTrace_5144056
  have hstable : (prefixWord ++ tailWord_5144056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144056).length < 2 ^ (prefixWord ++ tailWord_5144056).sum := by decide
  have hdescent : baseEnd_5144056 < baseStart_5144056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144179 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 5, 7]
def baseStart_5144179 : Nat := 118140960795 + 5144179 * 2 ^ 59
def prefixEnd_5144179 : Nat := 4983230072969 + 3 ^ 40 * 5144179 * 2
def baseEnd_5144179 : Nat := 880478799921711369901619

theorem tailTrace_5144179 : CollatzResearch.WordTrace tailWord_5144179 prefixEnd_5144179 880478799921711369901619 := by
  unfold tailWord_5144179
  simp only [CollatzResearch.WordTrace]
  refine ⟨187623622030525513672907591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125082414687017009115271727 187623622030525513672907591)
  ·
    refine ⟨281435433045788270509361387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187623622030525513672907591 281435433045788270509361387)
    ·
      refine ⟨422153149568682405764042081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281435433045788270509361387 422153149568682405764042081)
      ·
        refine ⟨316614862176511804323031561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422153149568682405764042081 316614862176511804323031561)
        ·
          refine ⟨237461146632383853242273671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316614862176511804323031561 237461146632383853242273671)
          ·
            refine ⟨356191719948575779863410507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237461146632383853242273671 356191719948575779863410507)
            ·
              refine ⟨534287579922863669795115761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356191719948575779863410507 534287579922863669795115761)
              ·
                refine ⟨400715684942147752346336821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534287579922863669795115761 400715684942147752346336821)
                ·
                  refine ⟨37567095463326351782469077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 400715684942147752346336821 37567095463326351782469077)
                  ·
                    refine ⟨880478799921711369901619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37567095463326351782469077 880478799921711369901619)
                    ·
                      rfl

theorem cell23_5144179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 7].length) (baseStart_5144179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144179 prefixEnd_5144179 := by exact prefixLift 5144179
  have htrace : WordTrace (prefixWord ++ tailWord_5144179) baseStart_5144179 baseEnd_5144179 := by
    simpa [prefixWord, tailWord_5144179, baseEnd_5144179] using wordTrace_append hprefix tailTrace_5144179
  have hstable : (prefixWord ++ tailWord_5144179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144179).length < 2 ^ (prefixWord ++ tailWord_5144179).sum := by decide
  have hdescent : baseEnd_5144179 < baseStart_5144179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144210 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_5144210 : Nat := 118140960795 + 5144210 * 2 ^ 59
def prefixEnd_5144210 : Nat := 4983230072969 + 3 ^ 40 * 5144210 * 2
def baseEnd_5144210 : Nat := 2641452317665423488417215

theorem tailTrace_5144210 : CollatzResearch.WordTrace tailWord_5144210 prefixEnd_5144210 2641452317665423488417215 := by
  unfold tailWord_5144210
  simp only [CollatzResearch.WordTrace]
  refine ⟨46906188173353301491821521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125083168462275470644857389 46906188173353301491821521)
  ·
    refine ⟨35179641130014976118866141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46906188173353301491821521 35179641130014976118866141)
    ·
      refine ⟨13192365423755616044574803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35179641130014976118866141 13192365423755616044574803)
      ·
        refine ⟨19788548135633424066862205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13192365423755616044574803 19788548135633424066862205)
        ·
          refine ⟨7420705550862534025073327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19788548135633424066862205 7420705550862534025073327)
          ·
            refine ⟨11131058326293801037609991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420705550862534025073327 11131058326293801037609991)
            ·
              refine ⟨16696587489440701556414987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11131058326293801037609991 16696587489440701556414987)
              ·
                refine ⟨25044881234161052334622481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16696587489440701556414987 25044881234161052334622481)
                ·
                  refine ⟨18783660925620789250966861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25044881234161052334622481 18783660925620789250966861)
                  ·
                    refine ⟨7043872847107795969112573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18783660925620789250966861 7043872847107795969112573)
                    ·
                      refine ⟨2641452317665423488417215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7043872847107795969112573 2641452317665423488417215)
                      ·
                        rfl

theorem cell23_5144210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_5144210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144210 prefixEnd_5144210 := by exact prefixLift 5144210
  have htrace : WordTrace (prefixWord ++ tailWord_5144210) baseStart_5144210 baseEnd_5144210 := by
    simpa [prefixWord, tailWord_5144210, baseEnd_5144210] using wordTrace_append hprefix tailTrace_5144210
  have hstable : (prefixWord ++ tailWord_5144210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144210).length < 2 ^ (prefixWord ++ tailWord_5144210).sum := by decide
  have hdescent : baseEnd_5144210 < baseStart_5144210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144253 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_5144253 : Nat := 118140960795 + 5144253 * 2 ^ 59
def prefixEnd_5144253 : Nat := 4983230072969 + 3 ^ 40 * 5144253 * 2
def baseEnd_5144253 : Nat := 2641474397333566820179517

theorem tailTrace_5144253 : CollatzResearch.WordTrace tailWord_5144253 prefixEnd_5144253 2641474397333566820179517 := by
  unfold tailWord_5144253
  simp only [CollatzResearch.WordTrace]
  refine ⟨187626321032257424311101413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125084214021504949540734275 187626321032257424311101413)
  ·
    refine ⟨35179935193548267058331515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187626321032257424311101413 35179935193548267058331515)
    ·
      refine ⟨52769902790322400587497273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35179935193548267058331515 52769902790322400587497273)
      ·
        refine ⟨39577427092741800440622955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52769902790322400587497273 39577427092741800440622955)
        ·
          refine ⟨59366140639112700660934433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39577427092741800440622955 59366140639112700660934433)
          ·
            refine ⟨44524605479334525495700825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59366140639112700660934433 44524605479334525495700825)
            ·
              refine ⟨33393454109500894121775619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44524605479334525495700825 33393454109500894121775619)
              ·
                refine ⟨50090181164251341182663429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33393454109500894121775619 50090181164251341182663429)
                ·
                  refine ⟨9391908968297126471749393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50090181164251341182663429 9391908968297126471749393)
                  ·
                    refine ⟨7043931726222844853812045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9391908968297126471749393 7043931726222844853812045)
                    ·
                      refine ⟨2641474397333566820179517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7043931726222844853812045 2641474397333566820179517)
                      ·
                        rfl

theorem cell23_5144253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_5144253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144253 prefixEnd_5144253 := by exact prefixLift 5144253
  have htrace : WordTrace (prefixWord ++ tailWord_5144253) baseStart_5144253 baseEnd_5144253 := by
    simpa [prefixWord, tailWord_5144253, baseEnd_5144253] using wordTrace_append hprefix tailTrace_5144253
  have hstable : (prefixWord ++ tailWord_5144253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144253).length < 2 ^ (prefixWord ++ tailWord_5144253).sum := by decide
  have hdescent : baseEnd_5144253 < baseStart_5144253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144256 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 8]
def baseStart_5144256 : Nat := 118140960795 + 5144256 * 2 ^ 59
def prefixEnd_5144256 : Nat := 4983230072969 + 3 ^ 40 * 5144256 * 2
def baseEnd_5144256 : Nat := 293497326419503367604667

theorem tailTrace_5144256 : CollatzResearch.WordTrace tailWord_5144256 prefixEnd_5144256 293497326419503367604667 := by
  unfold tailWord_5144256
  simp only [CollatzResearch.WordTrace]
  refine ⟨93813215225623277911730311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125084286967497703882307081 93813215225623277911730311)
  ·
    refine ⟨140719822838434916867595467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93813215225623277911730311 140719822838434916867595467)
    ·
      refine ⟨211079734257652375301393201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140719822838434916867595467 211079734257652375301393201)
      ·
        refine ⟨158309800693239281476044901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211079734257652375301393201 158309800693239281476044901)
        ·
          refine ⟨29683087629982365276758419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158309800693239281476044901 29683087629982365276758419)
          ·
            refine ⟨44524631444973547915137629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29683087629982365276758419 44524631444973547915137629)
            ·
              refine ⟨16696736791865080468176611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44524631444973547915137629 16696736791865080468176611)
              ·
                refine ⟨25045105187797620702264917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16696736791865080468176611 25045105187797620702264917)
                ·
                  refine ⟨293497326419503367604667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25045105187797620702264917 293497326419503367604667)
                  ·
                    rfl

theorem cell23_5144256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 8].length) (baseStart_5144256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144256 prefixEnd_5144256 := by exact prefixLift 5144256
  have htrace : WordTrace (prefixWord ++ tailWord_5144256) baseStart_5144256 baseEnd_5144256 := by
    simpa [prefixWord, tailWord_5144256, baseEnd_5144256] using wordTrace_append hprefix tailTrace_5144256
  have hstable : (prefixWord ++ tailWord_5144256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144256).length < 2 ^ (prefixWord ++ tailWord_5144256).sum := by decide
  have hdescent : baseEnd_5144256 < baseStart_5144256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144260 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_5144260 : Nat := 118140960795 + 5144260 * 2 ^ 59
def prefixEnd_5144260 : Nat := 4983230072969 + 3 ^ 40 * 5144260 * 2
def baseEnd_5144260 : Nat := 880492663899382764263995

theorem tailTrace_5144260 : CollatzResearch.WordTrace tailWord_5144260 prefixEnd_5144260 880492663899382764263995 := by
  unfold tailWord_5144260
  simp only [CollatzResearch.WordTrace]
  refine ⟨93813288171616032253303117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125084384228821376337737489 93813288171616032253303117)
  ·
    refine ⟨35179983064356012094988669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93813288171616032253303117 35179983064356012094988669)
    ·
      refine ⟨13192493649133504535620751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35179983064356012094988669 13192493649133504535620751)
      ·
        refine ⟨19788740473700256803431127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13192493649133504535620751 19788740473700256803431127)
        ·
          refine ⟨29683110710550385205146691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19788740473700256803431127 29683110710550385205146691)
          ·
            refine ⟨44524666065825577807720037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29683110710550385205146691 44524666065825577807720037)
            ·
              refine ⟨8348374887342295838947507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44524666065825577807720037 8348374887342295838947507)
              ·
                refine ⟨12522562331013443758421261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8348374887342295838947507 12522562331013443758421261)
                ·
                  refine ⟨4695960874130041409407973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12522562331013443758421261 4695960874130041409407973)
                  ·
                    refine ⟨880492663899382764263995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4695960874130041409407973 880492663899382764263995)
                    ·
                      rfl

theorem cell23_5144260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_5144260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144260 prefixEnd_5144260 := by exact prefixLift 5144260
  have htrace : WordTrace (prefixWord ++ tailWord_5144260) baseStart_5144260 baseEnd_5144260 := by
    simpa [prefixWord, tailWord_5144260, baseEnd_5144260] using wordTrace_append hprefix tailTrace_5144260
  have hstable : (prefixWord ++ tailWord_5144260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144260).length < 2 ^ (prefixWord ++ tailWord_5144260).sum := by decide
  have hdescent : baseEnd_5144260 < baseStart_5144260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144303 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 1, 5]
def baseStart_5144303 : Nat := 118140960795 + 5144303 * 2 ^ 59
def prefixEnd_5144303 : Nat := 4983230072969 + 3 ^ 40 * 5144303 * 2
def baseEnd_5144303 : Nat := 880500023788763874851429

theorem tailTrace_5144303 : CollatzResearch.WordTrace tailWord_5144303 prefixEnd_5144303 880500023788763874851429 := by
  unfold tailWord_5144303
  simp only [CollatzResearch.WordTrace]
  refine ⟨187628144682076282850421563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125085429788050855233614375 187628144682076282850421563)
  ·
    refine ⟨281442217023114424275632345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187628144682076282850421563 281442217023114424275632345)
    ·
      refine ⟨211081662767335818206724259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281442217023114424275632345 211081662767335818206724259)
      ·
        refine ⟨316622494151003727310086389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211081662767335818206724259 316622494151003727310086389)
        ·
          refine ⟨29683358826656599435320599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 316622494151003727310086389 29683358826656599435320599)
          ·
            refine ⟨44525038239984899152980899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29683358826656599435320599 44525038239984899152980899)
            ·
              refine ⟨66787557359977348729471349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44525038239984899152980899 66787557359977348729471349)
              ·
                refine ⟨6261333502497876443387939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66787557359977348729471349 6261333502497876443387939)
                ·
                  refine ⟨9392000253746814665081909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6261333502497876443387939 9392000253746814665081909)
                  ·
                    refine ⟨880500023788763874851429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9392000253746814665081909 880500023788763874851429)
                    ·
                      rfl

theorem cell23_5144303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_5144303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144303 prefixEnd_5144303 := by exact prefixLift 5144303
  have htrace : WordTrace (prefixWord ++ tailWord_5144303) baseStart_5144303 baseEnd_5144303 := by
    simpa [prefixWord, tailWord_5144303, baseEnd_5144303] using wordTrace_append hprefix tailTrace_5144303
  have hstable : (prefixWord ++ tailWord_5144303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144303).length < 2 ^ (prefixWord ++ tailWord_5144303).sum := by decide
  have hdescent : baseEnd_5144303 < baseStart_5144303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144353 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_5144353 : Nat := 118140960795 + 5144353 * 2 ^ 59
def prefixEnd_5144353 : Nat := 4983230072969 + 3 ^ 40 * 5144353 * 2
def baseEnd_5144353 : Nat := 2641525745399016428929057

theorem tailTrace_5144353 : CollatzResearch.WordTrace tailWord_5144353 prefixEnd_5144353 2641525745399016428929057 := by
  unfold tailWord_5144353
  simp only [CollatzResearch.WordTrace]
  refine ⟨187629968331895141389741713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125086645554596760926494475 187629968331895141389741713)
  ·
    refine ⟨140722476248921356042306285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187629968331895141389741713 140722476248921356042306285)
    ·
      refine ⟨52770928593345508515864857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140722476248921356042306285 52770928593345508515864857)
      ·
        refine ⟨39578196445009131386898643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52770928593345508515864857 39578196445009131386898643)
        ·
          refine ⟨59367294667513697080347965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39578196445009131386898643 59367294667513697080347965)
          ·
            refine ⟨22262735500317636405130487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59367294667513697080347965 22262735500317636405130487)
            ·
              refine ⟨33394103250476454607695731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22262735500317636405130487 33394103250476454607695731)
              ·
                refine ⟨50091154875714681911543597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33394103250476454607695731 50091154875714681911543597)
                ·
                  refine ⟨18784183078393005716828849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50091154875714681911543597 18784183078393005716828849)
                  ·
                    refine ⟨14088137308794754287621637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18784183078393005716828849 14088137308794754287621637)
                    ·
                      refine ⟨2641525745399016428929057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14088137308794754287621637 2641525745399016428929057)
                      ·
                        rfl

theorem cell23_5144353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_5144353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144353 prefixEnd_5144353 := by exact prefixLift 5144353
  have htrace : WordTrace (prefixWord ++ tailWord_5144353) baseStart_5144353 baseEnd_5144353 := by
    simpa [prefixWord, tailWord_5144353, baseEnd_5144353] using wordTrace_append hprefix tailTrace_5144353
  have hstable : (prefixWord ++ tailWord_5144353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144353).length < 2 ^ (prefixWord ++ tailWord_5144353).sum := by decide
  have hdescent : baseEnd_5144353 < baseStart_5144353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144357 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 1, 1, 4]
def baseStart_5144357 : Nat := 118140960795 + 5144357 * 2 ^ 59
def prefixEnd_5144357 : Nat := 4983230072969 + 3 ^ 40 * 5144357 * 2
def baseEnd_5144357 : Nat := 2641527799321634413279039

theorem tailTrace_5144357 : CollatzResearch.WordTrace tailWord_5144357 prefixEnd_5144357 2641527799321634413279039 := by
  unfold tailWord_5144357
  simp only [CollatzResearch.WordTrace]
  refine ⟨187630114223880650072887325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125086742815920433381924883 187630114223880650072887325)
  ·
    refine ⟨70361292833955243777332747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187630114223880650072887325 70361292833955243777332747)
    ·
      refine ⟨105541939250932865665999121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70361292833955243777332747 105541939250932865665999121)
      ·
        refine ⟨79156454438199649249499341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105541939250932865665999121 79156454438199649249499341)
        ·
          refine ⟨29683670414324868468562253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79156454438199649249499341 29683670414324868468562253)
          ·
            refine ⟨11131376405371825675710845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29683670414324868468562253 11131376405371825675710845)
            ·
              refine ⟨4174266152014434628391567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11131376405371825675710845 4174266152014434628391567)
              ·
                refine ⟨6261399228021651942587351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4174266152014434628391567 6261399228021651942587351)
                ·
                  refine ⟨9392098842032477913881027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6261399228021651942587351 9392098842032477913881027)
                  ·
                    refine ⟨14088148263048716870821541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9392098842032477913881027 14088148263048716870821541)
                    ·
                      refine ⟨2641527799321634413279039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14088148263048716870821541 2641527799321634413279039)
                      ·
                        rfl

theorem cell23_5144357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_5144357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144357 prefixEnd_5144357 := by exact prefixLift 5144357
  have htrace : WordTrace (prefixWord ++ tailWord_5144357) baseStart_5144357 baseEnd_5144357 := by
    simpa [prefixWord, tailWord_5144357, baseEnd_5144357] using wordTrace_append hprefix tailTrace_5144357
  have hstable : (prefixWord ++ tailWord_5144357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144357).length < 2 ^ (prefixWord ++ tailWord_5144357).sum := by decide
  have hdescent : baseEnd_5144357 < baseStart_5144357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144360 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_5144360 : Nat := 118140960795 + 5144360 * 2 ^ 59
def prefixEnd_5144360 : Nat := 4983230072969 + 3 ^ 40 * 5144360 * 2
def baseEnd_5144360 : Nat := 2641529339763597901541525

theorem tailTrace_5144360 : CollatzResearch.WordTrace tailWord_5144360 prefixEnd_5144360 2641529339763597901541525 := by
  unfold tailWord_5144360
  simp only [CollatzResearch.WordTrace]
  refine ⟨93815111821434890792623267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125086815761913187723497689 93815111821434890792623267)
  ·
    refine ⟨140722667732152336188934901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93815111821434890792623267 140722667732152336188934901)
    ·
      refine ⟨13192750099889281517712647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140722667732152336188934901 13192750099889281517712647)
      ·
        refine ⟨19789125149833922276568971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13192750099889281517712647 19789125149833922276568971)
        ·
          refine ⟨29683687724750883414853457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19789125149833922276568971 29683687724750883414853457)
          ·
            refine ⟨22262765793563162561140093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29683687724750883414853457 22262765793563162561140093)
            ·
              refine ⟨8348537172586185960427535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22262765793563162561140093 8348537172586185960427535)
              ·
                refine ⟨12522805758879278940641303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8348537172586185960427535 12522805758879278940641303)
                ·
                  refine ⟨18784208638318918410961955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12522805758879278940641303 18784208638318918410961955)
                  ·
                    refine ⟨28176312957478377616442933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18784208638318918410961955 28176312957478377616442933)
                    ·
                      refine ⟨2641529339763597901541525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28176312957478377616442933 2641529339763597901541525)
                      ·
                        rfl

theorem cell23_5144360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_5144360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144360 prefixEnd_5144360 := by exact prefixLift 5144360
  have htrace : WordTrace (prefixWord ++ tailWord_5144360) baseStart_5144360 baseEnd_5144360 := by
    simpa [prefixWord, tailWord_5144360, baseEnd_5144360] using wordTrace_append hprefix tailTrace_5144360
  have hstable : (prefixWord ++ tailWord_5144360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144360).length < 2 ^ (prefixWord ++ tailWord_5144360).sum := by decide
  have hdescent : baseEnd_5144360 < baseStart_5144360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144397 : List Nat := [1, 6, 1, 2, 1, 2, 3, 7]
def baseStart_5144397 : Nat := 118140960795 + 5144397 * 2 ^ 59
def prefixEnd_5144397 : Nat := 4983230072969 + 3 ^ 40 * 5144397 * 2
def baseEnd_5144397 : Nat := 97835123649919046547365

theorem tailTrace_5144397 : CollatzResearch.WordTrace tailWord_5144397 prefixEnd_5144397 97835123649919046547365 := by
  unfold tailWord_5144397
  simp only [CollatzResearch.WordTrace]
  refine ⟨187631573143735736904343445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125087715429157157936228963 187631573143735736904343445)
  ·
    refine ⟨8795229991112612667391099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187631573143735736904343445 8795229991112612667391099)
    ·
      refine ⟨13192844986668919001086649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8795229991112612667391099 13192844986668919001086649)
      ·
        refine ⟨9894633740001689250814987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13192844986668919001086649 9894633740001689250814987)
        ·
          refine ⟨14841950610002533876222481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9894633740001689250814987 14841950610002533876222481)
          ·
            refine ⟨11131462957501900407166861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14841950610002533876222481 11131462957501900407166861)
            ·
              refine ⟨4174298609063212652687573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11131462957501900407166861 4174298609063212652687573)
              ·
                refine ⟨97835123649919046547365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4174298609063212652687573 97835123649919046547365)
                ·
                  rfl

theorem cell23_5144397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 7].length) (baseStart_5144397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144397 prefixEnd_5144397 := by exact prefixLift 5144397
  have htrace : WordTrace (prefixWord ++ tailWord_5144397) baseStart_5144397 baseEnd_5144397 := by
    simpa [prefixWord, tailWord_5144397, baseEnd_5144397] using wordTrace_append hprefix tailTrace_5144397
  have hstable : (prefixWord ++ tailWord_5144397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144397).length < 2 ^ (prefixWord ++ tailWord_5144397).sum := by decide
  have hdescent : baseEnd_5144397 < baseStart_5144397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144417 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_5144417 : Nat := 118140960795 + 5144417 * 2 ^ 59
def prefixEnd_5144417 : Nat := 4983230072969 + 3 ^ 40 * 5144417 * 2
def baseEnd_5144417 : Nat := 2641558608160904178528763

theorem tailTrace_5144417 : CollatzResearch.WordTrace tailWord_5144417 prefixEnd_5144417 2641558608160904178528763 := by
  unfold tailWord_5144417
  simp only [CollatzResearch.WordTrace]
  refine ⟨187632302603663280320071505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125088201735775520213381003 187632302603663280320071505)
  ·
    refine ⟨140724226952747460240053629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187632302603663280320071505 140724226952747460240053629)
    ·
      refine ⟨52771585107280297590020111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140724226952747460240053629 52771585107280297590020111)
      ·
        refine ⟨79157377660920446385030167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52771585107280297590020111 79157377660920446385030167)
        ·
          refine ⟨118736066491380669577545251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79157377660920446385030167 118736066491380669577545251)
          ·
            refine ⟨178104099737071004366317877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118736066491380669577545251 178104099737071004366317877)
            ·
              refine ⟨16697259350350406659342301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178104099737071004366317877 16697259350350406659342301)
              ·
                refine ⟨6261472256381402497253363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16697259350350406659342301 6261472256381402497253363)
                ·
                  refine ⟨9392208384572103745880045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6261472256381402497253363 9392208384572103745880045)
                  ·
                    refine ⟨3522078144214538904705017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9392208384572103745880045 3522078144214538904705017)
                    ·
                      refine ⟨2641558608160904178528763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3522078144214538904705017 2641558608160904178528763)
                      ·
                        rfl

theorem cell23_5144417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_5144417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144417 prefixEnd_5144417 := by exact prefixLift 5144417
  have htrace : WordTrace (prefixWord ++ tailWord_5144417) baseStart_5144417 baseEnd_5144417 := by
    simpa [prefixWord, tailWord_5144417, baseEnd_5144417] using wordTrace_append hprefix tailTrace_5144417
  have hstable : (prefixWord ++ tailWord_5144417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144417).length < 2 ^ (prefixWord ++ tailWord_5144417).sum := by decide
  have hdescent : baseEnd_5144417 < baseStart_5144417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144423 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 4, 6]
def baseStart_5144423 : Nat := 118140960795 + 5144423 * 2 ^ 59
def prefixEnd_5144423 : Nat := 4983230072969 + 3 ^ 40 * 5144423 * 2
def baseEnd_5144423 : Nat := 880520563014943718351245

theorem tailTrace_5144423 : CollatzResearch.WordTrace tailWord_5144423 prefixEnd_5144423 880520563014943718351245 := by
  unfold tailWord_5144423
  simp only [CollatzResearch.WordTrace]
  refine ⟨187632521441641543344789923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125088347627761028896526615 187632521441641543344789923)
  ·
    refine ⟨281448782162462315017184885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187632521441641543344789923 281448782162462315017184885)
    ·
      refine ⟨26385823327730842032861083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 281448782162462315017184885 26385823327730842032861083)
      ·
        refine ⟨39578734991596263049291625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26385823327730842032861083 39578734991596263049291625)
        ·
          refine ⟨29684051243697197286968719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39578734991596263049291625 29684051243697197286968719)
          ·
            refine ⟨44526076865545795930453079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29684051243697197286968719 44526076865545795930453079)
            ·
              refine ⟨66789115298318693895679619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44526076865545795930453079 66789115298318693895679619)
              ·
                refine ⟨100183672947478040843519429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66789115298318693895679619 100183672947478040843519429)
                ·
                  refine ⟨18784438677652132658159893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100183672947478040843519429 18784438677652132658159893)
                  ·
                    refine ⟨880520563014943718351245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18784438677652132658159893 880520563014943718351245)
                    ·
                      rfl

theorem cell23_5144423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_5144423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144423 prefixEnd_5144423 := by exact prefixLift 5144423
  have htrace : WordTrace (prefixWord ++ tailWord_5144423) baseStart_5144423 baseEnd_5144423 := by
    simpa [prefixWord, tailWord_5144423, baseEnd_5144423] using wordTrace_append hprefix tailTrace_5144423
  have hstable : (prefixWord ++ tailWord_5144423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144423).length < 2 ^ (prefixWord ++ tailWord_5144423).sum := by decide
  have hdescent : baseEnd_5144423 < baseStart_5144423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144453 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 7]
def baseStart_5144453 : Nat := 118140960795 + 5144453 * 2 ^ 59
def prefixEnd_5144453 : Nat := 4983230072969 + 3 ^ 40 * 5144453 * 2
def baseEnd_5144453 : Nat := 293508565940496226408733

theorem tailTrace_5144453 : CollatzResearch.WordTrace tailWord_5144453 prefixEnd_5144453 293508565940496226408733 := by
  unfold tailWord_5144453
  simp only [CollatzResearch.WordTrace]
  refine ⟨187633615631532858468382013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125089077087688572312254675 187633615631532858468382013)
  ·
    refine ⟨70362605861824821925643255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187633615631532858468382013 70362605861824821925643255)
    ·
      refine ⟨105543908792737232888464883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70362605861824821925643255 105543908792737232888464883)
      ·
        refine ⟨158315863189105849332697325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105543908792737232888464883 158315863189105849332697325)
        ·
          refine ⟨59368448695914693499761497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158315863189105849332697325 59368448695914693499761497)
          ·
            refine ⟨44526336521936020124821123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59368448695914693499761497 44526336521936020124821123)
            ·
              refine ⟨66789504782904030187231685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44526336521936020124821123 66789504782904030187231685)
              ·
                refine ⟨12523032146794505660105941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66789504782904030187231685 12523032146794505660105941)
                ·
                  refine ⟨293508565940496226408733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12523032146794505660105941 293508565940496226408733)
                  ·
                    rfl

theorem cell23_5144453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_5144453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144453 prefixEnd_5144453 := by exact prefixLift 5144453
  have htrace : WordTrace (prefixWord ++ tailWord_5144453) baseStart_5144453 baseEnd_5144453 := by
    simpa [prefixWord, tailWord_5144453, baseEnd_5144453] using wordTrace_append hprefix tailTrace_5144453
  have hstable : (prefixWord ++ tailWord_5144453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144453).length < 2 ^ (prefixWord ++ tailWord_5144453).sum := by decide
  have hdescent : baseEnd_5144453 < baseStart_5144453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144487 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 7]
def baseStart_5144487 : Nat := 118140960795 + 5144487 * 2 ^ 59
def prefixEnd_5144487 : Nat := 4983230072969 + 3 ^ 40 * 5144487 * 2
def baseEnd_5144487 : Nat := 293510505756302100517049

theorem tailTrace_5144487 : CollatzResearch.WordTrace tailWord_5144487 prefixEnd_5144487 293510505756302100517049 := by
  unfold tailWord_5144487
  simp only [CollatzResearch.WordTrace]
  refine ⟨187634855713409682275119715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125089903808939788183413143 187634855713409682275119715)
  ·
    refine ⟨281452283570114523412679573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187634855713409682275119715 281452283570114523412679573)
    ·
      refine ⟨13193075792349118284969355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 281452283570114523412679573 13193075792349118284969355)
      ·
        refine ⟨19789613688523677427454033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13193075792349118284969355 19789613688523677427454033)
        ·
          refine ⟨14842210266392758070590525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19789613688523677427454033 14842210266392758070590525)
          ·
            refine ⟨5565828849897284276471447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14842210266392758070590525 5565828849897284276471447)
            ·
              refine ⟨8348743274845926414707171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5565828849897284276471447 8348743274845926414707171)
              ·
                refine ⟨12523114912268889622060757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8348743274845926414707171 12523114912268889622060757)
                ·
                  refine ⟨293510505756302100517049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12523114912268889622060757 293510505756302100517049)
                  ·
                    rfl

theorem cell23_5144487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 7].length) (baseStart_5144487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144487 prefixEnd_5144487 := by exact prefixLift 5144487
  have htrace : WordTrace (prefixWord ++ tailWord_5144487) baseStart_5144487 baseEnd_5144487 := by
    simpa [prefixWord, tailWord_5144487, baseEnd_5144487] using wordTrace_append hprefix tailTrace_5144487
  have hstable : (prefixWord ++ tailWord_5144487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144487).length < 2 ^ (prefixWord ++ tailWord_5144487).sum := by decide
  have hdescent : baseEnd_5144487 < baseStart_5144487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144560 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 6]
def baseStart_5144560 : Nat := 118140960795 + 5144560 * 2 ^ 59
def prefixEnd_5144560 : Nat := 4983230072969 + 3 ^ 40 * 5144560 * 2
def baseEnd_5144560 : Nat := 293514670654944124337845

theorem tailTrace_5144560 : CollatzResearch.WordTrace tailWord_5144560 prefixEnd_5144560 293514670654944124337845 := by
  unfold tailWord_5144560
  simp only [CollatzResearch.WordTrace]
  refine ⟨93818759121072607871263567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125091678828096810495018089 93818759121072607871263567)
  ·
    refine ⟨140728138681608911806895351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93818759121072607871263567 140728138681608911806895351)
    ·
      refine ⟨211092208022413367710343027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140728138681608911806895351 211092208022413367710343027)
      ·
        refine ⟨316638312033620051565514541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211092208022413367710343027 316638312033620051565514541)
        ·
          refine ⟨118739367012607519337067953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316638312033620051565514541 118739367012607519337067953)
          ·
            refine ⟨89054525259455639502800965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118739367012607519337067953 89054525259455639502800965)
            ·
              refine ⟨16697723486147932406775181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89054525259455639502800965 16697723486147932406775181)
              ·
                refine ⟨6261646307305474652540693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16697723486147932406775181 6261646307305474652540693)
                ·
                  refine ⟨293514670654944124337845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6261646307305474652540693 293514670654944124337845)
                  ·
                    rfl

theorem cell23_5144560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 6].length) (baseStart_5144560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144560 prefixEnd_5144560 := by exact prefixLift 5144560
  have htrace : WordTrace (prefixWord ++ tailWord_5144560) baseStart_5144560 baseEnd_5144560 := by
    simpa [prefixWord, tailWord_5144560, baseEnd_5144560] using wordTrace_append hprefix tailTrace_5144560
  have hstable : (prefixWord ++ tailWord_5144560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144560).length < 2 ^ (prefixWord ++ tailWord_5144560).sum := by decide
  have hdescent : baseEnd_5144560 < baseStart_5144560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144574 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_5144574 : Nat := 118140960795 + 5144574 * 2 ^ 59
def prefixEnd_5144574 : Nat := 4983230072969 + 3 ^ 40 * 5144574 * 2
def baseEnd_5144574 : Nat := 2641639224623660064265541

theorem tailTrace_5144574 : CollatzResearch.WordTrace tailWord_5144574 prefixEnd_5144574 2641639224623660064265541 := by
  unfold tailWord_5144574
  simp only [CollatzResearch.WordTrace]
  refine ⟨23454753608011812016692097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125092019242729664089024517 23454753608011812016692097)
  ·
    refine ⟨17591065206008859012519073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23454753608011812016692097 17591065206008859012519073)
    ·
      refine ⟨13193298904506644259389305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17591065206008859012519073 13193298904506644259389305)
      ·
        refine ⟨9894974178379983194541979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13193298904506644259389305 9894974178379983194541979)
        ·
          refine ⟨14842461267569974791812969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9894974178379983194541979 14842461267569974791812969)
          ·
            refine ⟨11131845950677481093859727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14842461267569974791812969 11131845950677481093859727)
            ·
              refine ⟨16697768926016221640789591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11131845950677481093859727 16697768926016221640789591)
              ·
                refine ⟨25046653389024332461184387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16697768926016221640789591 25046653389024332461184387)
                ·
                  refine ⟨37569980083536498691776581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25046653389024332461184387 37569980083536498691776581)
                  ·
                    refine ⟨7044371265663093504708109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37569980083536498691776581 7044371265663093504708109)
                    ·
                      refine ⟨2641639224623660064265541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7044371265663093504708109 2641639224623660064265541)
                      ·
                        rfl

theorem cell23_5144574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_5144574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144574 prefixEnd_5144574 := by exact prefixLift 5144574
  have htrace : WordTrace (prefixWord ++ tailWord_5144574) baseStart_5144574 baseEnd_5144574 := by
    simpa [prefixWord, tailWord_5144574, baseEnd_5144574] using wordTrace_append hprefix tailTrace_5144574
  have hstable : (prefixWord ++ tailWord_5144574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144574).length < 2 ^ (prefixWord ++ tailWord_5144574).sum := by decide
  have hdescent : baseEnd_5144574 < baseStart_5144574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144587 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 3]
def baseStart_5144587 : Nat := 118140960795 + 5144587 * 2 ^ 59
def prefixEnd_5144587 : Nat := 4983230072969 + 3 ^ 40 * 5144587 * 2
def baseEnd_5144587 : Nat := 2641645899872168513402981

theorem tailTrace_5144587 : CollatzResearch.WordTrace tailWord_5144587 prefixEnd_5144587 2641645899872168513402981 := by
  unfold tailWord_5144587
  simp only [CollatzResearch.WordTrace]
  refine ⟨187638503013047399353760015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125092335342031599569173343 187638503013047399353760015)
  ·
    refine ⟨281457754519571099030640023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187638503013047399353760015 281457754519571099030640023)
    ·
      refine ⟨422186631779356648545960035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281457754519571099030640023 422186631779356648545960035)
      ·
        refine ⟨633279947669034972818940053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422186631779356648545960035 633279947669034972818940053)
        ·
          refine ⟨29684997546986014350887815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 633279947669034972818940053 29684997546986014350887815)
          ·
            refine ⟨44527496320479021526331723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29684997546986014350887815 44527496320479021526331723)
            ·
              refine ⟨66791244480718532289497585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44527496320479021526331723 66791244480718532289497585)
              ·
                refine ⟨50093433360538899217123189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66791244480718532289497585 50093433360538899217123189)
                ·
                  refine ⟨4696259377550521801605299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50093433360538899217123189 4696259377550521801605299)
                  ·
                    refine ⟨7044389066325782702407949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4696259377550521801605299 7044389066325782702407949)
                    ·
                      refine ⟨2641645899872168513402981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7044389066325782702407949 2641645899872168513402981)
                      ·
                        rfl

theorem cell23_5144587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 3].length) (baseStart_5144587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144587 prefixEnd_5144587 := by exact prefixLift 5144587
  have htrace : WordTrace (prefixWord ++ tailWord_5144587) baseStart_5144587 baseEnd_5144587 := by
    simpa [prefixWord, tailWord_5144587, baseEnd_5144587] using wordTrace_append hprefix tailTrace_5144587
  have hstable : (prefixWord ++ tailWord_5144587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144587).length < 2 ^ (prefixWord ++ tailWord_5144587).sum := by decide
  have hdescent : baseEnd_5144587 < baseStart_5144587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144604 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_5144604 : Nat := 118140960795 + 5144604 * 2 ^ 59
def prefixEnd_5144604 : Nat := 4983230072969 + 3 ^ 40 * 5144604 * 2
def baseEnd_5144604 : Nat := 2641654629043294946890403

theorem tailTrace_5144604 : CollatzResearch.WordTrace tailWord_5144604 prefixEnd_5144604 2641654629043294946890403 := by
  unfold tailWord_5144604
  simp only [CollatzResearch.WordTrace]
  refine ⟨93819561526992905628564433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125092748702657207504752577 93819561526992905628564433)
  ·
    refine ⟨70364671145244679221423325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93819561526992905628564433 70364671145244679221423325)
    ·
      refine ⟨26386751679466754708033747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70364671145244679221423325 26386751679466754708033747)
      ·
        refine ⟨39580127519200132062050621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26386751679466754708033747 39580127519200132062050621)
        ·
          refine ⟨14842547819700049523268983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39580127519200132062050621 14842547819700049523268983)
          ·
            refine ⟨22263821729550074284903475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14842547819700049523268983 22263821729550074284903475)
            ·
              refine ⟨33395732594325111427355213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22263821729550074284903475 33395732594325111427355213)
              ·
                refine ⟨12523399722871916785258205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33395732594325111427355213 12523399722871916785258205)
                ·
                  refine ⟨4696274896076968794471827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12523399722871916785258205 4696274896076968794471827)
                  ·
                    refine ⟨7044412344115453191707741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4696274896076968794471827 7044412344115453191707741)
                    ·
                      refine ⟨2641654629043294946890403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7044412344115453191707741 2641654629043294946890403)
                      ·
                        rfl

theorem cell23_5144604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_5144604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144604 prefixEnd_5144604 := by exact prefixLift 5144604
  have htrace : WordTrace (prefixWord ++ tailWord_5144604) baseStart_5144604 baseEnd_5144604 := by
    simpa [prefixWord, tailWord_5144604, baseEnd_5144604] using wordTrace_append hprefix tailTrace_5144604
  have hstable : (prefixWord ++ tailWord_5144604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144604).length < 2 ^ (prefixWord ++ tailWord_5144604).sum := by decide
  have hdescent : baseEnd_5144604 < baseStart_5144604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144620 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_5144620 : Nat := 118140960795 + 5144620 * 2 ^ 59
def prefixEnd_5144620 : Nat := 4983230072969 + 3 ^ 40 * 5144620 * 2
def baseEnd_5144620 : Nat := 880554281577922294763443

theorem tailTrace_5144620 : CollatzResearch.WordTrace tailWord_5144620 prefixEnd_5144620 880554281577922294763443 := by
  unfold tailWord_5144620
  simp only [CollatzResearch.WordTrace]
  refine ⟨93819853310963922994855657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125093137747951897326474209 93819853310963922994855657)
  ·
    refine ⟨70364889983222942246141743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93819853310963922994855657 70364889983222942246141743)
    ·
      refine ⟨105547334974834413369212615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70364889983222942246141743 105547334974834413369212615)
      ·
        refine ⟨158321002462251620053818923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105547334974834413369212615 158321002462251620053818923)
        ·
          refine ⟨237481503693377430080728385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158321002462251620053818923 237481503693377430080728385)
          ·
            refine ⟨178111127770033072560546289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237481503693377430080728385 178111127770033072560546289)
            ·
              refine ⟨133583345827524804420409717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178111127770033072560546289 133583345827524804420409717)
              ·
                refine ⟨12523438671330450414413411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133583345827524804420409717 12523438671330450414413411)
                ·
                  refine ⟨18785158006995675621620117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12523438671330450414413411 18785158006995675621620117)
                  ·
                    refine ⟨880554281577922294763443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18785158006995675621620117 880554281577922294763443)
                    ·
                      rfl

theorem cell23_5144620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_5144620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144620 prefixEnd_5144620 := by exact prefixLift 5144620
  have htrace : WordTrace (prefixWord ++ tailWord_5144620) baseStart_5144620 baseEnd_5144620 := by
    simpa [prefixWord, tailWord_5144620, baseEnd_5144620] using wordTrace_append hprefix tailTrace_5144620
  have hstable : (prefixWord ++ tailWord_5144620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144620).length < 2 ^ (prefixWord ++ tailWord_5144620).sum := by decide
  have hdescent : baseEnd_5144620 < baseStart_5144620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144627 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 4]
def baseStart_5144627 : Nat := 118140960795 + 5144627 * 2 ^ 59
def prefixEnd_5144627 : Nat := 4983230072969 + 3 ^ 40 * 5144627 * 2
def baseEnd_5144627 : Nat := 2641666439098348356902797

theorem tailTrace_5144627 : CollatzResearch.WordTrace tailWord_5144627 prefixEnd_5144627 2641666439098348356902797 := by
  unfold tailWord_5144627
  simp only [CollatzResearch.WordTrace]
  refine ⟨187639961932902486185216135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125093307955268324123477423 187639961932902486185216135)
  ·
    refine ⟨281459942899353729277824203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187639961932902486185216135 281459942899353729277824203)
    ·
      refine ⟨422189914349030593916736305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281459942899353729277824203 422189914349030593916736305)
      ·
        refine ⟨316642435761772945437552229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422189914349030593916736305 316642435761772945437552229)
        ·
          refine ⟨59370456705332427269541043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 316642435761772945437552229 59370456705332427269541043)
          ·
            refine ⟨89055685057998640904311565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59370456705332427269541043 89055685057998640904311565)
            ·
              refine ⟨33395881896749490339116837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89055685057998640904311565 33395881896749490339116837)
              ·
                refine ⟨6261727855640529438584407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33395881896749490339116837 6261727855640529438584407)
                ·
                  refine ⟨9392591783460794157876611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6261727855640529438584407 9392591783460794157876611)
                  ·
                    refine ⟨14088887675191191236814917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9392591783460794157876611 14088887675191191236814917)
                    ·
                      refine ⟨2641666439098348356902797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14088887675191191236814917 2641666439098348356902797)
                      ·
                        rfl

theorem cell23_5144627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 4].length) (baseStart_5144627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144627 prefixEnd_5144627 := by exact prefixLift 5144627
  have htrace : WordTrace (prefixWord ++ tailWord_5144627) baseStart_5144627 baseEnd_5144627 := by
    simpa [prefixWord, tailWord_5144627, baseEnd_5144627] using wordTrace_append hprefix tailTrace_5144627
  have hstable : (prefixWord ++ tailWord_5144627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144627).length < 2 ^ (prefixWord ++ tailWord_5144627).sum := by decide
  have hdescent : baseEnd_5144627 < baseStart_5144627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144637 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_5144637 : Nat := 118140960795 + 5144637 * 2 ^ 59
def prefixEnd_5144637 : Nat := 4983230072969 + 3 ^ 40 * 5144637 * 2
def baseEnd_5144637 : Nat := 880557191301631105925917

theorem tailTrace_5144637 : CollatzResearch.WordTrace tailWord_5144637 prefixEnd_5144637 880557191301631105925917 := by
  unfold tailWord_5144637
  simp only [CollatzResearch.WordTrace]
  refine ⟨187640326662866257893080165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125093551108577505262053443 187640326662866257893080165)
  ·
    refine ⟨35182561249287423354952531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187640326662866257893080165 35182561249287423354952531)
    ·
      refine ⟨52773841873931135032428797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35182561249287423354952531 52773841873931135032428797)
      ·
        refine ⟨19790190702724175637160799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52773841873931135032428797 19790190702724175637160799)
        ·
          refine ⟨29685286054086263455741199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19790190702724175637160799 29685286054086263455741199)
          ·
            refine ⟨44527929081129395183611799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29685286054086263455741199 44527929081129395183611799)
            ·
              refine ⟨66791893621694092775417699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44527929081129395183611799 66791893621694092775417699)
              ·
                refine ⟨100187840432541139163126549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66791893621694092775417699 100187840432541139163126549)
                ·
                  refine ⟨4696305020275365898271557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100187840432541139163126549 4696305020275365898271557)
                  ·
                    refine ⟨880557191301631105925917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4696305020275365898271557 880557191301631105925917)
                    ·
                      rfl

theorem cell23_5144637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_5144637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144637 prefixEnd_5144637 := by exact prefixLift 5144637
  have htrace : WordTrace (prefixWord ++ tailWord_5144637) baseStart_5144637 baseEnd_5144637 := by
    simpa [prefixWord, tailWord_5144637, baseEnd_5144637] using wordTrace_append hprefix tailTrace_5144637
  have hstable : (prefixWord ++ tailWord_5144637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144637).length < 2 ^ (prefixWord ++ tailWord_5144637).sum := by decide
  have hdescent : baseEnd_5144637 < baseStart_5144637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144647 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_5144647 : Nat := 118140960795 + 5144647 * 2 ^ 59
def prefixEnd_5144647 : Nat := 4983230072969 + 3 ^ 40 * 5144647 * 2
def baseEnd_5144647 : Nat := 2641676708711438278652705

theorem tailTrace_5144647 : CollatzResearch.WordTrace tailWord_5144647 prefixEnd_5144647 2641676708711438278652705 := by
  unfold tailWord_5144647
  simp only [CollatzResearch.WordTrace]
  refine ⟨187640691392830029600944195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125093794261886686400629463 187640691392830029600944195)
  ·
    refine ⟨281461037089245044401416293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187640691392830029600944195 281461037089245044401416293)
    ·
      refine ⟨52773944454233445825265555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281461037089245044401416293 52773944454233445825265555)
      ·
        refine ⟨79160916681350168737898333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52773944454233445825265555 79160916681350168737898333)
        ·
          refine ⟨29685343755506313276711875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79160916681350168737898333 29685343755506313276711875)
          ·
            refine ⟨44528015633259469915067813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29685343755506313276711875 44528015633259469915067813)
            ·
              refine ⟨8349002931236150609075215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44528015633259469915067813 8349002931236150609075215)
              ·
                refine ⟨12523504396854225913612823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8349002931236150609075215 12523504396854225913612823)
                ·
                  refine ⟨18785256595281338870419235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12523504396854225913612823 18785256595281338870419235)
                  ·
                    refine ⟨28177884892922008305628853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18785256595281338870419235 28177884892922008305628853)
                    ·
                      refine ⟨2641676708711438278652705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28177884892922008305628853 2641676708711438278652705)
                      ·
                        rfl

theorem cell23_5144647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_5144647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144647 prefixEnd_5144647 := by exact prefixLift 5144647
  have htrace : WordTrace (prefixWord ++ tailWord_5144647) baseStart_5144647 baseEnd_5144647 := by
    simpa [prefixWord, tailWord_5144647, baseEnd_5144647] using wordTrace_append hprefix tailTrace_5144647
  have hstable : (prefixWord ++ tailWord_5144647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144647).length < 2 ^ (prefixWord ++ tailWord_5144647).sum := by decide
  have hdescent : baseEnd_5144647 < baseStart_5144647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144661 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_5144661 : Nat := 118140960795 + 5144661 * 2 ^ 59
def prefixEnd_5144661 : Nat := 4983230072969 + 3 ^ 40 * 5144661 * 2
def baseEnd_5144661 : Nat := 2641683897440601223877641

theorem tailTrace_5144661 : CollatzResearch.WordTrace tailWord_5144661 prefixEnd_5144661 2641683897440601223877641 := by
  unfold tailWord_5144661
  simp only [CollatzResearch.WordTrace]
  refine ⟨187641202014779309991953837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125094134676519539994635891 187641202014779309991953837)
  ·
    refine ⟨70365450755542241246982689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187641202014779309991953837 70365450755542241246982689)
    ·
      refine ⟨52774088066656680935237017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70365450755542241246982689 52774088066656680935237017)
      ·
        refine ⟨39580566049992510701427763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52774088066656680935237017 39580566049992510701427763)
        ·
          refine ⟨59370849074988766052141645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39580566049992510701427763 59370849074988766052141645)
          ·
            refine ⟨22264068403120787269553117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59370849074988766052141645 22264068403120787269553117)
            ·
              refine ⟨8349025651170295226082419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22264068403120787269553117 8349025651170295226082419)
              ·
                refine ⟨12523538476755442839123629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8349025651170295226082419 12523538476755442839123629)
                ·
                  refine ⟨4696326928783291064671361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12523538476755442839123629 4696326928783291064671361)
                  ·
                    refine ⟨3522245196587468298503521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4696326928783291064671361 3522245196587468298503521)
                    ·
                      refine ⟨2641683897440601223877641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3522245196587468298503521 2641683897440601223877641)
                      ·
                        rfl

theorem cell23_5144661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_5144661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144661 prefixEnd_5144661 := by exact prefixLift 5144661
  have htrace : WordTrace (prefixWord ++ tailWord_5144661) baseStart_5144661 baseEnd_5144661 := by
    simpa [prefixWord, tailWord_5144661, baseEnd_5144661] using wordTrace_append hprefix tailTrace_5144661
  have hstable : (prefixWord ++ tailWord_5144661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144661).length < 2 ^ (prefixWord ++ tailWord_5144661).sum := by decide
  have hdescent : baseEnd_5144661 < baseStart_5144661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144694 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_5144694 : Nat := 118140960795 + 5144694 * 2 ^ 59
def prefixEnd_5144694 : Nat := 4983230072969 + 3 ^ 40 * 5144694 * 2
def baseEnd_5144694 : Nat := 2641700842302199594764989

theorem tailTrace_5144694 : CollatzResearch.WordTrace tailWord_5144694 prefixEnd_5144694 2641700842302199594764989 := by
  unfold tailWord_5144694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11727650351478734789244071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125094937082439837751936757 11727650351478734789244071)
  ·
    refine ⟨17591475527218102183866107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11727650351478734789244071 17591475527218102183866107)
    ·
      refine ⟨26387213290827153275799161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17591475527218102183866107 26387213290827153275799161)
      ·
        refine ⟨19790409968120364956849371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26387213290827153275799161 19790409968120364956849371)
        ·
          refine ⟨29685614952180547435274057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19790409968120364956849371 29685614952180547435274057)
          ·
            refine ⟨22264211214135410576455543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29685614952180547435274057 22264211214135410576455543)
            ·
              refine ⟨33396316821203115864683315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22264211214135410576455543 33396316821203115864683315)
              ·
                refine ⟨50094475231804673797024973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33396316821203115864683315 50094475231804673797024973)
                ·
                  refine ⟨18785428211926752673884365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50094475231804673797024973 18785428211926752673884365)
                  ·
                    refine ⟨7044535579472532252706637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18785428211926752673884365 7044535579472532252706637)
                    ·
                      refine ⟨2641700842302199594764989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7044535579472532252706637 2641700842302199594764989)
                      ·
                        rfl

theorem cell23_5144694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_5144694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144694 prefixEnd_5144694 := by exact prefixLift 5144694
  have htrace : WordTrace (prefixWord ++ tailWord_5144694) baseStart_5144694 baseEnd_5144694 := by
    simpa [prefixWord, tailWord_5144694, baseEnd_5144694] using wordTrace_append hprefix tailTrace_5144694
  have hstable : (prefixWord ++ tailWord_5144694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144694).length < 2 ^ (prefixWord ++ tailWord_5144694).sum := by decide
  have hdescent : baseEnd_5144694 < baseStart_5144694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144712 : List Nat := [2, 1, 3, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_5144712 : Nat := 118140960795 + 5144712 * 2 ^ 59
def prefixEnd_5144712 : Nat := 4983230072969 + 3 ^ 40 * 5144712 * 2
def baseEnd_5144712 : Nat := 2641710084953980524339907

theorem tailTrace_5144712 : CollatzResearch.WordTrace tailWord_5144712 prefixEnd_5144712 2641710084953980524339907 := by
  unfold tailWord_5144712
  simp only [CollatzResearch.WordTrace]
  refine ⟨93821531068797272851030195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125095374758396363801373593 93821531068797272851030195)
  ·
    refine ⟨140732296603195909276545293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93821531068797272851030195 140732296603195909276545293)
    ·
      refine ⟨52774611226198465978704485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140732296603195909276545293 52774611226198465978704485)
      ·
        refine ⟨9895239604912212371007091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52774611226198465978704485 9895239604912212371007091)
        ·
          refine ⟨14842859407368318556510637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9895239604912212371007091 14842859407368318556510637)
          ·
            refine ⟨5566072277763119458691489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14842859407368318556510637 5566072277763119458691489)
            ·
              refine ⟨4174554208322339594018617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5566072277763119458691489 4174554208322339594018617)
              ·
                refine ⟨3130915656241754695513963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4174554208322339594018617 3130915656241754695513963)
                ·
                  refine ⟨4696373484362632043270945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130915656241754695513963 4696373484362632043270945)
                  ·
                    refine ⟨3522280113271974032453209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4696373484362632043270945 3522280113271974032453209)
                    ·
                      refine ⟨2641710084953980524339907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3522280113271974032453209 2641710084953980524339907)
                      ·
                        rfl

theorem cell23_5144712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_5144712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144712 prefixEnd_5144712 := by exact prefixLift 5144712
  have htrace : WordTrace (prefixWord ++ tailWord_5144712) baseStart_5144712 baseEnd_5144712 := by
    simpa [prefixWord, tailWord_5144712, baseEnd_5144712] using wordTrace_append hprefix tailTrace_5144712
  have hstable : (prefixWord ++ tailWord_5144712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144712).length < 2 ^ (prefixWord ++ tailWord_5144712).sum := by decide
  have hdescent : baseEnd_5144712 < baseStart_5144712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144768 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 2, 2, 2]
def baseStart_5144768 : Nat := 118140960795 + 5144768 * 2 ^ 59
def prefixEnd_5144768 : Nat := 4983230072969 + 3 ^ 40 * 5144768 * 2
def baseEnd_5144768 : Nat := 2641738839870632305239649

theorem tailTrace_5144768 : CollatzResearch.WordTrace tailWord_5144768 prefixEnd_5144768 2641738839870632305239649 := by
  unfold tailWord_5144768
  simp only [CollatzResearch.WordTrace]
  refine ⟨93822552312695833633049479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125096736416927778177399305 93822552312695833633049479)
  ·
    refine ⟨140733828469043750449574219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93822552312695833633049479 140733828469043750449574219)
    ·
      refine ⟨211100742703565625674361329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140733828469043750449574219 211100742703565625674361329)
      ·
        refine ⟨158325557027674219255770997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211100742703565625674361329 158325557027674219255770997)
        ·
          refine ⟨14843020971344458055228531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158325557027674219255770997 14843020971344458055228531)
          ·
            refine ⟨22264531457016687082842797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14843020971344458055228531 22264531457016687082842797)
            ·
              refine ⟨8349199296381257656066049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22264531457016687082842797 8349199296381257656066049)
              ·
                refine ⟨6261899472285943242049537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8349199296381257656066049 6261899472285943242049537)
                ·
                  refine ⟨4696424604214457431537153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6261899472285943242049537 4696424604214457431537153)
                  ·
                    refine ⟨3522318453160843073652865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4696424604214457431537153 3522318453160843073652865)
                    ·
                      refine ⟨2641738839870632305239649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3522318453160843073652865 2641738839870632305239649)
                      ·
                        rfl

theorem cell23_5144768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_5144768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144768 prefixEnd_5144768 := by exact prefixLift 5144768
  have htrace : WordTrace (prefixWord ++ tailWord_5144768) baseStart_5144768 baseEnd_5144768 := by
    simpa [prefixWord, tailWord_5144768, baseEnd_5144768] using wordTrace_append hprefix tailTrace_5144768
  have hstable : (prefixWord ++ tailWord_5144768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144768).length < 2 ^ (prefixWord ++ tailWord_5144768).sum := by decide
  have hdescent : baseEnd_5144768 < baseStart_5144768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144794 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2]
def baseStart_5144794 : Nat := 118140960795 + 5144794 * 2 ^ 59
def prefixEnd_5144794 : Nat := 4983230072969 + 3 ^ 40 * 5144794 * 2
def baseEnd_5144794 : Nat := 2641752190367649203514529

theorem tailTrace_5144794 : CollatzResearch.WordTrace tailWord_5144794 prefixEnd_5144794 2641752190367649203514529 := by
  unfold tailWord_5144794
  simp only [CollatzResearch.WordTrace]
  refine ⟨46911513230824368426636359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125097368615531649137696957 46911513230824368426636359)
  ·
    refine ⟨70367269846236552639954539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46911513230824368426636359 70367269846236552639954539)
    ·
      refine ⟨105550904769354828959931809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70367269846236552639954539 105550904769354828959931809)
      ·
        refine ⟨79163178577016121719948857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105550904769354828959931809 79163178577016121719948857)
        ·
          refine ⟨59372383932762091289961643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79163178577016121719948857 59372383932762091289961643)
          ·
            refine ⟨89058575899143136934942465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59372383932762091289961643 89058575899143136934942465)
            ·
              refine ⟨66793931924357352701206849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89058575899143136934942465 66793931924357352701206849)
              ·
                refine ⟨50095448943268014525905137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66793931924357352701206849 50095448943268014525905137)
                ·
                  refine ⟨37571586707451010894428853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50095448943268014525905137 37571586707451010894428853)
                  ·
                    refine ⟨3522336253823532271352705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37571586707451010894428853 3522336253823532271352705)
                    ·
                      refine ⟨2641752190367649203514529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3522336253823532271352705 2641752190367649203514529)
                      ·
                        rfl

theorem cell23_5144794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_5144794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144794 prefixEnd_5144794 := by exact prefixLift 5144794
  have htrace : WordTrace (prefixWord ++ tailWord_5144794) baseStart_5144794 baseEnd_5144794 := by
    simpa [prefixWord, tailWord_5144794, baseEnd_5144794] using wordTrace_append hprefix tailTrace_5144794
  have hstable : (prefixWord ++ tailWord_5144794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144794).length < 2 ^ (prefixWord ++ tailWord_5144794).sum := by decide
  have hdescent : baseEnd_5144794 < baseStart_5144794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144824 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 4, 4, 2]
def baseStart_5144824 : Nat := 118140960795 + 5144824 * 2 ^ 59
def prefixEnd_5144824 : Nat := 4983230072969 + 3 ^ 40 * 5144824 * 2
def baseEnd_5144824 : Nat := 2641767594787284086139391

theorem tailTrace_5144824 : CollatzResearch.WordTrace tailWord_5144824 prefixEnd_5144824 2641767594787284086139391 := by
  unfold tailWord_5144824
  simp only [CollatzResearch.WordTrace]
  refine ⟨93823573556594394415068763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125098098075459192553425017 93823573556594394415068763)
  ·
    refine ⟨140735360334891591622603145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93823573556594394415068763 140735360334891591622603145)
    ·
      refine ⟨105551520251168693716952359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140735360334891591622603145 105551520251168693716952359)
      ·
        refine ⟨158327280376753040575428539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105551520251168693716952359 158327280376753040575428539)
        ·
          refine ⟨237490920565129560863142809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158327280376753040575428539 237490920565129560863142809)
          ·
            refine ⟨178118190423847170647357107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237490920565129560863142809 178118190423847170647357107)
            ·
              refine ⟨267177285635770755971035661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178118190423847170647357107 267177285635770755971035661)
              ·
                refine ⟨100191482113414033489138373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267177285635770755971035661 100191482113414033489138373)
                ·
                  refine ⟨18785902896265131279213445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100191482113414033489138373 18785902896265131279213445)
                  ·
                    refine ⟨3522356793049712114852521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18785902896265131279213445 3522356793049712114852521)
                    ·
                      refine ⟨2641767594787284086139391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3522356793049712114852521 2641767594787284086139391)
                      ·
                        rfl

theorem cell23_5144824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_5144824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144824 prefixEnd_5144824 := by exact prefixLift 5144824
  have htrace : WordTrace (prefixWord ++ tailWord_5144824) baseStart_5144824 baseEnd_5144824 := by
    simpa [prefixWord, tailWord_5144824, baseEnd_5144824] using wordTrace_append hprefix tailTrace_5144824
  have hstable : (prefixWord ++ tailWord_5144824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144824).length < 2 ^ (prefixWord ++ tailWord_5144824).sum := by decide
  have hdescent : baseEnd_5144824 < baseStart_5144824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144827 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 3]
def baseStart_5144827 : Nat := 118140960795 + 5144827 * 2 ^ 59
def prefixEnd_5144827 : Nat := 4983230072969 + 3 ^ 40 * 5144827 * 2
def baseEnd_5144827 : Nat := 2641769135229247574401877

theorem tailTrace_5144827 : CollatzResearch.WordTrace tailWord_5144827 prefixEnd_5144827 2641769135229247574401877 := by
  unfold tailWord_5144827
  simp only [CollatzResearch.WordTrace]
  refine ⟨187647256532177920342496735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125098171021451946894997823 187647256532177920342496735)
  ·
    refine ⟨281470884798266880513745103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187647256532177920342496735 281470884798266880513745103)
    ·
      refine ⟨422206327197400320770617655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281470884798266880513745103 422206327197400320770617655)
      ·
        refine ⟨633309490796100481155926483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422206327197400320770617655 633309490796100481155926483)
        ·
          refine ⟨949964236194150721733889725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633309490796100481155926483 949964236194150721733889725)
          ·
            refine ⟨356236588572806520650208647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 949964236194150721733889725 356236588572806520650208647)
            ·
              refine ⟨534354882859209780975312971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356236588572806520650208647 534354882859209780975312971)
              ·
                refine ⟨801532324288814671462969457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534354882859209780975312971 801532324288814671462969457)
                ·
                  refine ⟨601149243216611003597227093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 801532324288814671462969457 601149243216611003597227093)
                  ·
                    refine ⟨7044717693944660198405005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 601149243216611003597227093 7044717693944660198405005)
                    ·
                      refine ⟨2641769135229247574401877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7044717693944660198405005 2641769135229247574401877)
                      ·
                        rfl

theorem cell23_5144827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 3].length) (baseStart_5144827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144827 prefixEnd_5144827 := by exact prefixLift 5144827
  have htrace : WordTrace (prefixWord ++ tailWord_5144827) baseStart_5144827 baseEnd_5144827 := by
    simpa [prefixWord, tailWord_5144827, baseEnd_5144827] using wordTrace_append hprefix tailTrace_5144827
  have hstable : (prefixWord ++ tailWord_5144827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144827).length < 2 ^ (prefixWord ++ tailWord_5144827).sum := by decide
  have hdescent : baseEnd_5144827 < baseStart_5144827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144837 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_5144837 : Nat := 118140960795 + 5144837 * 2 ^ 59
def prefixEnd_5144837 : Nat := 4983230072969 + 3 ^ 40 * 5144837 * 2
def baseEnd_5144837 : Nat := 2641774270035792535276831

theorem tailTrace_5144837 : CollatzResearch.WordTrace tailWord_5144837 prefixEnd_5144837 2641774270035792535276831 := by
  unfold tailWord_5144837
  simp only [CollatzResearch.WordTrace]
  refine ⟨187647621262141692050360765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125098414174761128033573843 187647621262141692050360765)
  ·
    refine ⟨70367857973303134518885287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187647621262141692050360765 70367857973303134518885287)
    ·
      refine ⟨105551786959954701778327931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70367857973303134518885287 105551786959954701778327931)
      ·
        refine ⟨158327680439932052667491897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105551786959954701778327931 158327680439932052667491897)
        ·
          refine ⟨118745760329949039500618923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158327680439932052667491897 118745760329949039500618923)
          ·
            refine ⟨178118640494923559250928385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118745760329949039500618923 178118640494923559250928385)
            ·
              refine ⟨133588980371192669438196289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178118640494923559250928385 133588980371192669438196289)
              ·
                refine ⟨100191735278394502078647217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133588980371192669438196289 100191735278394502078647217)
                ·
                  refine ⟨75143801458795876558985413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100191735278394502078647217 75143801458795876558985413)
                  ·
                    refine ⟨14089462773524226854809765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75143801458795876558985413 14089462773524226854809765)
                    ·
                      refine ⟨2641774270035792535276831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14089462773524226854809765 2641774270035792535276831)
                      ·
                        rfl

theorem cell23_5144837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_5144837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144837 prefixEnd_5144837 := by exact prefixLift 5144837
  have htrace : WordTrace (prefixWord ++ tailWord_5144837) baseStart_5144837 baseEnd_5144837 := by
    simpa [prefixWord, tailWord_5144837, baseEnd_5144837] using wordTrace_append hprefix tailTrace_5144837
  have hstable : (prefixWord ++ tailWord_5144837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144837).length < 2 ^ (prefixWord ++ tailWord_5144837).sum := by decide
  have hdescent : baseEnd_5144837 < baseStart_5144837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144844 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_5144844 : Nat := 118140960795 + 5144844 * 2 ^ 59
def prefixEnd_5144844 : Nat := 4983230072969 + 3 ^ 40 * 5144844 * 2
def baseEnd_5144844 : Nat := 2641777864400374007889299

theorem tailTrace_5144844 : CollatzResearch.WordTrace tailWord_5144844 prefixEnd_5144844 2641777864400374007889299 := by
  unfold tailWord_5144844
  simp only [CollatzResearch.WordTrace]
  refine ⟨93823938286558166122932793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125098584382077554830577057 93823938286558166122932793)
  ·
    refine ⟨70367953714918624592199595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93823938286558166122932793 70367953714918624592199595)
    ·
      refine ⟨105551930572377936888299393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70367953714918624592199595 105551930572377936888299393)
      ·
        refine ⟨79163947929283452666224545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105551930572377936888299393 79163947929283452666224545)
        ·
          refine ⟨59372960946962589499668409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79163947929283452666224545 59372960946962589499668409)
          ·
            refine ⟨44529720710221942124751307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59372960946962589499668409 44529720710221942124751307)
            ·
              refine ⟨66794581065332913187126961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44529720710221942124751307 66794581065332913187126961)
              ·
                refine ⟨50095935798999684890345221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66794581065332913187126961 50095935798999684890345221)
                ·
                  refine ⟨9392987962312440916939729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50095935798999684890345221 9392987962312440916939729)
                  ·
                    refine ⟨7044740971734330687704797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9392987962312440916939729 7044740971734330687704797)
                    ·
                      refine ⟨2641777864400374007889299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7044740971734330687704797 2641777864400374007889299)
                      ·
                        rfl

theorem cell23_5144844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_5144844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144844 prefixEnd_5144844 := by exact prefixLift 5144844
  have htrace : WordTrace (prefixWord ++ tailWord_5144844) baseStart_5144844 baseEnd_5144844 := by
    simpa [prefixWord, tailWord_5144844, baseEnd_5144844] using wordTrace_append hprefix tailTrace_5144844
  have hstable : (prefixWord ++ tailWord_5144844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144844).length < 2 ^ (prefixWord ++ tailWord_5144844).sum := by decide
  have hdescent : baseEnd_5144844 < baseStart_5144844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144881 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 6]
def baseStart_5144881 : Nat := 118140960795 + 5144881 * 2 ^ 59
def prefixEnd_5144881 : Nat := 4983230072969 + 3 ^ 40 * 5144881 * 2
def baseEnd_5144881 : Nat := 293532984798287818125181

theorem tailTrace_5144881 : CollatzResearch.WordTrace tailWord_5144881 prefixEnd_5144881 293532984798287818125181 := by
  unfold tailWord_5144881
  simp only [CollatzResearch.WordTrace]
  refine ⟨187649226073982287564962497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125099484049321525043308331 187649226073982287564962497)
  ·
    refine ⟨140736919555486715673721873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187649226073982287564962497 140736919555486715673721873)
    ·
      refine ⟨105552689666615036755291405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140736919555486715673721873 105552689666615036755291405)
      ·
        refine ⟨39582258624980638783234277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105552689666615036755291405 39582258624980638783234277)
        ·
          refine ⟨7421673492183869771856427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39582258624980638783234277 7421673492183869771856427)
          ·
            refine ⟨11132510238275804657784641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7421673492183869771856427 11132510238275804657784641)
            ·
              refine ⟨8349382678706853493338481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11132510238275804657784641 8349382678706853493338481)
              ·
                refine ⟨6262037009030140120003861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8349382678706853493338481 6262037009030140120003861)
                ·
                  refine ⟨293532984798287818125181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6262037009030140120003861 293532984798287818125181)
                  ·
                    rfl

theorem cell23_5144881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 6].length) (baseStart_5144881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144881 prefixEnd_5144881 := by exact prefixLift 5144881
  have htrace : WordTrace (prefixWord ++ tailWord_5144881) baseStart_5144881 baseEnd_5144881 := by
    simpa [prefixWord, tailWord_5144881, baseEnd_5144881] using wordTrace_append hprefix tailTrace_5144881
  have hstable : (prefixWord ++ tailWord_5144881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144881).length < 2 ^ (prefixWord ++ tailWord_5144881).sum := by decide
  have hdescent : baseEnd_5144881 < baseStart_5144881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144887 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_5144887 : Nat := 118140960795 + 5144887 * 2 ^ 59
def prefixEnd_5144887 : Nat := 4983230072969 + 3 ^ 40 * 5144887 * 2
def baseEnd_5144887 : Nat := 2641799944068517339651601

theorem tailTrace_5144887 : CollatzResearch.WordTrace tailWord_5144887 prefixEnd_5144887 2641799944068517339651601 := by
  unfold tailWord_5144887
  simp only [CollatzResearch.WordTrace]
  refine ⟨187649444911960550589680915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125099629941307033726453943 187649444911960550589680915)
  ·
    refine ⟨281474167367940825884521373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187649444911960550589680915 281474167367940825884521373)
    ·
      refine ⟨105552812762977809706695515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281474167367940825884521373 105552812762977809706695515)
      ·
        refine ⟨158329219144466714560043273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105552812762977809706695515 158329219144466714560043273)
        ·
          refine ⟨118746914358350035920032455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158329219144466714560043273 118746914358350035920032455)
          ·
            refine ⟨178120371537525053880048683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118746914358350035920032455 178120371537525053880048683)
            ·
              refine ⟨267180557306287580820073025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178120371537525053880048683 267180557306287580820073025)
              ·
                refine ⟨200385417979715685615054769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267180557306287580820073025 200385417979715685615054769)
                ·
                  refine ⟨150289063484786764211291077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200385417979715685615054769 150289063484786764211291077)
                  ·
                    refine ⟨28179199403397518289617077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150289063484786764211291077 28179199403397518289617077)
                    ·
                      refine ⟨2641799944068517339651601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28179199403397518289617077 2641799944068517339651601)
                      ·
                        rfl

theorem cell23_5144887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_5144887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144887 prefixEnd_5144887 := by exact prefixLift 5144887
  have htrace : WordTrace (prefixWord ++ tailWord_5144887) baseStart_5144887 baseEnd_5144887 := by
    simpa [prefixWord, tailWord_5144887, baseEnd_5144887] using wordTrace_append hprefix tailTrace_5144887
  have hstable : (prefixWord ++ tailWord_5144887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144887).length < 2 ^ (prefixWord ++ tailWord_5144887).sum := by decide
  have hdescent : baseEnd_5144887 < baseStart_5144887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144931 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 4]
def baseStart_5144931 : Nat := 118140960795 + 5144931 * 2 ^ 59
def prefixEnd_5144931 : Nat := 4983230072969 + 3 ^ 40 * 5144931 * 2
def baseEnd_5144931 : Nat := 2641822537217315167501399

theorem tailTrace_5144931 : CollatzResearch.WordTrace tailWord_5144931 prefixEnd_5144931 2641822537217315167501399 := by
  unfold tailWord_5144931
  simp only [CollatzResearch.WordTrace]
  refine ⟨187651049723801146104282647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125100699815867430736188431 187651049723801146104282647)
  ·
    refine ⟨281476574585701719156423971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187651049723801146104282647 281476574585701719156423971)
    ·
      refine ⟨422214861878552578734635957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281476574585701719156423971 422214861878552578734635957)
      ·
        refine ⟨39582643301114304256372121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 422214861878552578734635957 39582643301114304256372121)
        ·
          refine ⟨29686982475835728192279091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39582643301114304256372121 29686982475835728192279091)
          ·
            refine ⟨44530473713753592288418637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29686982475835728192279091 44530473713753592288418637)
            ·
              refine ⟨16698927642657597108156989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44530473713753592288418637 16698927642657597108156989)
              ·
                refine ⟨6262097865996598915558871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16698927642657597108156989 6262097865996598915558871)
                ·
                  refine ⟨9393146798994898373338307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6262097865996598915558871 9393146798994898373338307)
                  ·
                    refine ⟨14089720198492347560007461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9393146798994898373338307 14089720198492347560007461)
                    ·
                      refine ⟨2641822537217315167501399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14089720198492347560007461 2641822537217315167501399)
                      ·
                        rfl

theorem cell23_5144931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_5144931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144931 prefixEnd_5144931 := by exact prefixLift 5144931
  have htrace : WordTrace (prefixWord ++ tailWord_5144931) baseStart_5144931 baseEnd_5144931 := by
    simpa [prefixWord, tailWord_5144931, baseEnd_5144931] using wordTrace_append hprefix tailTrace_5144931
  have hstable : (prefixWord ++ tailWord_5144931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144931).length < 2 ^ (prefixWord ++ tailWord_5144931).sum := by decide
  have hdescent : baseEnd_5144931 < baseStart_5144931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144937 : List Nat := [1, 2, 1, 1, 1, 3, 14]
def baseStart_5144937 : Nat := 118140960795 + 5144937 * 2 ^ 59
def prefixEnd_5144937 : Nat := 4983230072969 + 3 ^ 40 * 5144937 * 2
def baseEnd_5144937 : Nat := 32615131087669656099091

theorem tailTrace_5144937 : CollatzResearch.WordTrace tailWord_5144937 prefixEnd_5144937 32615131087669656099091 := by
  unfold tailWord_5144937
  simp only [CollatzResearch.WordTrace]
  refine ⟨187651268561779409129001065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125100845707852939419334043 187651268561779409129001065)
  ·
    refine ⟨140738451421334556846750799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187651268561779409129001065 140738451421334556846750799)
    ·
      refine ⟨211107677132001835270126199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140738451421334556846750799 211107677132001835270126199)
      ·
        refine ⟨316661515698002752905189299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211107677132001835270126199 316661515698002752905189299)
        ·
          refine ⟨474992273547004129357783949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316661515698002752905189299 474992273547004129357783949)
          ·
            refine ⟨178122102580126548509168981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474992273547004129357783949 178122102580126548509168981)
            ·
              refine ⟨32615131087669656099091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 178122102580126548509168981 32615131087669656099091)
              ·
                rfl

theorem cell23_5144937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 14].length) (baseStart_5144937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144937 prefixEnd_5144937 := by exact prefixLift 5144937
  have htrace : WordTrace (prefixWord ++ tailWord_5144937) baseStart_5144937 baseEnd_5144937 := by
    simpa [prefixWord, tailWord_5144937, baseEnd_5144937] using wordTrace_append hprefix tailTrace_5144937
  have hstable : (prefixWord ++ tailWord_5144937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144937).length < 2 ^ (prefixWord ++ tailWord_5144937).sum := by decide
  have hdescent : baseEnd_5144937 < baseStart_5144937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144941 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_5144941 : Nat := 118140960795 + 5144941 * 2 ^ 59
def prefixEnd_5144941 : Nat := 4983230072969 + 3 ^ 40 * 5144941 * 2
def baseEnd_5144941 : Nat := 880609224007953376125451

theorem tailTrace_5144941 : CollatzResearch.WordTrace tailWord_5144941 prefixEnd_5144941 880609224007953376125451 := by
  unfold tailWord_5144941
  simp only [CollatzResearch.WordTrace]
  refine ⟨187651414453764917812146677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125100942969176611874764451 187651414453764917812146677)
  ·
    refine ⟨17592320105040461044888751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187651414453764917812146677 17592320105040461044888751)
    ·
      refine ⟨26388480157560691567333127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17592320105040461044888751 26388480157560691567333127)
      ·
        refine ⟨39582720236341037350999691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26388480157560691567333127 39582720236341037350999691)
        ·
          refine ⟨59374080354511556026499537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39582720236341037350999691 59374080354511556026499537)
          ·
            refine ⟨44530560265883667019874653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59374080354511556026499537 44530560265883667019874653)
            ·
              refine ⟨16698960099706375132452995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44530560265883667019874653 16698960099706375132452995)
              ·
                refine ⟨25048440149559562698679493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16698960099706375132452995 25048440149559562698679493)
                ·
                  refine ⟨4696582528042418006002405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25048440149559562698679493 4696582528042418006002405)
                  ·
                    refine ⟨880609224007953376125451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4696582528042418006002405 880609224007953376125451)
                    ·
                      rfl

theorem cell23_5144941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_5144941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144941 prefixEnd_5144941 := by exact prefixLift 5144941
  have htrace : WordTrace (prefixWord ++ tailWord_5144941) baseStart_5144941 baseEnd_5144941 := by
    simpa [prefixWord, tailWord_5144941, baseEnd_5144941] using wordTrace_append hprefix tailTrace_5144941
  have hstable : (prefixWord ++ tailWord_5144941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144941).length < 2 ^ (prefixWord ++ tailWord_5144941).sum := by decide
  have hdescent : baseEnd_5144941 < baseStart_5144941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144961 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5144961 : Nat := 118140960795 + 5144961 * 2 ^ 59
def prefixEnd_5144961 : Nat := 4983230072969 + 3 ^ 40 * 5144961 * 2
def baseEnd_5144961 : Nat := 2641837941636950050126261

theorem tailTrace_5144961 : CollatzResearch.WordTrace tailWord_5144961 prefixEnd_5144961 2641837941636950050126261 := by
  unfold tailWord_5144961
  simp only [CollatzResearch.WordTrace]
  refine ⟨187652143913692461227874737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125101429275794974151916491 187652143913692461227874737)
  ·
    refine ⟨140739107935269345920906053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187652143913692461227874737 140739107935269345920906053)
    ·
      refine ⟨26388582737863002360169885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140739107935269345920906053 26388582737863002360169885)
      ·
        refine ⟨9895718526698625885063707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26388582737863002360169885 9895718526698625885063707)
        ·
          refine ⟨14843577790047938827595561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9895718526698625885063707 14843577790047938827595561)
          ·
            refine ⟨11132683342535954120696671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14843577790047938827595561 11132683342535954120696671)
            ·
              refine ⟨16699025013803931181045007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11132683342535954120696671 16699025013803931181045007)
              ·
                refine ⟨25048537520705896771567511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16699025013803931181045007 25048537520705896771567511)
                ·
                  refine ⟨37572806281058845157351267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25048537520705896771567511 37572806281058845157351267)
                  ·
                    refine ⟨56359209421588267736026901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37572806281058845157351267 56359209421588267736026901)
                    ·
                      refine ⟨2641837941636950050126261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56359209421588267736026901 2641837941636950050126261)
                      ·
                        rfl

theorem cell23_5144961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5144961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144961 prefixEnd_5144961 := by exact prefixLift 5144961
  have htrace : WordTrace (prefixWord ++ tailWord_5144961) baseStart_5144961 baseEnd_5144961 := by
    simpa [prefixWord, tailWord_5144961, baseEnd_5144961] using wordTrace_append hprefix tailTrace_5144961
  have hstable : (prefixWord ++ tailWord_5144961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144961).length < 2 ^ (prefixWord ++ tailWord_5144961).sum := by decide
  have hdescent : baseEnd_5144961 < baseStart_5144961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144968 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_5144968 : Nat := 118140960795 + 5144968 * 2 ^ 59
def prefixEnd_5144968 : Nat := 4983230072969 + 3 ^ 40 * 5144968 * 2
def baseEnd_5144968 : Nat := 2641841536001531522738729

theorem tailTrace_5144968 : CollatzResearch.WordTrace tailWord_5144968 prefixEnd_5144968 2641841536001531522738729 := by
  unfold tailWord_5144968
  simp only [CollatzResearch.WordTrace]
  refine ⟨93826199612333550711689779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125101599483111400948919705 93826199612333550711689779)
  ·
    refine ⟨140739299418500326067534669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93826199612333550711689779 140739299418500326067534669)
    ·
      refine ⟨52777237281937622275325501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140739299418500326067534669 52777237281937622275325501)
      ·
        refine ⟨19791463980726608353247063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52777237281937622275325501 19791463980726608353247063)
        ·
          refine ⟨29687195971089912529870595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19791463980726608353247063 29687195971089912529870595)
          ·
            refine ⟨44530793956634868794805893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29687195971089912529870595 44530793956634868794805893)
            ·
              refine ⟨8349523866869037899026105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44530793956634868794805893 8349523866869037899026105)
              ·
                refine ⟨6262142900151778424269579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8349523866869037899026105 6262142900151778424269579)
                ·
                  refine ⟨9393214350227667636404369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6262142900151778424269579 9393214350227667636404369)
                  ·
                    refine ⟨7044910762670750727303277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9393214350227667636404369 7044910762670750727303277)
                    ·
                      refine ⟨2641841536001531522738729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7044910762670750727303277 2641841536001531522738729)
                      ·
                        rfl

theorem cell23_5144968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_5144968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144968 prefixEnd_5144968 := by exact prefixLift 5144968
  have htrace : WordTrace (prefixWord ++ tailWord_5144968) baseStart_5144968 baseEnd_5144968 := by
    simpa [prefixWord, tailWord_5144968, baseEnd_5144968] using wordTrace_append hprefix tailTrace_5144968
  have hstable : (prefixWord ++ tailWord_5144968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144968).length < 2 ^ (prefixWord ++ tailWord_5144968).sum := by decide
  have hdescent : baseEnd_5144968 < baseStart_5144968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144971 : List Nat := [1, 1, 1, 1, 4, 6, 2, 7]
def baseStart_5144971 : Nat := 118140960795 + 5144971 * 2 ^ 59
def prefixEnd_5144971 : Nat := 4983230072969 + 3 ^ 40 * 5144971 * 2
def baseEnd_5144971 : Nat := 97846039868277593000045

theorem tailTrace_5144971 : CollatzResearch.WordTrace tailWord_5144971 prefixEnd_5144971 97846039868277593000045 := by
  unfold tailWord_5144971
  simp only [CollatzResearch.WordTrace]
  refine ⟨187652508643656232935738767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125101672429104155290492511 187652508643656232935738767)
  ·
    refine ⟨281478762965484349403608151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187652508643656232935738767 281478762965484349403608151)
    ·
      refine ⟨422218144448226524105412227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281478762965484349403608151 422218144448226524105412227)
      ·
        refine ⟨633327216672339786158118341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422218144448226524105412227 633327216672339786158118341)
        ·
          refine ⟨118748853126063709904647189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 633327216672339786158118341 118748853126063709904647189)
          ·
            refine ⟨5566352490284236401780337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118748853126063709904647189 5566352490284236401780337)
            ·
              refine ⟨4174764367713177301335253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5566352490284236401780337 4174764367713177301335253)
              ·
                refine ⟨97846039868277593000045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4174764367713177301335253 97846039868277593000045)
                ·
                  rfl

theorem cell23_5144971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 7].length) (baseStart_5144971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144971 prefixEnd_5144971 := by exact prefixLift 5144971
  have htrace : WordTrace (prefixWord ++ tailWord_5144971) baseStart_5144971 baseEnd_5144971 := by
    simpa [prefixWord, tailWord_5144971, baseEnd_5144971] using wordTrace_append hprefix tailTrace_5144971
  have hstable : (prefixWord ++ tailWord_5144971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144971).length < 2 ^ (prefixWord ++ tailWord_5144971).sum := by decide
  have hdescent : baseEnd_5144971 < baseStart_5144971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5144999 : List Nat := [1, 1, 6, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_5144999 : Nat := 118140960795 + 5144999 * 2 ^ 59
def prefixEnd_5144999 : Nat := 4983230072969 + 3 ^ 40 * 5144999 * 2
def baseEnd_5144999 : Nat := 2641857453901820901451087

theorem tailTrace_5144999 : CollatzResearch.WordTrace tailWord_5144999 prefixEnd_5144999 2641857453901820901451087 := by
  unfold tailWord_5144999
  simp only [CollatzResearch.WordTrace]
  refine ⟨187653529887554793717758051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125102353258369862478505367 187653529887554793717758051)
  ·
    refine ⟨281480294831332190576637077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187653529887554793717758051 281480294831332190576637077)
    ·
      refine ⟨13194388820218696433279863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 281480294831332190576637077 13194388820218696433279863)
      ·
        refine ⟨19791583230328044649919795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13194388820218696433279863 19791583230328044649919795)
        ·
          refine ⟨29687374845492066974879693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19791583230328044649919795 29687374845492066974879693)
          ·
            refine ⟨11132765567059525115579885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29687374845492066974879693 11132765567059525115579885)
            ·
              refine ⟨4174787087647321918342457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11132765567059525115579885 4174787087647321918342457)
              ·
                refine ⟨3131090315735491438756843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4174787087647321918342457 3131090315735491438756843)
                ·
                  refine ⟨4696635473603237158135265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131090315735491438756843 4696635473603237158135265)
                  ·
                    refine ⟨3522476605202427868601449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4696635473603237158135265 3522476605202427868601449)
                    ·
                      refine ⟨2641857453901820901451087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3522476605202427868601449 2641857453901820901451087)
                      ·
                        rfl

theorem cell23_5144999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_5144999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5144999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5144999 prefixEnd_5144999 := by exact prefixLift 5144999
  have htrace : WordTrace (prefixWord ++ tailWord_5144999) baseStart_5144999 baseEnd_5144999 := by
    simpa [prefixWord, tailWord_5144999, baseEnd_5144999] using wordTrace_append hprefix tailTrace_5144999
  have hstable : (prefixWord ++ tailWord_5144999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5144999).length < 2 ^ (prefixWord ++ tailWord_5144999).sum := by decide
  have hdescent : baseEnd_5144999 < baseStart_5144999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5144999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145004 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_5145004 : Nat := 118140960795 + 5145004 * 2 ^ 59
def prefixEnd_5145004 : Nat := 4983230072969 + 3 ^ 40 * 5145004 * 2
def baseEnd_5145004 : Nat := 2641860021305093381888563

theorem tailTrace_5145004 : CollatzResearch.WordTrace tailWord_5145004 prefixEnd_5145004 2641860021305093381888563 := by
  unfold tailWord_5145004
  simp only [CollatzResearch.WordTrace]
  refine ⟨93826856126268339785845033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125102474835024453047793377 93826856126268339785845033)
  ·
    refine ⟨70370142094701254839383775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93826856126268339785845033 70370142094701254839383775)
    ·
      refine ⟨105555213142051882259075663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70370142094701254839383775 105555213142051882259075663)
      ·
        refine ⟨158332819713077823388613495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105555213142051882259075663 158332819713077823388613495)
        ·
          refine ⟨237499229569616735082920243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158332819713077823388613495 237499229569616735082920243)
          ·
            refine ⟨356248844354425102624380365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237499229569616735082920243 356248844354425102624380365)
            ·
              refine ⟨133593316632909413484142637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356248844354425102624380365 133593316632909413484142637)
              ·
                refine ⟨50097493737341030056553489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133593316632909413484142637 50097493737341030056553489)
                ·
                  refine ⟨37573120303005772542415117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50097493737341030056553489 37573120303005772542415117)
                  ·
                    refine ⟨14089920113627164703405669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37573120303005772542415117 14089920113627164703405669)
                    ·
                      refine ⟨2641860021305093381888563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14089920113627164703405669 2641860021305093381888563)
                      ·
                        rfl

theorem cell23_5145004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_5145004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145004 prefixEnd_5145004 := by exact prefixLift 5145004
  have htrace : WordTrace (prefixWord ++ tailWord_5145004) baseStart_5145004 baseEnd_5145004 := by
    simpa [prefixWord, tailWord_5145004, baseEnd_5145004] using wordTrace_append hprefix tailTrace_5145004
  have hstable : (prefixWord ++ tailWord_5145004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145004).length < 2 ^ (prefixWord ++ tailWord_5145004).sum := by decide
  have hdescent : baseEnd_5145004 < baseStart_5145004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145015 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 2, 1, 3]
def baseStart_5145015 : Nat := 118140960795 + 5145015 * 2 ^ 59
def prefixEnd_5145015 : Nat := 4983230072969 + 3 ^ 40 * 5145015 * 2
def baseEnd_5145015 : Nat := 2641865669592292838851013

theorem tailTrace_5145015 : CollatzResearch.WordTrace tailWord_5145015 prefixEnd_5145015 2641865669592292838851013 := by
  unfold tailWord_5145015
  simp only [CollatzResearch.WordTrace]
  refine ⟨187654113455496828450340499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125102742303664552300226999 187654113455496828450340499)
  ·
    refine ⟨281481170183245242675510749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187654113455496828450340499 281481170183245242675510749)
    ·
      refine ⟨105555438818716966003316531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281481170183245242675510749 105555438818716966003316531)
      ·
        refine ⟨158333158228075449004974797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105555438818716966003316531 158333158228075449004974797)
        ·
          refine ⟨59374934335528293376865549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158333158228075449004974797 59374934335528293376865549)
          ·
            refine ⟨22265600375823110016324581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59374934335528293376865549 22265600375823110016324581)
            ·
              refine ⟨4174800070466833128060859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22265600375823110016324581 4174800070466833128060859)
              ·
                refine ⟨6262200105700249692091289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4174800070466833128060859 6262200105700249692091289)
                ·
                  refine ⟨4696650079275187269068467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6262200105700249692091289 4696650079275187269068467)
                  ·
                    refine ⟨7044975118912780903602701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4696650079275187269068467 7044975118912780903602701)
                    ·
                      refine ⟨2641865669592292838851013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7044975118912780903602701 2641865669592292838851013)
                      ·
                        rfl

theorem cell23_5145015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_5145015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145015 prefixEnd_5145015 := by exact prefixLift 5145015
  have htrace : WordTrace (prefixWord ++ tailWord_5145015) baseStart_5145015 baseEnd_5145015 := by
    simpa [prefixWord, tailWord_5145015, baseEnd_5145015] using wordTrace_append hprefix tailTrace_5145015
  have hstable : (prefixWord ++ tailWord_5145015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145015).length < 2 ^ (prefixWord ++ tailWord_5145015).sum := by decide
  have hdescent : baseEnd_5145015 < baseStart_5145015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145055 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 2, 2, 2]
def baseStart_5145055 : Nat := 118140960795 + 5145055 * 2 ^ 59
def prefixEnd_5145055 : Nat := 4983230072969 + 3 ^ 40 * 5145055 * 2
def baseEnd_5145055 : Nat := 2641886208818472682350829

theorem tailTrace_5145055 : CollatzResearch.WordTrace tailWord_5145055 prefixEnd_5145055 2641886208818472682350829 := by
  unfold tailWord_5145055
  simp only [CollatzResearch.WordTrace]
  refine ⟨187655572375351915281796619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125103714916901276854531079 187655572375351915281796619)
  ·
    refine ⟨281483358563027872922694929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187655572375351915281796619 281483358563027872922694929)
    ·
      refine ⟨211112518922270904692021197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281483358563027872922694929 211112518922270904692021197)
      ·
        refine ⟨79167194595851589259507949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211112518922270904692021197 79167194595851589259507949)
        ·
          refine ⟨29687697973444345972315481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79167194595851589259507949 29687697973444345972315481)
          ·
            refine ⟨22265773480083259479236611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29687697973444345972315481 22265773480083259479236611)
            ·
              refine ⟨33398660220124889218854917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22265773480083259479236611 33398660220124889218854917)
              ·
                refine ⟨6262248791273416728535297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33398660220124889218854917 6262248791273416728535297)
                ·
                  refine ⟨4696686593455062546401473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6262248791273416728535297 4696686593455062546401473)
                  ·
                    refine ⟨3522514945091296909801105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4696686593455062546401473 3522514945091296909801105)
                    ·
                      refine ⟨2641886208818472682350829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3522514945091296909801105 2641886208818472682350829)
                      ·
                        rfl

theorem cell23_5145055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_5145055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145055 prefixEnd_5145055 := by exact prefixLift 5145055
  have htrace : WordTrace (prefixWord ++ tailWord_5145055) baseStart_5145055 baseEnd_5145055 := by
    simpa [prefixWord, tailWord_5145055, baseEnd_5145055] using wordTrace_append hprefix tailTrace_5145055
  have hstable : (prefixWord ++ tailWord_5145055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145055).length < 2 ^ (prefixWord ++ tailWord_5145055).sum := by decide
  have hdescent : baseEnd_5145055 < baseStart_5145055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145095 : List Nat := [1, 1, 4, 3, 3, 1, 2, 3, 5]
def baseStart_5145095 : Nat := 118140960795 + 5145095 * 2 ^ 59
def prefixEnd_5145095 : Nat := 4983230072969 + 3 ^ 40 * 5145095 * 2
def baseEnd_5145095 : Nat := 293545194227183613983405

theorem tailTrace_5145095 : CollatzResearch.WordTrace tailWord_5145095 prefixEnd_5145095 293545194227183613983405 := by
  unfold tailWord_5145095
  simp only [CollatzResearch.WordTrace]
  refine ⟨187657031295207002113252739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125104687530138001408835159 187657031295207002113252739)
  ·
    refine ⟨281485546942810503169879109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187657031295207002113252739 281485546942810503169879109)
    ·
      refine ⟨52778540051776969344352333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281485546942810503169879109 52778540051776969344352333)
      ·
        refine ⟨19791952519416363504132125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52778540051776969344352333 19791952519416363504132125)
        ·
          refine ⟨7421982194781136314049547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19791952519416363504132125 7421982194781136314049547)
          ·
            refine ⟨11132973292171704471074321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7421982194781136314049547 11132973292171704471074321)
            ·
              refine ⟨8349729969128778353305741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11132973292171704471074321 8349729969128778353305741)
              ·
                refine ⟨3131148738423291882489653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8349729969128778353305741 3131148738423291882489653)
                ·
                  refine ⟨293545194227183613983405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3131148738423291882489653 293545194227183613983405)
                  ·
                    rfl

theorem cell23_5145095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 5].length) (baseStart_5145095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145095 prefixEnd_5145095 := by exact prefixLift 5145095
  have htrace : WordTrace (prefixWord ++ tailWord_5145095) baseStart_5145095 baseEnd_5145095 := by
    simpa [prefixWord, tailWord_5145095, baseEnd_5145095] using wordTrace_append hprefix tailTrace_5145095
  have hstable : (prefixWord ++ tailWord_5145095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145095).length < 2 ^ (prefixWord ++ tailWord_5145095).sum := by decide
  have hdescent : baseEnd_5145095 < baseStart_5145095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145128 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5145128 : Nat := 118140960795 + 5145128 * 2 ^ 59
def prefixEnd_5145128 : Nat := 4983230072969 + 3 ^ 40 * 5145128 * 2
def baseEnd_5145128 : Nat := 2641923692906250896737993

theorem tailTrace_5145128 : CollatzResearch.WordTrace tailWord_5145128 prefixEnd_5145128 2641923692906250896737993 := by
  unfold tailWord_5145128
  simp only [CollatzResearch.WordTrace]
  refine ⟨93829117452043724374602019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125105489936058299166136025 93829117452043724374602019)
  ·
    refine ⟨140743676178065586561903029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93829117452043724374602019 140743676178065586561903029)
    ·
      refine ⟨13194719641693648740178409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140743676178065586561903029 13194719641693648740178409)
      ·
        refine ⟨9896039731270236555133807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13194719641693648740178409 9896039731270236555133807)
        ·
          refine ⟨14844059596905354832700711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9896039731270236555133807 14844059596905354832700711)
          ·
            refine ⟨22266089395358032249051067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14844059596905354832700711 22266089395358032249051067)
            ·
              refine ⟨33399134093037048373576601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22266089395358032249051067 33399134093037048373576601)
              ·
                refine ⟨25049350569777786280182451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33399134093037048373576601 25049350569777786280182451)
                ·
                  refine ⟨37574025854666679420273677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25049350569777786280182451 37574025854666679420273677)
                  ·
                    refine ⟨14090259695500004782602629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37574025854666679420273677 14090259695500004782602629)
                    ·
                      refine ⟨2641923692906250896737993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14090259695500004782602629 2641923692906250896737993)
                      ·
                        rfl

theorem cell23_5145128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5145128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145128 prefixEnd_5145128 := by exact prefixLift 5145128
  have htrace : WordTrace (prefixWord ++ tailWord_5145128) baseStart_5145128 baseEnd_5145128 := by
    simpa [prefixWord, tailWord_5145128, baseEnd_5145128] using wordTrace_append hprefix tailTrace_5145128
  have hstable : (prefixWord ++ tailWord_5145128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145128).length < 2 ^ (prefixWord ++ tailWord_5145128).sum := by decide
  have hdescent : baseEnd_5145128 < baseStart_5145128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145138 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_5145138 : Nat := 118140960795 + 5145138 * 2 ^ 59
def prefixEnd_5145138 : Nat := 4983230072969 + 3 ^ 40 * 5145138 * 2
def baseEnd_5145138 : Nat := 880642942570931952537649

theorem tailTrace_5145138 : CollatzResearch.WordTrace tailWord_5145138 prefixEnd_5145138 880642942570931952537649 := by
  unfold tailWord_5145138
  simp only [CollatzResearch.WordTrace]
  refine ⟨46914649908512805114267017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125105733089367480304712045 46914649908512805114267017)
  ·
    refine ⟨35185987431384603835700263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46914649908512805114267017 35185987431384603835700263)
    ·
      refine ⟨52778981147076905753550395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35185987431384603835700263 52778981147076905753550395)
      ·
        refine ⟨79168471720615358630325593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52778981147076905753550395 79168471720615358630325593)
        ·
          refine ⟨59376353790461518972744195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79168471720615358630325593 59376353790461518972744195)
          ·
            refine ⟨89064530685692278459116293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59376353790461518972744195 89064530685692278459116293)
            ·
              refine ⟨16699599503567302211084305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89064530685692278459116293 16699599503567302211084305)
              ·
                refine ⟨12524699627675476658313229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16699599503567302211084305 12524699627675476658313229)
                ·
                  refine ⟨4696762360378303746867461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12524699627675476658313229 4696762360378303746867461)
                  ·
                    refine ⟨880642942570931952537649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4696762360378303746867461 880642942570931952537649)
                    ·
                      rfl

theorem cell23_5145138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_5145138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145138 prefixEnd_5145138 := by exact prefixLift 5145138
  have htrace : WordTrace (prefixWord ++ tailWord_5145138) baseStart_5145138 baseEnd_5145138 := by
    simpa [prefixWord, tailWord_5145138, baseEnd_5145138] using wordTrace_append hprefix tailTrace_5145138
  have hstable : (prefixWord ++ tailWord_5145138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145138).length < 2 ^ (prefixWord ++ tailWord_5145138).sum := by decide
  have hdescent : baseEnd_5145138 < baseStart_5145138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145141 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_5145141 : Nat := 118140960795 + 5145141 * 2 ^ 59
def prefixEnd_5145141 : Nat := 4983230072969 + 3 ^ 40 * 5145141 * 2
def baseEnd_5145141 : Nat := 2641930368154759345875433

theorem tailTrace_5145141 : CollatzResearch.WordTrace tailWord_5145141 prefixEnd_5145141 2641930368154759345875433 := by
  unfold tailWord_5145141
  simp only [CollatzResearch.WordTrace]
  refine ⟨187658709053040351969427277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125105806035360234646284851 187658709053040351969427277)
  ·
    refine ⟨70372015894890131988535229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187658709053040351969427277 70372015894890131988535229)
    ·
      refine ⟨26389505960583799495700711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70372015894890131988535229 26389505960583799495700711)
      ·
        refine ⟨39584258940875699243551067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26389505960583799495700711 39584258940875699243551067)
        ·
          refine ⟨59376388411313548865326601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39584258940875699243551067 59376388411313548865326601)
          ·
            refine ⟨44532291308485161648994951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59376388411313548865326601 44532291308485161648994951)
            ·
              refine ⟨66798436962727742473492427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44532291308485161648994951 66798436962727742473492427)
              ·
                refine ⟨100197655444091613710238641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66798436962727742473492427 100197655444091613710238641)
                ·
                  refine ⟨75148241583068710282678981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100197655444091613710238641 75148241583068710282678981)
                  ·
                    refine ⟨14090295296825383178002309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75148241583068710282678981 14090295296825383178002309)
                    ·
                      refine ⟨2641930368154759345875433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14090295296825383178002309 2641930368154759345875433)
                      ·
                        rfl

theorem cell23_5145141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_5145141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145141 prefixEnd_5145141 := by exact prefixLift 5145141
  have htrace : WordTrace (prefixWord ++ tailWord_5145141) baseStart_5145141 baseEnd_5145141 := by
    simpa [prefixWord, tailWord_5145141, baseEnd_5145141] using wordTrace_append hprefix tailTrace_5145141
  have hstable : (prefixWord ++ tailWord_5145141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145141).length < 2 ^ (prefixWord ++ tailWord_5145141).sum := by decide
  have hdescent : baseEnd_5145141 < baseStart_5145141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145148 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_5145148 : Nat := 118140960795 + 5145148 * 2 ^ 59
def prefixEnd_5145148 : Nat := 4983230072969 + 3 ^ 40 * 5145148 * 2
def baseEnd_5145148 : Nat := 2641933962519340818487901

theorem tailTrace_5145148 : CollatzResearch.WordTrace tailWord_5145148 prefixEnd_5145148 2641933962519340818487901 := by
  unfold tailWord_5145148
  simp only [CollatzResearch.WordTrace]
  refine ⟨93829482182007496082466049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125105976242676661443288065 93829482182007496082466049)
  ·
    refine ⟨70372111636505622061849537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93829482182007496082466049 70372111636505622061849537)
    ·
      refine ⟨52779083727379216546387153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70372111636505622061849537 52779083727379216546387153)
      ·
        refine ⟨39584312795534412409790365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52779083727379216546387153 39584312795534412409790365)
        ·
          refine ⟨14844117298325404653671387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39584312795534412409790365 14844117298325404653671387)
          ·
            refine ⟨22266175947488106980507081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14844117298325404653671387 22266175947488106980507081)
            ·
              refine ⟨16699631960616080235380311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22266175947488106980507081 16699631960616080235380311)
              ·
                refine ⟨25049447940924120353070467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16699631960616080235380311 25049447940924120353070467)
                ·
                  refine ⟨37574171911386180529605701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25049447940924120353070467 37574171911386180529605701)
                  ·
                    refine ⟨7045157233384908849301069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37574171911386180529605701 7045157233384908849301069)
                    ·
                      refine ⟨2641933962519340818487901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7045157233384908849301069 2641933962519340818487901)
                      ·
                        rfl

theorem cell23_5145148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_5145148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145148 prefixEnd_5145148 := by exact prefixLift 5145148
  have htrace : WordTrace (prefixWord ++ tailWord_5145148) baseStart_5145148 baseEnd_5145148 := by
    simpa [prefixWord, tailWord_5145148, baseEnd_5145148] using wordTrace_append hprefix tailTrace_5145148
  have hstable : (prefixWord ++ tailWord_5145148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145148).length < 2 ^ (prefixWord ++ tailWord_5145148).sum := by decide
  have hdescent : baseEnd_5145148 < baseStart_5145148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145165 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_5145165 : Nat := 118140960795 + 5145165 * 2 ^ 59
def prefixEnd_5145165 : Nat := 4983230072969 + 3 ^ 40 * 5145165 * 2
def baseEnd_5145165 : Nat := 2641942691690467251975323

theorem tailTrace_5145165 : CollatzResearch.WordTrace tailWord_5145165 prefixEnd_5145165 2641942691690467251975323 := by
  unfold tailWord_5145165
  simp only [CollatzResearch.WordTrace]
  refine ⟨187659584404953404068300949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125106389603302269378867299 187659584404953404068300949)
  ·
    refine ⟨8796543018982190815701607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187659584404953404068300949 8796543018982190815701607)
    ·
      refine ⟨13194814528473286223552411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8796543018982190815701607 13194814528473286223552411)
      ·
        refine ⟨19792221792709929335328617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13194814528473286223552411 19792221792709929335328617)
        ·
          refine ⟨14844166344532447001496463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19792221792709929335328617 14844166344532447001496463)
          ·
            refine ⟨22266249516798670502244695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14844166344532447001496463 22266249516798670502244695)
            ·
              refine ⟨33399374275198005753367043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22266249516798670502244695 33399374275198005753367043)
              ·
                refine ⟨50099061412797008630050565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33399374275198005753367043 50099061412797008630050565)
                ·
                  refine ⟨9393574014899439118134481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50099061412797008630050565 9393574014899439118134481)
                  ·
                    refine ⟨7045180511174579338600861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9393574014899439118134481 7045180511174579338600861)
                    ·
                      refine ⟨2641942691690467251975323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7045180511174579338600861 2641942691690467251975323)
                      ·
                        rfl

theorem cell23_5145165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_5145165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145165 prefixEnd_5145165 := by exact prefixLift 5145165
  have htrace : WordTrace (prefixWord ++ tailWord_5145165) baseStart_5145165 baseEnd_5145165 := by
    simpa [prefixWord, tailWord_5145165, baseEnd_5145165] using wordTrace_append hprefix tailTrace_5145165
  have hstable : (prefixWord ++ tailWord_5145165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145165).length < 2 ^ (prefixWord ++ tailWord_5145165).sum := by decide
  have hdescent : baseEnd_5145165 < baseStart_5145165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145185 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 6]
def baseStart_5145185 : Nat := 118140960795 + 5145185 * 2 ^ 59
def prefixEnd_5145185 : Nat := 4983230072969 + 3 ^ 40 * 5145185 * 2
def baseEnd_5145185 : Nat := 293550329033728574858359

theorem tailTrace_5145185 : CollatzResearch.WordTrace tailWord_5145185 prefixEnd_5145185 293550329033728574858359 := by
  unfold tailWord_5145185
  simp only [CollatzResearch.WordTrace]
  refine ⟨187660313864880947484029009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125106875909920631656019339 187660313864880947484029009)
  ·
    refine ⟨140745235398660710613021757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187660313864880947484029009 140745235398660710613021757)
    ·
      refine ⟨52779463274497766479883159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140745235398660710613021757 52779463274497766479883159)
      ·
        refine ⟨79169194911746649719824739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52779463274497766479883159 79169194911746649719824739)
        ·
          refine ⟨118753792367619974579737109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79169194911746649719824739 118753792367619974579737109)
          ·
            refine ⟨5566584017232186308425177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118753792367619974579737109 5566584017232186308425177)
            ·
              refine ⟨4174938012924139731318883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5566584017232186308425177 4174938012924139731318883)
              ·
                refine ⟨6262407019386209596978325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4174938012924139731318883 6262407019386209596978325)
                ·
                  refine ⟨293550329033728574858359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6262407019386209596978325 293550329033728574858359)
                  ·
                    rfl

theorem cell23_5145185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 6].length) (baseStart_5145185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145185 prefixEnd_5145185 := by exact prefixLift 5145185
  have htrace : WordTrace (prefixWord ++ tailWord_5145185) baseStart_5145185 baseEnd_5145185 := by
    simpa [prefixWord, tailWord_5145185, baseEnd_5145185] using wordTrace_append hprefix tailTrace_5145185
  have hstable : (prefixWord ++ tailWord_5145185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145185).length < 2 ^ (prefixWord ++ tailWord_5145185).sum := by decide
  have hdescent : baseEnd_5145185 < baseStart_5145185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145245 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_5145245 : Nat := 118140960795 + 5145245 * 2 ^ 59
def prefixEnd_5145245 : Nat := 4983230072969 + 3 ^ 40 * 5145245 * 2
def baseEnd_5145245 : Nat := 880661256714275646324985

theorem tailTrace_5145245 : CollatzResearch.WordTrace tailWord_5145245 prefixEnd_5145245 880661256714275646324985 := by
  unfold tailWord_5145245
  simp only [CollatzResearch.WordTrace]
  refine ⟨187662502244663577731213189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125108334829775718487475459 187662502244663577731213189)
  ·
    refine ⟨35186719170874420824602473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187662502244663577731213189 35186719170874420824602473)
    ·
      refine ⟨26390039378155815618451855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35186719170874420824602473 26390039378155815618451855)
      ·
        refine ⟨39585059067233723427677783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26390039378155815618451855 39585059067233723427677783)
        ·
          refine ⟨59377588600850585141516675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39585059067233723427677783 59377588600850585141516675)
          ·
            refine ⟨89066382901275877712275013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59377588600850585141516675 89066382901275877712275013)
            ·
              refine ⟨16699946793989227071051565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89066382901275877712275013 16699946793989227071051565)
              ·
                refine ⟨6262480047745960151644337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16699946793989227071051565 6262480047745960151644337)
                ·
                  refine ⟨4696860035809470113733253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6262480047745960151644337 4696860035809470113733253)
                  ·
                    refine ⟨880661256714275646324985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4696860035809470113733253 880661256714275646324985)
                    ·
                      rfl

theorem cell23_5145245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_5145245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145245 prefixEnd_5145245 := by exact prefixLift 5145245
  have htrace : WordTrace (prefixWord ++ tailWord_5145245) baseStart_5145245 baseEnd_5145245 := by
    simpa [prefixWord, tailWord_5145245, baseEnd_5145245] using wordTrace_append hprefix tailTrace_5145245
  have hstable : (prefixWord ++ tailWord_5145245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145245).length < 2 ^ (prefixWord ++ tailWord_5145245).sum := by decide
  have hdescent : baseEnd_5145245 < baseStart_5145245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145252 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_5145252 : Nat := 118140960795 + 5145252 * 2 ^ 59
def prefixEnd_5145252 : Nat := 4983230072969 + 3 ^ 40 * 5145252 * 2
def baseEnd_5145252 : Nat := 2641987364507408411587423

theorem tailTrace_5145252 : CollatzResearch.WordTrace tailWord_5145252 prefixEnd_5145252 2641987364507408411587423 := by
  unfold tailWord_5145252
  simp only [CollatzResearch.WordTrace]
  refine ⟨93831378777819108963359005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125108505037092145284478673 93831378777819108963359005)
  ·
    refine ⟨35186767041682165861259627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93831378777819108963359005 35186767041682165861259627)
    ·
      refine ⟨52780150562523248791889441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35186767041682165861259627 52780150562523248791889441)
      ·
        refine ⟨39585112921892436593917081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52780150562523248791889441 39585112921892436593917081)
        ·
          refine ⟨29688834691419327445437811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39585112921892436593917081 29688834691419327445437811)
          ·
            refine ⟨44533252037128991168156717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29688834691419327445437811 44533252037128991168156717)
            ·
              refine ⟨16699969513923371688058769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44533252037128991168156717 16699969513923371688058769)
              ·
                refine ⟨12524977135442528766044077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16699969513923371688058769 12524977135442528766044077)
                ·
                  refine ⟨4696866425790948287266529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12524977135442528766044077 4696866425790948287266529)
                  ·
                    refine ⟨3522649819343211215449897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4696866425790948287266529 3522649819343211215449897)
                    ·
                      refine ⟨2641987364507408411587423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3522649819343211215449897 2641987364507408411587423)
                      ·
                        rfl

theorem cell23_5145252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_5145252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145252 prefixEnd_5145252 := by exact prefixLift 5145252
  have htrace : WordTrace (prefixWord ++ tailWord_5145252) baseStart_5145252 baseEnd_5145252 := by
    simpa [prefixWord, tailWord_5145252, baseEnd_5145252] using wordTrace_append hprefix tailTrace_5145252
  have hstable : (prefixWord ++ tailWord_5145252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145252).length < 2 ^ (prefixWord ++ tailWord_5145252).sum := by decide
  have hdescent : baseEnd_5145252 < baseStart_5145252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145269 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_5145269 : Nat := 118140960795 + 5145269 * 2 ^ 59
def prefixEnd_5145269 : Nat := 4983230072969 + 3 ^ 40 * 5145269 * 2
def baseEnd_5145269 : Nat := 2641996093678534845074845

theorem tailTrace_5145269 : CollatzResearch.WordTrace tailWord_5145269 prefixEnd_5145269 2641996093678534845074845 := by
  unfold tailWord_5145269
  simp only [CollatzResearch.WordTrace]
  refine ⟨187663377596576629830086861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125108918397717753220057907 187663377596576629830086861)
  ·
    refine ⟨70373766598716236186282573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187663377596576629830086861 70373766598716236186282573)
    ·
      refine ⟨26390162474518588569855965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70373766598716236186282573 26390162474518588569855965)
      ·
        refine ⟨9896310927944470713695987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26390162474518588569855965 9896310927944470713695987)
        ·
          refine ⟨14844466391916706070543981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9896310927944470713695987 14844466391916706070543981)
          ·
            refine ⟨5566674896968764776453993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14844466391916706070543981 5566674896968764776453993)
            ·
              refine ⟨4175006172726573582340495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5566674896968764776453993 4175006172726573582340495)
              ·
                refine ⟨6262509259089860373510743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4175006172726573582340495 6262509259089860373510743)
                ·
                  refine ⟨9393763888634790560266115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6262509259089860373510743 9393763888634790560266115)
                  ·
                    refine ⟨14090645832952185840399173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9393763888634790560266115 14090645832952185840399173)
                    ·
                      refine ⟨2641996093678534845074845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14090645832952185840399173 2641996093678534845074845)
                      ·
                        rfl

theorem cell23_5145269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_5145269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145269 prefixEnd_5145269 := by exact prefixLift 5145269
  have htrace : WordTrace (prefixWord ++ tailWord_5145269) baseStart_5145269 baseEnd_5145269 := by
    simpa [prefixWord, tailWord_5145269, baseEnd_5145269] using wordTrace_append hprefix tailTrace_5145269
  have hstable : (prefixWord ++ tailWord_5145269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145269).length < 2 ^ (prefixWord ++ tailWord_5145269).sum := by decide
  have hdescent : baseEnd_5145269 < baseStart_5145269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145328 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_5145328 : Nat := 118140960795 + 5145328 * 2 ^ 59
def prefixEnd_5145328 : Nat := 4983230072969 + 3 ^ 40 * 5145328 * 2
def baseEnd_5145328 : Nat := 2642026389037150114237073

theorem tailTrace_5145328 : CollatzResearch.WordTrace tailWord_5145328 prefixEnd_5145328 2642026389037150114237073 := by
  unfold tailWord_5145328
  simp only [CollatzResearch.WordTrace]
  refine ⟨93832764751681441453242319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125110353002241921937656425 93832764751681441453242319)
  ·
    refine ⟨140749147127522162179863479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93832764751681441453242319 140749147127522162179863479)
    ·
      refine ⟨211123720691283243269795219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140749147127522162179863479 211123720691283243269795219)
      ·
        refine ⟨316685581036924864904692829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211123720691283243269795219 316685581036924864904692829)
        ·
          refine ⟨118757092888846824339259811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316685581036924864904692829 118757092888846824339259811)
          ·
            refine ⟨178135639333270236508889717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118757092888846824339259811 178135639333270236508889717)
            ·
              refine ⟨16700216187494084672708411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178135639333270236508889717 16700216187494084672708411)
              ·
                refine ⟨25050324281241127009062617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16700216187494084672708411 25050324281241127009062617)
                ·
                  refine ⟨18787743210930845256796963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25050324281241127009062617 18787743210930845256796963)
                  ·
                    refine ⟨28181614816396267885195445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18787743210930845256796963 28181614816396267885195445)
                    ·
                      refine ⟨2642026389037150114237073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28181614816396267885195445 2642026389037150114237073)
                      ·
                        rfl

theorem cell23_5145328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_5145328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145328 prefixEnd_5145328 := by exact prefixLift 5145328
  have htrace : WordTrace (prefixWord ++ tailWord_5145328) baseStart_5145328 baseEnd_5145328 := by
    simpa [prefixWord, tailWord_5145328, baseEnd_5145328] using wordTrace_append hprefix tailTrace_5145328
  have hstable : (prefixWord ++ tailWord_5145328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145328).length < 2 ^ (prefixWord ++ tailWord_5145328).sum := by decide
  have hdescent : baseEnd_5145328 < baseStart_5145328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145338 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_5145338 : Nat := 118140960795 + 5145338 * 2 ^ 59
def prefixEnd_5145338 : Nat := 4983230072969 + 3 ^ 40 * 5145338 * 2
def baseEnd_5145338 : Nat := 2642031523843695075112027

theorem tailTrace_5145338 : CollatzResearch.WordTrace tailWord_5145338 prefixEnd_5145338 2642031523843695075112027 := by
  unfold tailWord_5145338
  simp only [CollatzResearch.WordTrace]
  refine ⟨46916473558331663653587167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125110596155551103076232445 46916473558331663653587167)
  ·
    refine ⟨70374710337497495480380751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46916473558331663653587167 70374710337497495480380751)
    ·
      refine ⟨105562065506246243220571127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70374710337497495480380751 105562065506246243220571127)
      ·
        refine ⟨158343098259369364830856691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105562065506246243220571127 158343098259369364830856691)
        ·
          refine ⟨237514647389054047246285037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158343098259369364830856691 237514647389054047246285037)
          ·
            refine ⟨89067992770895267717356889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237514647389054047246285037 89067992770895267717356889)
            ·
              refine ⟨66800994578171450788017667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89067992770895267717356889 66800994578171450788017667)
              ·
                refine ⟨100201491867257176182026501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66800994578171450788017667 100201491867257176182026501)
                ·
                  refine ⟨18787779725110720534129969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100201491867257176182026501 18787779725110720534129969)
                  ·
                    refine ⟨14090834793833040400597477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18787779725110720534129969 14090834793833040400597477)
                    ·
                      refine ⟨2642031523843695075112027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14090834793833040400597477 2642031523843695075112027)
                      ·
                        rfl

theorem cell23_5145338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_5145338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145338 prefixEnd_5145338 := by exact prefixLift 5145338
  have htrace : WordTrace (prefixWord ++ tailWord_5145338) baseStart_5145338 baseEnd_5145338 := by
    simpa [prefixWord, tailWord_5145338, baseEnd_5145338] using wordTrace_append hprefix tailTrace_5145338
  have hstable : (prefixWord ++ tailWord_5145338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145338).length < 2 ^ (prefixWord ++ tailWord_5145338).sum := by decide
  have hdescent : baseEnd_5145338 < baseStart_5145338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145388 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_5145388 : Nat := 118140960795 + 5145388 * 2 ^ 59
def prefixEnd_5145388 : Nat := 4983230072969 + 3 ^ 40 * 5145388 * 2
def baseEnd_5145388 : Nat := 2642057197876419879486797

theorem tailTrace_5145388 : CollatzResearch.WordTrace tailWord_5145388 prefixEnd_5145388 2642057197876419879486797 := by
  unfold tailWord_5145388
  simp only [CollatzResearch.WordTrace]
  refine ⟨93833858941572756576834409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125111811922097008769112545 93833858941572756576834409)
  ·
    refine ⟨70375394206179567432625807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93833858941572756576834409 70375394206179567432625807)
    ·
      refine ⟨105563091309269351148938711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70375394206179567432625807 105563091309269351148938711)
      ·
        refine ⟨158344636963904026723408067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105563091309269351148938711 158344636963904026723408067)
        ·
          refine ⟨237516955445856040085112101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158344636963904026723408067 237516955445856040085112101)
          ·
            refine ⟨44534429146098007515958519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237516955445856040085112101 44534429146098007515958519)
            ·
              refine ⟨66801643719147011273937779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44534429146098007515958519 66801643719147011273937779)
              ·
                refine ⟨100202465578720516910906669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66801643719147011273937779 100202465578720516910906669)
                ·
                  refine ⟨37575924592020193841590001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100202465578720516910906669 37575924592020193841590001)
                  ·
                    refine ⟨28181943444015145381192501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37575924592020193841590001 28181943444015145381192501)
                    ·
                      refine ⟨2642057197876419879486797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28181943444015145381192501 2642057197876419879486797)
                      ·
                        rfl

theorem cell23_5145388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_5145388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145388 prefixEnd_5145388 := by exact prefixLift 5145388
  have htrace : WordTrace (prefixWord ++ tailWord_5145388) baseStart_5145388 baseEnd_5145388 := by
    simpa [prefixWord, tailWord_5145388, baseEnd_5145388] using wordTrace_append hprefix tailTrace_5145388
  have hstable : (prefixWord ++ tailWord_5145388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145388).length < 2 ^ (prefixWord ++ tailWord_5145388).sum := by decide
  have hdescent : baseEnd_5145388 < baseStart_5145388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145395 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 2, 5]
def baseStart_5145395 : Nat := 118140960795 + 5145395 * 2 ^ 59
def prefixEnd_5145395 : Nat := 4983230072969 + 3 ^ 40 * 5145395 * 2
def baseEnd_5145395 : Nat := 880686930747000450699755

theorem tailTrace_5145395 : CollatzResearch.WordTrace tailWord_5145395 prefixEnd_5145395 880686930747000450699755 := by
  unfold tailWord_5145395
  simp only [CollatzResearch.WordTrace]
  refine ⟨187667973194120153349173639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125111982129413435566115759 187667973194120153349173639)
  ·
    refine ⟨281501959791180230023760459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187667973194120153349173639 281501959791180230023760459)
    ·
      refine ⟨422252939686770345035640689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281501959791180230023760459 422252939686770345035640689)
      ·
        refine ⟨316689704765077758776730517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422252939686770345035640689 316689704765077758776730517)
        ·
          refine ⟨14844829910863019942659243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 316689704765077758776730517 14844829910863019942659243)
          ·
            refine ⟨22267244866294529913988865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14844829910863019942659243 22267244866294529913988865)
            ·
              refine ⟨16700433649720897435491649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22267244866294529913988865 16700433649720897435491649)
              ·
                refine ⟨12525325237290673076618737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16700433649720897435491649 12525325237290673076618737)
                ·
                  refine ⟨9393993927968004807464053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12525325237290673076618737 9393993927968004807464053)
                  ·
                    refine ⟨880686930747000450699755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9393993927968004807464053 880686930747000450699755)
                    ·
                      rfl

theorem cell23_5145395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 5].length) (baseStart_5145395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145395 prefixEnd_5145395 := by exact prefixLift 5145395
  have htrace : WordTrace (prefixWord ++ tailWord_5145395) baseStart_5145395 baseEnd_5145395 := by
    simpa [prefixWord, tailWord_5145395, baseEnd_5145395] using wordTrace_append hprefix tailTrace_5145395
  have hstable : (prefixWord ++ tailWord_5145395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145395).length < 2 ^ (prefixWord ++ tailWord_5145395).sum := by decide
  have hdescent : baseEnd_5145395 < baseStart_5145395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145409 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5145409 : Nat := 118140960795 + 5145409 * 2 ^ 59
def prefixEnd_5145409 : Nat := 4983230072969 + 3 ^ 40 * 5145409 * 2
def baseEnd_5145409 : Nat := 2642067980970164297324201

theorem tailTrace_5145409 : CollatzResearch.WordTrace tailWord_5145409 prefixEnd_5145409 2642067980970164297324201 := by
  unfold tailWord_5145409
  simp only [CollatzResearch.WordTrace]
  refine ⟨187668483816069433740183281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125112322544046289160122187 187668483816069433740183281)
  ·
    refine ⟨140751362862052075305137461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187668483816069433740183281 140751362862052075305137461)
    ·
      refine ⟨13195440268317382059856637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140751362862052075305137461 13195440268317382059856637)
      ·
        refine ⟨4948290100619018272446239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13195440268317382059856637 4948290100619018272446239)
        ·
          refine ⟨7422435150928527408669359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4948290100619018272446239 7422435150928527408669359)
          ·
            refine ⟨11133652726392791113004039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7422435150928527408669359 11133652726392791113004039)
            ·
              refine ⟨16700479089589186669506059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11133652726392791113004039 16700479089589186669506059)
              ·
                refine ⟨25050718634383780004259089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16700479089589186669506059 25050718634383780004259089)
                ·
                  refine ⟨18788038975787835003194317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25050718634383780004259089 18788038975787835003194317)
                  ·
                    refine ⟨7045514615920438126197869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18788038975787835003194317 7045514615920438126197869)
                    ·
                      refine ⟨2642067980970164297324201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7045514615920438126197869 2642067980970164297324201)
                      ·
                        rfl

theorem cell23_5145409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5145409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145409 prefixEnd_5145409 := by exact prefixLift 5145409
  have htrace : WordTrace (prefixWord ++ tailWord_5145409) baseStart_5145409 baseEnd_5145409 := by
    simpa [prefixWord, tailWord_5145409, baseEnd_5145409] using wordTrace_append hprefix tailTrace_5145409
  have hstable : (prefixWord ++ tailWord_5145409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145409).length < 2 ^ (prefixWord ++ tailWord_5145409).sum := by decide
  have hdescent : baseEnd_5145409 < baseStart_5145409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145556 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5145556 : Nat := 118140960795 + 5145556 * 2 ^ 59
def prefixEnd_5145556 : Nat := 4983230072969 + 3 ^ 40 * 5145556 * 2
def baseEnd_5145556 : Nat := 2642143462626375222186025

theorem tailTrace_5145556 : CollatzResearch.WordTrace tailWord_5145556 prefixEnd_5145556 2642143462626375222186025 := by
  unfold tailWord_5145556
  simp only [CollatzResearch.WordTrace]
  refine ⟨93836922673268438922892261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125115896897691251897189681 93836922673268438922892261)
  ·
    refine ⟨17594423001237832298042299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93836922673268438922892261 17594423001237832298042299)
    ·
      refine ⟨26391634501856748447063449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17594423001237832298042299 26391634501856748447063449)
      ·
        refine ⟨19793725876392561335297587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26391634501856748447063449 19793725876392561335297587)
        ·
          refine ⟨29690588814588842002946381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19793725876392561335297587 29690588814588842002946381)
          ·
            refine ⟨11133970805470815751104893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29690588814588842002946381 11133970805470815751104893)
            ·
              refine ⟨4175239052051555906664335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11133970805470815751104893 4175239052051555906664335)
              ·
                refine ⟨6262858578077333859996503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4175239052051555906664335 6262858578077333859996503)
                ·
                  refine ⟨9394287867116000789994755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6262858578077333859996503 9394287867116000789994755)
                  ·
                    refine ⟨14091431800674001184992133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9394287867116000789994755 14091431800674001184992133)
                    ·
                      refine ⟨2642143462626375222186025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14091431800674001184992133 2642143462626375222186025)
                      ·
                        rfl

theorem cell23_5145556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5145556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145556 prefixEnd_5145556 := by exact prefixLift 5145556
  have htrace : WordTrace (prefixWord ++ tailWord_5145556) baseStart_5145556 baseEnd_5145556 := by
    simpa [prefixWord, tailWord_5145556, baseEnd_5145556] using wordTrace_append hprefix tailTrace_5145556
  have hstable : (prefixWord ++ tailWord_5145556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145556).length < 2 ^ (prefixWord ++ tailWord_5145556).sum := by decide
  have hdescent : baseEnd_5145556 < baseStart_5145556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145586 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5145586 : Nat := 118140960795 + 5145586 * 2 ^ 59
def prefixEnd_5145586 : Nat := 4983230072969 + 3 ^ 40 * 5145586 * 2
def baseEnd_5145586 : Nat := 2642158867046010104810887

theorem tailTrace_5145586 : CollatzResearch.WordTrace tailWord_5145586 prefixEnd_5145586 2642158867046010104810887 := by
  unfold tailWord_5145586
  simp only [CollatzResearch.WordTrace]
  refine ⟨46918734884107048242344153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125116626357618795312917741 46918734884107048242344153)
  ·
    refine ⟨35189051163080286181758115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46918734884107048242344153 35189051163080286181758115)
    ·
      refine ⟨52783576744620429272637173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35189051163080286181758115 52783576744620429272637173)
      ·
        refine ⟨4948460319808165244309735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52783576744620429272637173 4948460319808165244309735)
        ·
          refine ⟨7422690479712247866464603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4948460319808165244309735 7422690479712247866464603)
          ·
            refine ⟨11134035719568371799696905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7422690479712247866464603 11134035719568371799696905)
            ·
              refine ⟨8350526789676278849772679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11134035719568371799696905 8350526789676278849772679)
              ·
                refine ⟨12525790184514418274659019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8350526789676278849772679 12525790184514418274659019)
                ·
                  refine ⟨18788685276771627411988529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12525790184514418274659019 18788685276771627411988529)
                  ·
                    refine ⟨14091513957578720558991397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18788685276771627411988529 14091513957578720558991397)
                    ·
                      refine ⟨2642158867046010104810887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14091513957578720558991397 2642158867046010104810887)
                      ·
                        rfl

theorem cell23_5145586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5145586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145586 prefixEnd_5145586 := by exact prefixLift 5145586
  have htrace : WordTrace (prefixWord ++ tailWord_5145586) baseStart_5145586 baseEnd_5145586 := by
    simpa [prefixWord, tailWord_5145586, baseEnd_5145586] using wordTrace_append hprefix tailTrace_5145586
  have hstable : (prefixWord ++ tailWord_5145586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145586).length < 2 ^ (prefixWord ++ tailWord_5145586).sum := by decide
  have hdescent : baseEnd_5145586 < baseStart_5145586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145595 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 4]
def baseStart_5145595 : Nat := 118140960795 + 5145595 * 2 ^ 59
def prefixEnd_5145595 : Nat := 4983230072969 + 3 ^ 40 * 5145595 * 2
def baseEnd_5145595 : Nat := 2642163488371900569598345

theorem tailTrace_5145595 : CollatzResearch.WordTrace tailWord_5145595 prefixEnd_5145595 2642163488371900569598345 := by
  unfold tailWord_5145595
  simp only [CollatzResearch.WordTrace]
  refine ⟨187675267793395587506454239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125116845195597058337636159 187675267793395587506454239)
  ·
    refine ⟨281512901690093381259681359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187675267793395587506454239 281512901690093381259681359)
    ·
      refine ⟨422269352535140071889522039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281512901690093381259681359 422269352535140071889522039)
      ·
        refine ⟨633404028802710107834283059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422269352535140071889522039 633404028802710107834283059)
        ·
          refine ⟨950106043204065161751424589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633404028802710107834283059 950106043204065161751424589)
          ·
            refine ⟨356289766201524435656784221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 950106043204065161751424589 356289766201524435656784221)
            ·
              refine ⟨133608662325571663371294083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356289766201524435656784221 133608662325571663371294083)
              ·
                refine ⟨200412993488357495056941125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133608662325571663371294083 200412993488357495056941125)
                ·
                  refine ⟨37577436279067030323176461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200412993488357495056941125 37577436279067030323176461)
                  ·
                    refine ⟨14091538604650136371191173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37577436279067030323176461 14091538604650136371191173)
                    ·
                      refine ⟨2642163488371900569598345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14091538604650136371191173 2642163488371900569598345)
                      ·
                        rfl

theorem cell23_5145595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 4].length) (baseStart_5145595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145595 prefixEnd_5145595 := by exact prefixLift 5145595
  have htrace : WordTrace (prefixWord ++ tailWord_5145595) baseStart_5145595 baseEnd_5145595 := by
    simpa [prefixWord, tailWord_5145595, baseEnd_5145595] using wordTrace_append hprefix tailTrace_5145595
  have hstable : (prefixWord ++ tailWord_5145595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145595).length < 2 ^ (prefixWord ++ tailWord_5145595).sum := by decide
  have hdescent : baseEnd_5145595 < baseStart_5145595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145605 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_5145605 : Nat := 118140960795 + 5145605 * 2 ^ 59
def prefixEnd_5145605 : Nat := 4983230072969 + 3 ^ 40 * 5145605 * 2
def baseEnd_5145605 : Nat := 880722874392815176824433

theorem tailTrace_5145605 : CollatzResearch.WordTrace tailWord_5145605 prefixEnd_5145605 880722874392815176824433 := by
  unfold tailWord_5145605
  simp only [CollatzResearch.WordTrace]
  refine ⟨187675632523359359214318269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125117088348906239476212179 187675632523359359214318269)
  ·
    refine ⟨70378362196259759705369351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187675632523359359214318269 70378362196259759705369351)
    ·
      refine ⟨105567543294389639558054027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70378362196259759705369351 105567543294389639558054027)
      ·
        refine ⟨158351314941584459337081041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105567543294389639558054027 158351314941584459337081041)
        ·
          refine ⟨118763486206188344502810781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158351314941584459337081041 118763486206188344502810781)
          ·
            refine ⟨44536307327320629188554043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118763486206188344502810781 44536307327320629188554043)
            ·
              refine ⟨66804460990980943782831065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44536307327320629188554043 66804460990980943782831065)
              ·
                refine ⟨50103345743235707837123299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66804460990980943782831065 50103345743235707837123299)
                ·
                  refine ⟨75155018614853561755684949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50103345743235707837123299 75155018614853561755684949)
                  ·
                    refine ⟨880722874392815176824433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75155018614853561755684949 880722874392815176824433)
                    ·
                      rfl

theorem cell23_5145605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_5145605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145605 prefixEnd_5145605 := by exact prefixLift 5145605
  have htrace : WordTrace (prefixWord ++ tailWord_5145605) baseStart_5145605 baseEnd_5145605 := by
    simpa [prefixWord, tailWord_5145605, baseEnd_5145605] using wordTrace_append hprefix tailTrace_5145605
  have hstable : (prefixWord ++ tailWord_5145605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145605).length < 2 ^ (prefixWord ++ tailWord_5145605).sum := by decide
  have hdescent : baseEnd_5145605 < baseStart_5145605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145623 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5145623 : Nat := 118140960795 + 5145623 * 2 ^ 59
def prefixEnd_5145623 : Nat := 4983230072969 + 3 ^ 40 * 5145623 * 2
def baseEnd_5145623 : Nat := 2642177865830226460048217

theorem tailTrace_5145623 : CollatzResearch.WordTrace tailWord_5145623 prefixEnd_5145623 2642177865830226460048217 := by
  unfold tailWord_5145623
  simp only [CollatzResearch.WordTrace]
  refine ⟨187676289037294148288473523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125117526024862765525649015 187676289037294148288473523)
  ·
    refine ⟨281514433555941222432710285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187676289037294148288473523 281514433555941222432710285)
    ·
      refine ⟨105567912583477958412266357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281514433555941222432710285 105567912583477958412266357)
      ·
        refine ⟨9896991804701058601149971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105567912583477958412266357 9896991804701058601149971)
        ·
          refine ⟨14845487707051587901724957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9896991804701058601149971 14845487707051587901724957)
          ·
            refine ⟨5567057890144345463146859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14845487707051587901724957 5567057890144345463146859)
            ·
              refine ⟨8350586835216518194720289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567057890144345463146859 8350586835216518194720289)
              ·
                refine ⟨6262940126412388646040217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8350586835216518194720289 6262940126412388646040217)
                ·
                  refine ⟨4697205094809291484530163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6262940126412388646040217 4697205094809291484530163)
                  ·
                    refine ⟨7045807642213937226795245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4697205094809291484530163 7045807642213937226795245)
                    ·
                      refine ⟨2642177865830226460048217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7045807642213937226795245 2642177865830226460048217)
                      ·
                        rfl

theorem cell23_5145623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5145623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145623 prefixEnd_5145623 := by exact prefixLift 5145623
  have htrace : WordTrace (prefixWord ++ tailWord_5145623) baseStart_5145623 baseEnd_5145623 := by
    simpa [prefixWord, tailWord_5145623, baseEnd_5145623] using wordTrace_append hprefix tailTrace_5145623
  have hstable : (prefixWord ++ tailWord_5145623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145623).length < 2 ^ (prefixWord ++ tailWord_5145623).sum := by decide
  have hdescent : baseEnd_5145623 < baseStart_5145623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145639 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 2, 6]
def baseStart_5145639 : Nat := 118140960795 + 5145639 * 2 ^ 59
def prefixEnd_5145639 : Nat := 4983230072969 + 3 ^ 40 * 5145639 * 2
def baseEnd_5145639 : Nat := 880728693840232799149381

theorem tailTrace_5145639 : CollatzResearch.WordTrace tailWord_5145639 prefixEnd_5145639 880728693840232799149381 := by
  unfold tailWord_5145639
  simp only [CollatzResearch.WordTrace]
  refine ⟨187676872605236183021055971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125117915070157455347370647 187676872605236183021055971)
  ·
    refine ⟨281515308907854274531583957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187676872605236183021055971 281515308907854274531583957)
    ·
      refine ⟨6598015052527834559333999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 281515308907854274531583957 6598015052527834559333999)
      ·
        refine ⟨9897022578791751839000999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598015052527834559333999 9897022578791751839000999)
        ·
          refine ⟨14845533868187627758501499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9897022578791751839000999 14845533868187627758501499)
          ·
            refine ⟨22268300802281441637752249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14845533868187627758501499 22268300802281441637752249)
            ·
              refine ⟨16701225601711081228314187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22268300802281441637752249 16701225601711081228314187)
              ·
                refine ⟨25051838402566621842471281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16701225601711081228314187 25051838402566621842471281)
                ·
                  refine ⟨18788878801924966381853461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25051838402566621842471281 18788878801924966381853461)
                  ·
                    refine ⟨880728693840232799149381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18788878801924966381853461 880728693840232799149381)
                    ·
                      rfl

theorem cell23_5145639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_5145639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145639 prefixEnd_5145639 := by exact prefixLift 5145639
  have htrace : WordTrace (prefixWord ++ tailWord_5145639) baseStart_5145639 baseEnd_5145639 := by
    simpa [prefixWord, tailWord_5145639, baseEnd_5145639] using wordTrace_append hprefix tailTrace_5145639
  have hstable : (prefixWord ++ tailWord_5145639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145639).length < 2 ^ (prefixWord ++ tailWord_5145639).sum := by decide
  have hdescent : baseEnd_5145639 < baseStart_5145639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145669 : List Nat := [1, 3, 1, 1, 1, 3, 5, 3, 5]
def baseStart_5145669 : Nat := 118140960795 + 5145669 * 2 ^ 59
def prefixEnd_5145669 : Nat := 4983230072969 + 3 ^ 40 * 5145669 * 2
def baseEnd_5145669 : Nat := 293577942882259253341445

theorem tailTrace_5145669 : CollatzResearch.WordTrace tailWord_5145669 prefixEnd_5145669 293577942882259253341445 := by
  unfold tailWord_5145669
  simp only [CollatzResearch.WordTrace]
  refine ⟨187677966795127498144648061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125118644530084998763098707 187677966795127498144648061)
  ·
    refine ⟨70379237548172811804243023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187677966795127498144648061 70379237548172811804243023)
    ·
      refine ⟨105568856322259217706364535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70379237548172811804243023 105568856322259217706364535)
      ·
        refine ⟨158353284483388826559546803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105568856322259217706364535 158353284483388826559546803)
        ·
          refine ⟨237529926725083239839320205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158353284483388826559546803 237529926725083239839320205)
          ·
            refine ⟨89073722521906214939745077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237529926725083239839320205 89073722521906214939745077)
            ·
              refine ⟨8350661486428707650601101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89073722521906214939745077 8350661486428707650601101)
              ·
                refine ⟨3131498057410765368975413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8350661486428707650601101 3131498057410765368975413)
                ·
                  refine ⟨293577942882259253341445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3131498057410765368975413 293577942882259253341445)
                  ·
                    rfl

theorem cell23_5145669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_5145669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145669 prefixEnd_5145669 := by exact prefixLift 5145669
  have htrace : WordTrace (prefixWord ++ tailWord_5145669) baseStart_5145669 baseEnd_5145669 := by
    simpa [prefixWord, tailWord_5145669, baseEnd_5145669] using wordTrace_append hprefix tailTrace_5145669
  have hstable : (prefixWord ++ tailWord_5145669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145669).length < 2 ^ (prefixWord ++ tailWord_5145669).sum := by decide
  have hdescent : baseEnd_5145669 < baseStart_5145669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145719 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_5145719 : Nat := 118140960795 + 5145719 * 2 ^ 59
def prefixEnd_5145719 : Nat := 4983230072969 + 3 ^ 40 * 5145719 * 2
def baseEnd_5145719 : Nat := 2642227159973058084447775

theorem tailTrace_5145719 : CollatzResearch.WordTrace tailWord_5145719 prefixEnd_5145719 2642227159973058084447775 := by
  unfold tailWord_5145719
  simp only [CollatzResearch.WordTrace]
  refine ⟨187679790444946356683968211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125119860296630904455978807 187679790444946356683968211)
  ·
    refine ⟨281519685667419535025952317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187679790444946356683968211 281519685667419535025952317)
    ·
      refine ⟨105569882125282325634732119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281519685667419535025952317 105569882125282325634732119)
      ·
        refine ⟨158354823187923488452098179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105569882125282325634732119 158354823187923488452098179)
        ·
          refine ⟨237532234781885232678147269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158354823187923488452098179 237532234781885232678147269)
          ·
            refine ⟨44537294021603481127152613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237532234781885232678147269 44537294021603481127152613)
            ·
              refine ⟨8350742629050652711341115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44537294021603481127152613 8350742629050652711341115)
              ·
                refine ⟨12526113943575979067011673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8350742629050652711341115 12526113943575979067011673)
                ·
                  refine ⟨9394585457681984300258755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12526113943575979067011673 9394585457681984300258755)
                  ·
                    refine ⟨14091878186522976450388133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9394585457681984300258755 14091878186522976450388133)
                    ·
                      refine ⟨2642227159973058084447775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14091878186522976450388133 2642227159973058084447775)
                      ·
                        rfl

theorem cell23_5145719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_5145719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145719 prefixEnd_5145719 := by exact prefixLift 5145719
  have htrace : WordTrace (prefixWord ++ tailWord_5145719) baseStart_5145719 baseEnd_5145719 := by
    simpa [prefixWord, tailWord_5145719, baseEnd_5145719] using wordTrace_append hprefix tailTrace_5145719
  have hstable : (prefixWord ++ tailWord_5145719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145719).length < 2 ^ (prefixWord ++ tailWord_5145719).sum := by decide
  have hdescent : baseEnd_5145719 < baseStart_5145719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145793 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 6]
def baseStart_5145793 : Nat := 118140960795 + 5145793 * 2 ^ 59
def prefixEnd_5145793 : Nat := 4983230072969 + 3 ^ 40 * 5145793 * 2
def baseEnd_5145793 : Nat := 293585017504610088324715

theorem tailTrace_5145793 : CollatzResearch.WordTrace tailWord_5145793 prefixEnd_5145793 293585017504610088324715 := by
  unfold tailWord_5145793
  simp only [CollatzResearch.WordTrace]
  refine ⟨187682489446678267322162033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125121659631118844881441355 187682489446678267322162033)
  ·
    refine ⟨140761867085008700491621525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187682489446678267322162033 140761867085008700491621525)
    ·
      refine ⟨6598212519609782835544759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140761867085008700491621525 6598212519609782835544759)
      ·
        refine ⟨9897318779414674253317139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598212519609782835544759 9897318779414674253317139)
        ·
          refine ⟨14845978169122011379975709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9897318779414674253317139 14845978169122011379975709)
          ·
            refine ⟨5567241813420754267490891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14845978169122011379975709 5567241813420754267490891)
            ·
              refine ⟨8350862720131131401236337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567241813420754267490891 8350862720131131401236337)
              ·
                refine ⟨6263147040098348550927253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8350862720131131401236337 6263147040098348550927253)
                ·
                  refine ⟨293585017504610088324715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6263147040098348550927253 293585017504610088324715)
                  ·
                    rfl

theorem cell23_5145793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 6].length) (baseStart_5145793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145793 prefixEnd_5145793 := by exact prefixLift 5145793
  have htrace : WordTrace (prefixWord ++ tailWord_5145793) baseStart_5145793 baseEnd_5145793 := by
    simpa [prefixWord, tailWord_5145793, baseEnd_5145793] using wordTrace_append hprefix tailTrace_5145793
  have hstable : (prefixWord ++ tailWord_5145793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145793).length < 2 ^ (prefixWord ++ tailWord_5145793).sum := by decide
  have hdescent : baseEnd_5145793 < baseStart_5145793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145837 : List Nat := [1, 5, 1, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_5145837 : Nat := 118140960795 + 5145837 * 2 ^ 59
def prefixEnd_5145837 : Nat := 4983230072969 + 3 ^ 40 * 5145837 * 2
def baseEnd_5145837 : Nat := 2642287750690288622772233

theorem tailTrace_5145837 : CollatzResearch.WordTrace tailWord_5145837 prefixEnd_5145837 2642287750690288622772233 := by
  unfold tailWord_5145837
  simp only [CollatzResearch.WordTrace]
  refine ⟨187684094258518862836763765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125122729505679241891175843 187684094258518862836763765)
  ·
    refine ⟨17595383836736143390946603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187684094258518862836763765 17595383836736143390946603)
    ·
      refine ⟨26393075755104215086419905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17595383836736143390946603 26393075755104215086419905)
      ·
        refine ⟨19794806816328161314814929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26393075755104215086419905 19794806816328161314814929)
        ·
          refine ⟨14846105112246120986111197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19794806816328161314814929 14846105112246120986111197)
          ·
            refine ⟨5567289417092295369791699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14846105112246120986111197 5567289417092295369791699)
            ·
              refine ⟨8350934125638443054687549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567289417092295369791699 8350934125638443054687549)
              ·
                refine ⟨3131600297114416145507831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8350934125638443054687549 3131600297114416145507831)
                ·
                  refine ⟨4697400445671624218261747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131600297114416145507831 4697400445671624218261747)
                  ·
                    refine ⟨7046100668507436327392621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4697400445671624218261747 7046100668507436327392621)
                    ·
                      refine ⟨2642287750690288622772233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7046100668507436327392621 2642287750690288622772233)
                      ·
                        rfl

theorem cell23_5145837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_5145837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145837 prefixEnd_5145837 := by exact prefixLift 5145837
  have htrace : WordTrace (prefixWord ++ tailWord_5145837) baseStart_5145837 baseEnd_5145837 := by
    simpa [prefixWord, tailWord_5145837, baseEnd_5145837] using wordTrace_append hprefix tailTrace_5145837
  have hstable : (prefixWord ++ tailWord_5145837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145837).length < 2 ^ (prefixWord ++ tailWord_5145837).sum := by decide
  have hdescent : baseEnd_5145837 < baseStart_5145837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145846 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_5145846 : Nat := 118140960795 + 5145846 * 2 ^ 59
def prefixEnd_5145846 : Nat := 4983230072969 + 3 ^ 40 * 5145846 * 2
def baseEnd_5145846 : Nat := 2642292372016179087559691

theorem tailTrace_5145846 : CollatzResearch.WordTrace tailWord_5145846 prefixEnd_5145846 2642292372016179087559691 := by
  unfold tailWord_5145846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11730276407217891085865087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125122948343657504915894261 11730276407217891085865087)
  ·
    refine ⟨17595414610826836628797631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11730276407217891085865087 17595414610826836628797631)
    ·
      refine ⟨26393121916240254943196447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17595414610826836628797631 26393121916240254943196447)
      ·
        refine ⟨39589682874360382414794671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26393121916240254943196447 39589682874360382414794671)
        ·
          refine ⟨59384524311540573622192007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39589682874360382414794671 59384524311540573622192007)
          ·
            refine ⟨89076786467310860433288011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59384524311540573622192007 89076786467310860433288011)
            ·
              refine ⟨133615179700966290649932017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89076786467310860433288011 133615179700966290649932017)
              ·
                refine ⟨100211384775724717987449013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133615179700966290649932017 100211384775724717987449013)
                ·
                  refine ⟨9394817322724192311323345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100211384775724717987449013 9394817322724192311323345)
                  ·
                    refine ⟨7046112992043144233492509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9394817322724192311323345 7046112992043144233492509)
                    ·
                      refine ⟨2642292372016179087559691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7046112992043144233492509 2642292372016179087559691)
                      ·
                        rfl

theorem cell23_5145846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_5145846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145846 prefixEnd_5145846 := by exact prefixLift 5145846
  have htrace : WordTrace (prefixWord ++ tailWord_5145846) baseStart_5145846 baseEnd_5145846 := by
    simpa [prefixWord, tailWord_5145846, baseEnd_5145846] using wordTrace_append hprefix tailTrace_5145846
  have hstable : (prefixWord ++ tailWord_5145846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145846).length < 2 ^ (prefixWord ++ tailWord_5145846).sum := by decide
  have hdescent : baseEnd_5145846 < baseStart_5145846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145860 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_5145860 : Nat := 118140960795 + 5145860 * 2 ^ 59
def prefixEnd_5145860 : Nat := 4983230072969 + 3 ^ 40 * 5145860 * 2
def baseEnd_5145860 : Nat := 2642299560745342032784627

theorem tailTrace_5145860 : CollatzResearch.WordTrace tailWord_5145860 prefixEnd_5145860 2642299560745342032784627 := by
  unfold tailWord_5145860
  simp only [CollatzResearch.WordTrace]
  refine ⟨93842466568717768882425517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125123288758290358509900689 93842466568717768882425517)
  ·
    refine ⟨35190924963269163330909569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93842466568717768882425517 35190924963269163330909569)
    ·
      refine ⟨26393193722451872498182177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35190924963269163330909569 26393193722451872498182177)
      ·
        refine ⟨19794895291838904373636633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26393193722451872498182177 19794895291838904373636633)
        ·
          refine ⟨14846171468879178280227475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19794895291838904373636633 14846171468879178280227475)
          ·
            refine ⟨22269257203318767420341213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14846171468879178280227475 22269257203318767420341213)
            ·
              refine ⟨8350971451244537782627955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22269257203318767420341213 8350971451244537782627955)
              ·
                refine ⟨12526457176866806673941933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8350971451244537782627955 12526457176866806673941933)
                ·
                  refine ⟨4697421441325052502728225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12526457176866806673941933 4697421441325052502728225)
                  ·
                    refine ⟨3523066080993789377046169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4697421441325052502728225 3523066080993789377046169)
                    ·
                      refine ⟨2642299560745342032784627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523066080993789377046169 2642299560745342032784627)
                      ·
                        rfl

theorem cell23_5145860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_5145860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145860 prefixEnd_5145860 := by exact prefixLift 5145860
  have htrace : WordTrace (prefixWord ++ tailWord_5145860) baseStart_5145860 baseEnd_5145860 := by
    simpa [prefixWord, tailWord_5145860, baseEnd_5145860] using wordTrace_append hprefix tailTrace_5145860
  have hstable : (prefixWord ++ tailWord_5145860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145860).length < 2 ^ (prefixWord ++ tailWord_5145860).sum := by decide
  have hdescent : baseEnd_5145860 < baseStart_5145860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145870 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_5145870 : Nat := 118140960795 + 5145870 * 2 ^ 59
def prefixEnd_5145870 : Nat := 4983230072969 + 3 ^ 40 * 5145870 * 2
def baseEnd_5145870 : Nat := 880768231850628997886527

theorem tailTrace_5145870 : CollatzResearch.WordTrace tailWord_5145870 prefixEnd_5145870 880768231850628997886527 := by
  unfold tailWord_5145870
  simp only [CollatzResearch.WordTrace]
  refine ⟨23460662233424913684089383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125123531911599539648476709 23460662233424913684089383)
  ·
    refine ⟨35190993350137370526134075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23460662233424913684089383 35190993350137370526134075)
    ·
      refine ⟨52786490025206055789201113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35190993350137370526134075 52786490025206055789201113)
      ·
        refine ⟨39589867518904541841900835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52786490025206055789201113 39589867518904541841900835)
        ·
          refine ⟨59384801278356812762851253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39589867518904541841900835 59384801278356812762851253)
          ·
            refine ⟨5567325119845951196517305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59384801278356812762851253 5567325119845951196517305)
            ·
              refine ⟨4175493839884463397387979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5567325119845951196517305 4175493839884463397387979)
              ·
                refine ⟨6263240759826695096081969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4175493839884463397387979 6263240759826695096081969)
                ·
                  refine ⟨4697430569870021322061477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6263240759826695096081969 4697430569870021322061477)
                  ·
                    refine ⟨880768231850628997886527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4697430569870021322061477 880768231850628997886527)
                    ·
                      rfl

theorem cell23_5145870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_5145870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145870 prefixEnd_5145870 := by exact prefixLift 5145870
  have htrace : WordTrace (prefixWord ++ tailWord_5145870) baseStart_5145870 baseEnd_5145870 := by
    simpa [prefixWord, tailWord_5145870, baseEnd_5145870] using wordTrace_append hprefix tailTrace_5145870
  have hstable : (prefixWord ++ tailWord_5145870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145870).length < 2 ^ (prefixWord ++ tailWord_5145870).sum := by decide
  have hdescent : baseEnd_5145870 < baseStart_5145870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145929 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_5145929 : Nat := 118140960795 + 5145929 * 2 ^ 59
def prefixEnd_5145929 : Nat := 4983230072969 + 3 ^ 40 * 5145929 * 2
def baseEnd_5145929 : Nat := 2642334990910502262821809

theorem tailTrace_5145929 : CollatzResearch.WordTrace tailWord_5145929 prefixEnd_5145929 2642334990910502262821809 := by
  unfold tailWord_5145929
  simp only [CollatzResearch.WordTrace]
  refine ⟨187687449774185562549112841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125124966516123708366075227 187687449774185562549112841)
  ·
    refine ⟨140765587330639171911834631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187687449774185562549112841 140765587330639171911834631)
    ·
      refine ⟨211148380995958757867751947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140765587330639171911834631 211148380995958757867751947)
      ·
        refine ⟨316722571493938136801627921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211148380995958757867751947 316722571493938136801627921)
        ·
          refine ⟨237541928620453602601220941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316722571493938136801627921 237541928620453602601220941)
          ·
            refine ⟨89078223232670100975457853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237541928620453602601220941 89078223232670100975457853)
            ·
              refine ⟨33404333712251287865796695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89078223232670100975457853 33404333712251287865796695)
              ·
                refine ⟨50106500568376931798695043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33404333712251287865796695 50106500568376931798695043)
                ·
                  refine ⟨75159750852565397698042565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50106500568376931798695043 75159750852565397698042565)
                  ·
                    refine ⟨14092453284856012068382981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75159750852565397698042565 14092453284856012068382981)
                    ·
                      refine ⟨2642334990910502262821809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14092453284856012068382981 2642334990910502262821809)
                      ·
                        rfl

theorem cell23_5145929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_5145929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145929 prefixEnd_5145929 := by exact prefixLift 5145929
  have htrace : WordTrace (prefixWord ++ tailWord_5145929) baseStart_5145929 baseEnd_5145929 := by
    simpa [prefixWord, tailWord_5145929, baseEnd_5145929] using wordTrace_append hprefix tailTrace_5145929
  have hstable : (prefixWord ++ tailWord_5145929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145929).length < 2 ^ (prefixWord ++ tailWord_5145929).sum := by decide
  have hdescent : baseEnd_5145929 < baseStart_5145929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145939 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 7]
def baseStart_5145939 : Nat := 118140960795 + 5145939 * 2 ^ 59
def prefixEnd_5145939 : Nat := 4983230072969 + 3 ^ 40 * 5145939 * 2
def baseEnd_5145939 : Nat := 293593347301894135966307

theorem tailTrace_5145939 : CollatzResearch.WordTrace tailWord_5145939 prefixEnd_5145939 293593347301894135966307 := by
  unfold tailWord_5145939
  simp only [CollatzResearch.WordTrace]
  refine ⟨187687814504149334256976871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125125209669432889504651247 187687814504149334256976871)
  ·
    refine ⟨281531721756224001385465307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187687814504149334256976871 281531721756224001385465307)
    ·
      refine ⟨422297582634336002078197961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281531721756224001385465307 422297582634336002078197961)
      ·
        refine ⟨316723186975752001558648471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422297582634336002078197961 316723186975752001558648471)
        ·
          refine ⟨475084780463628002337972707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316723186975752001558648471 475084780463628002337972707)
          ·
            refine ⟨712627170695442003506959061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475084780463628002337972707 712627170695442003506959061)
            ·
              refine ⟨16702199313174421957194353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 712627170695442003506959061 16702199313174421957194353)
              ·
                refine ⟨12526649484880816467895765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16702199313174421957194353 12526649484880816467895765)
                ·
                  refine ⟨293593347301894135966307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12526649484880816467895765 293593347301894135966307)
                  ·
                    rfl

theorem cell23_5145939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 7].length) (baseStart_5145939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145939 prefixEnd_5145939 := by exact prefixLift 5145939
  have htrace : WordTrace (prefixWord ++ tailWord_5145939) baseStart_5145939 baseEnd_5145939 := by
    simpa [prefixWord, tailWord_5145939, baseEnd_5145939] using wordTrace_append hprefix tailTrace_5145939
  have hstable : (prefixWord ++ tailWord_5145939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145939).length < 2 ^ (prefixWord ++ tailWord_5145939).sum := by decide
  have hdescent : baseEnd_5145939 < baseStart_5145939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145973 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 7]
def baseStart_5145973 : Nat := 118140960795 + 5145973 * 2 ^ 59
def prefixEnd_5145973 : Nat := 4983230072969 + 3 ^ 40 * 5145973 * 2
def baseEnd_5145973 : Nat := 293595287117700010074623

theorem tailTrace_5145973 : CollatzResearch.WordTrace tailWord_5145973 prefixEnd_5145973 293595287117700010074623 := by
  unfold tailWord_5145973
  simp only [CollatzResearch.WordTrace]
  refine ⟨187689054586026158063714573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125126036390684105375809715 187689054586026158063714573)
  ·
    refine ⟨70383395469759809273892965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187689054586026158063714573 70383395469759809273892965)
    ·
      refine ⟨13196886650579964238854931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70383395469759809273892965 13196886650579964238854931)
      ·
        refine ⟨19795329975869946358282397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13196886650579964238854931 19795329975869946358282397)
        ·
          refine ⟨7423248740951229884355899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19795329975869946358282397 7423248740951229884355899)
          ·
            refine ⟨11134873111426844826533849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7423248740951229884355899 11134873111426844826533849)
            ·
              refine ⟨8351154833570133619900387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11134873111426844826533849 8351154833570133619900387)
              ·
                refine ⟨12526732250355200429850581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8351154833570133619900387 12526732250355200429850581)
                ·
                  refine ⟨293595287117700010074623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12526732250355200429850581 293595287117700010074623)
                  ·
                    rfl

theorem cell23_5145973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_5145973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145973 prefixEnd_5145973 := by exact prefixLift 5145973
  have htrace : WordTrace (prefixWord ++ tailWord_5145973) baseStart_5145973 baseEnd_5145973 := by
    simpa [prefixWord, tailWord_5145973, baseEnd_5145973] using wordTrace_append hprefix tailTrace_5145973
  have hstable : (prefixWord ++ tailWord_5145973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145973).length < 2 ^ (prefixWord ++ tailWord_5145973).sum := by decide
  have hdescent : baseEnd_5145973 < baseStart_5145973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5145979 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 7]
def baseStart_5145979 : Nat := 118140960795 + 5145979 * 2 ^ 59
def prefixEnd_5145979 : Nat := 4983230072969 + 3 ^ 40 * 5145979 * 2
def baseEnd_5145979 : Nat := 2642360664943227067196579

theorem tailTrace_5145979 : CollatzResearch.WordTrace tailWord_5145979 prefixEnd_5145979 2642360664943227067196579 := by
  unfold tailWord_5145979
  simp only [CollatzResearch.WordTrace]
  refine ⟨187689273424004421088432991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125126182282669614058955327 187689273424004421088432991)
  ·
    refine ⟨281533910136006631632649487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187689273424004421088432991 281533910136006631632649487)
    ·
      refine ⟨422300865204009947448974231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281533910136006631632649487 422300865204009947448974231)
      ·
        refine ⟨633451297806014921173461347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422300865204009947448974231 633451297806014921173461347)
        ·
          refine ⟨950176946709022381760192021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633451297806014921173461347 950176946709022381760192021)
          ·
            refine ⟨44539544376985424145009001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 950176946709022381760192021 44539544376985424145009001)
            ·
              refine ⟨33404658282739068108756751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44539544376985424145009001 33404658282739068108756751)
              ·
                refine ⟨50106987424108602163135127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33404658282739068108756751 50106987424108602163135127)
                ·
                  refine ⟨75160481136162903244702691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50106987424108602163135127 75160481136162903244702691)
                  ·
                    refine ⟨112740721704244354867054037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75160481136162903244702691 112740721704244354867054037)
                    ·
                      refine ⟨2642360664943227067196579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112740721704244354867054037 2642360664943227067196579)
                      ·
                        rfl

theorem cell23_5145979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_5145979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5145979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5145979 prefixEnd_5145979 := by exact prefixLift 5145979
  have htrace : WordTrace (prefixWord ++ tailWord_5145979) baseStart_5145979 baseEnd_5145979 := by
    simpa [prefixWord, tailWord_5145979, baseEnd_5145979] using wordTrace_append hprefix tailTrace_5145979
  have hstable : (prefixWord ++ tailWord_5145979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5145979).length < 2 ^ (prefixWord ++ tailWord_5145979).sum := by decide
  have hdescent : baseEnd_5145979 < baseStart_5145979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5145979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146023 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_5146023 : Nat := 118140960795 + 5146023 * 2 ^ 59
def prefixEnd_5146023 : Nat := 4983230072969 + 3 ^ 40 * 5146023 * 2
def baseEnd_5146023 : Nat := 2642383258092024895046377

theorem tailTrace_5146023 : CollatzResearch.WordTrace tailWord_5146023 prefixEnd_5146023 2642383258092024895046377 := by
  unfold tailWord_5146023
  simp only [CollatzResearch.WordTrace]
  refine ⟨187690878235845016603034723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125127252157230011068689815 187690878235845016603034723)
  ·
    refine ⟨281536317353767524904552085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187690878235845016603034723 281536317353767524904552085)
    ·
      refine ⟨13197014875957852729900879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 281536317353767524904552085 13197014875957852729900879)
      ·
        refine ⟨19795522313936779094851319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13197014875957852729900879 19795522313936779094851319)
        ·
          refine ⟨29693283470905168642276979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19795522313936779094851319 29693283470905168642276979)
          ·
            refine ⟨44539925206357752963415469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29693283470905168642276979 44539925206357752963415469)
            ·
              refine ⟨16702471952384157361280801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44539925206357752963415469 16702471952384157361280801)
              ·
                refine ⟨12526853964288118020960601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16702471952384157361280801 12526853964288118020960601)
                ·
                  refine ⟨9395140473216088515720451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12526853964288118020960601 9395140473216088515720451)
                  ·
                    refine ⟨14092710709824132773580677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9395140473216088515720451 14092710709824132773580677)
                    ·
                      refine ⟨2642383258092024895046377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14092710709824132773580677 2642383258092024895046377)
                      ·
                        rfl

theorem cell23_5146023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_5146023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146023 prefixEnd_5146023 := by exact prefixLift 5146023
  have htrace : WordTrace (prefixWord ++ tailWord_5146023) baseStart_5146023 baseEnd_5146023 := by
    simpa [prefixWord, tailWord_5146023, baseEnd_5146023] using wordTrace_append hprefix tailTrace_5146023
  have hstable : (prefixWord ++ tailWord_5146023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146023).length < 2 ^ (prefixWord ++ tailWord_5146023).sum := by decide
  have hdescent : baseEnd_5146023 < baseStart_5146023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146060 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_5146060 : Nat := 118140960795 + 5146060 * 2 ^ 59
def prefixEnd_5146060 : Nat := 4983230072969 + 3 ^ 40 * 5146060 * 2
def baseEnd_5146060 : Nat := 2642402256876241250283707

theorem tailTrace_5146060 : CollatzResearch.WordTrace tailWord_5146060 prefixEnd_5146060 2642402256876241250283707 := by
  unfold tailWord_5146060
  simp only [CollatzResearch.WordTrace]
  refine ⟨93846113868355485961065817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125128151824473981281421089 93846113868355485961065817)
  ·
    refine ⟨70384585401266614470799363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93846113868355485961065817 70384585401266614470799363)
    ·
      refine ⟨105576878101899921706199045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70384585401266614470799363 105576878101899921706199045)
      ·
        refine ⟨19795664644106235319912321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105576878101899921706199045 19795664644106235319912321)
        ·
          refine ⟨14846748483079676489934241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19795664644106235319912321 14846748483079676489934241)
          ·
            refine ⟨11135061362309757367450681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14846748483079676489934241 11135061362309757367450681)
            ·
              refine ⟨8351296021732318025588011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11135061362309757367450681 8351296021732318025588011)
              ·
                refine ⟨12526944032598477038382017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8351296021732318025588011 12526944032598477038382017)
                ·
                  refine ⟨9395208024448857778786513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12526944032598477038382017 9395208024448857778786513)
                  ·
                    refine ⟨7046406018336643334089885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9395208024448857778786513 7046406018336643334089885)
                    ·
                      refine ⟨2642402256876241250283707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7046406018336643334089885 2642402256876241250283707)
                      ·
                        rfl

theorem cell23_5146060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_5146060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146060 prefixEnd_5146060 := by exact prefixLift 5146060
  have htrace : WordTrace (prefixWord ++ tailWord_5146060) baseStart_5146060 baseEnd_5146060 := by
    simpa [prefixWord, tailWord_5146060, baseEnd_5146060] using wordTrace_append hprefix tailTrace_5146060
  have hstable : (prefixWord ++ tailWord_5146060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146060).length < 2 ^ (prefixWord ++ tailWord_5146060).sum := by decide
  have hdescent : baseEnd_5146060 < baseStart_5146060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146118 : List Nat := [6, 2, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5146118 : Nat := 118140960795 + 5146118 * 2 ^ 59
def prefixEnd_5146118 : Nat := 4983230072969 + 3 ^ 40 * 5146118 * 2
def baseEnd_5146118 : Nat := 880810679584734007786147

theorem tailTrace_5146118 : CollatzResearch.WordTrace tailWord_5146118 prefixEnd_5146118 880810679584734007786147 := by
  unfold tailWord_5146118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865448224078151494616969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125129562113667231885162005 5865448224078151494616969)
  ·
    refine ⟨4399086168058613620962727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5865448224078151494616969 4399086168058613620962727)
    ·
      refine ⟨6598629252087920431444091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399086168058613620962727 6598629252087920431444091)
      ·
        refine ⟨9897943878131880647166137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598629252087920431444091 9897943878131880647166137)
        ·
          refine ⟨7423457908598910485374603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9897943878131880647166137 7423457908598910485374603)
          ·
            refine ⟨11135186862898365728061905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7423457908598910485374603 11135186862898365728061905)
            ·
              refine ⟨8351390147173774296046429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11135186862898365728061905 8351390147173774296046429)
              ·
                refine ⟨3131771305190165361017411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8351390147173774296046429 3131771305190165361017411)
                ·
                  refine ⟨4697656957785248041526117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131771305190165361017411 4697656957785248041526117)
                  ·
                    refine ⟨880810679584734007786147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4697656957785248041526117 880810679584734007786147)
                    ·
                      rfl

theorem cell23_5146118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5146118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146118 prefixEnd_5146118 := by exact prefixLift 5146118
  have htrace : WordTrace (prefixWord ++ tailWord_5146118) baseStart_5146118 baseEnd_5146118 := by
    simpa [prefixWord, tailWord_5146118, baseEnd_5146118] using wordTrace_append hprefix tailTrace_5146118
  have hstable : (prefixWord ++ tailWord_5146118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146118).length < 2 ^ (prefixWord ++ tailWord_5146118).sum := by decide
  have hdescent : baseEnd_5146118 < baseStart_5146118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146124 : List Nat := [2, 2, 1, 2, 5, 1, 2, 3, 1, 1, 3]
def baseStart_5146124 : Nat := 118140960795 + 5146124 * 2 ^ 59
def prefixEnd_5146124 : Nat := 4983230072969 + 3 ^ 40 * 5146124 * 2
def baseEnd_5146124 : Nat := 2642435119638128999883413

theorem tailTrace_5146124 : CollatzResearch.WordTrace tailWord_5146124 prefixEnd_5146124 2642435119638128999883413 := by
  unfold tailWord_5146124
  simp only [CollatzResearch.WordTrace]
  refine ⟨93847281004239555426230713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125129708005652740568307617 93847281004239555426230713)
  ·
    refine ⟨70385460753179666569673035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93847281004239555426230713 70385460753179666569673035)
    ·
      refine ⟨105578191129769499854509553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70385460753179666569673035 105578191129769499854509553)
      ·
        refine ⟨79183643347327124890882165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105578191129769499854509553 79183643347327124890882165)
        ·
          refine ⟨7423466563811917958520203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79183643347327124890882165 7423466563811917958520203)
          ·
            refine ⟨11135199845717876937780305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7423466563811917958520203 11135199845717876937780305)
            ·
              refine ⟨8351399884288407703335229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11135199845717876937780305 8351399884288407703335229)
              ·
                refine ⟨3131774956608152888750711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8351399884288407703335229 3131774956608152888750711)
                ·
                  refine ⟨4697662434912229333126067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131774956608152888750711 4697662434912229333126067)
                  ·
                    refine ⟨7046493652368343999689101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4697662434912229333126067 7046493652368343999689101)
                    ·
                      refine ⟨2642435119638128999883413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7046493652368343999689101 2642435119638128999883413)
                      ·
                        rfl

theorem cell23_5146124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_5146124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146124 prefixEnd_5146124 := by exact prefixLift 5146124
  have htrace : WordTrace (prefixWord ++ tailWord_5146124) baseStart_5146124 baseEnd_5146124 := by
    simpa [prefixWord, tailWord_5146124, baseEnd_5146124] using wordTrace_append hprefix tailTrace_5146124
  have hstable : (prefixWord ++ tailWord_5146124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146124).length < 2 ^ (prefixWord ++ tailWord_5146124).sum := by decide
  have hdescent : baseEnd_5146124 < baseStart_5146124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146190 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_5146190 : Nat := 118140960795 + 5146190 * 2 ^ 59
def prefixEnd_5146190 : Nat := 4983230072969 + 3 ^ 40 * 5146190 * 2
def baseEnd_5146190 : Nat := 2642469009361325741658109

theorem tailTrace_5146190 : CollatzResearch.WordTrace tailWord_5146190 prefixEnd_5146190 2642469009361325741658109 := by
  unfold tailWord_5146190
  simp only [CollatzResearch.WordTrace]
  refine ⟨23462121153280000515545503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125131312817493336082909349 23462121153280000515545503)
  ·
    refine ⟨35193181729920000773318255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23462121153280000515545503 35193181729920000773318255)
    ·
      refine ⟨52789772594880001159977383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35193181729920000773318255 52789772594880001159977383)
      ·
        refine ⟨79184658892320001739966075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52789772594880001159977383 79184658892320001739966075)
        ·
          refine ⟨118776988338480002609949113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79184658892320001739966075 118776988338480002609949113)
          ·
            refine ⟨89082741253860001957461835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118776988338480002609949113 89082741253860001957461835)
            ·
              refine ⟨133624111880790002936192753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89082741253860001957461835 133624111880790002936192753)
              ·
                refine ⟨100218083910592502202144565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133624111880790002936192753 100218083910592502202144565)
                ·
                  refine ⟨9395445366618047081451053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100218083910592502202144565 9395445366618047081451053)
                  ·
                    refine ⟨3523292012481767655544145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9395445366618047081451053 3523292012481767655544145)
                    ·
                      refine ⟨2642469009361325741658109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523292012481767655544145 2642469009361325741658109)
                      ·
                        rfl

theorem cell23_5146190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_5146190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146190 prefixEnd_5146190 := by exact prefixLift 5146190
  have htrace : WordTrace (prefixWord ++ tailWord_5146190) baseStart_5146190 baseEnd_5146190 := by
    simpa [prefixWord, tailWord_5146190, baseEnd_5146190] using wordTrace_append hprefix tailTrace_5146190
  have hstable : (prefixWord ++ tailWord_5146190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146190).length < 2 ^ (prefixWord ++ tailWord_5146190).sum := by decide
  have hdescent : baseEnd_5146190 < baseStart_5146190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146220 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 1, 4, 2]
def baseStart_5146220 : Nat := 118140960795 + 5146220 * 2 ^ 59
def prefixEnd_5146220 : Nat := 4983230072969 + 3 ^ 40 * 5146220 * 2
def baseEnd_5146220 : Nat := 2642484413780960624282971

theorem tailTrace_5146220 : CollatzResearch.WordTrace tailWord_5146220 prefixEnd_5146220 2642484413780960624282971 := by
  unfold tailWord_5146220
  simp only [CollatzResearch.WordTrace]
  refine ⟨93849031708065659623978057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125132042277420879498637409 93849031708065659623978057)
  ·
    refine ⟨70386773781049244717983543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93849031708065659623978057 70386773781049244717983543)
    ·
      refine ⟨105580160671573867076975315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70386773781049244717983543 105580160671573867076975315)
      ·
        refine ⟨158370241007360800615462973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105580160671573867076975315 158370241007360800615462973)
        ·
          refine ⟨59388840377760300230798615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158370241007360800615462973 59388840377760300230798615)
          ·
            refine ⟨89083260566640450346197923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59388840377760300230798615 89083260566640450346197923)
            ·
              refine ⟨133624890849960675519296885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89083260566640450346197923 133624890849960675519296885)
              ·
                refine ⟨12527333517183813329934083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133624890849960675519296885 12527333517183813329934083)
                ·
                  refine ⟨18791000275775719994901125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12527333517183813329934083 18791000275775719994901125)
                  ·
                    refine ⟨3523312551707947499043961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18791000275775719994901125 3523312551707947499043961)
                    ·
                      refine ⟨2642484413780960624282971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523312551707947499043961 2642484413780960624282971)
                      ·
                        rfl

theorem cell23_5146220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_5146220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146220 prefixEnd_5146220 := by exact prefixLift 5146220
  have htrace : WordTrace (prefixWord ++ tailWord_5146220) baseStart_5146220 baseEnd_5146220 := by
    simpa [prefixWord, tailWord_5146220, baseEnd_5146220] using wordTrace_append hprefix tailTrace_5146220
  have hstable : (prefixWord ++ tailWord_5146220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146220).length < 2 ^ (prefixWord ++ tailWord_5146220).sum := by decide
  have hdescent : baseEnd_5146220 < baseStart_5146220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146224 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 1, 3, 2]
def baseStart_5146224 : Nat := 118140960795 + 5146224 * 2 ^ 59
def prefixEnd_5146224 : Nat := 4983230072969 + 3 ^ 40 * 5146224 * 2
def baseEnd_5146224 : Nat := 2642486467703578608632953

theorem tailTrace_5146224 : CollatzResearch.WordTrace tailWord_5146224 prefixEnd_5146224 2642486467703578608632953 := by
  unfold tailWord_5146224
  simp only [CollatzResearch.WordTrace]
  refine ⟨93849104654058413965550863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125132139538744551954067817 93849104654058413965550863)
  ·
    refine ⟨140773656981087620948326295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93849104654058413965550863 140773656981087620948326295)
    ·
      refine ⟨211160485471631431422489443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140773656981087620948326295 211160485471631431422489443)
      ·
        refine ⟨316740728207447147133734165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211160485471631431422489443 316740728207447147133734165)
        ·
          refine ⟨14847221634724085021893789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 316740728207447147133734165 14847221634724085021893789)
          ·
            refine ⟨5567708113021531883210171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14847221634724085021893789 5567708113021531883210171)
            ·
              refine ⟨8351562169532297824815257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567708113021531883210171 8351562169532297824815257)
              ·
                refine ⟨6263671627149223368611443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8351562169532297824815257 6263671627149223368611443)
                ·
                  refine ⟨9395507440723835052917165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6263671627149223368611443 9395507440723835052917165)
                  ·
                    refine ⟨3523315290271438144843937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9395507440723835052917165 3523315290271438144843937)
                    ·
                      refine ⟨2642486467703578608632953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523315290271438144843937 2642486467703578608632953)
                      ·
                        rfl

theorem cell23_5146224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 3, 2].length) (baseStart_5146224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146224 prefixEnd_5146224 := by exact prefixLift 5146224
  have htrace : WordTrace (prefixWord ++ tailWord_5146224) baseStart_5146224 baseEnd_5146224 := by
    simpa [prefixWord, tailWord_5146224, baseEnd_5146224] using wordTrace_append hprefix tailTrace_5146224
  have hstable : (prefixWord ++ tailWord_5146224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146224).length < 2 ^ (prefixWord ++ tailWord_5146224).sum := by decide
  have hdescent : baseEnd_5146224 < baseStart_5146224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146237 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_5146237 : Nat := 118140960795 + 5146237 * 2 ^ 59
def prefixEnd_5146237 : Nat := 4983230072969 + 3 ^ 40 * 5146237 * 2
def baseEnd_5146237 : Nat := 2642493142952087057770393

theorem tailTrace_5146237 : CollatzResearch.WordTrace tailWord_5146237 prefixEnd_5146237 2642493142952087057770393 := by
  unfold tailWord_5146237
  simp only [CollatzResearch.WordTrace]
  refine ⟨187698683457069731151324965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125132455638046487434216643 187698683457069731151324965)
  ·
    refine ⟨35193503148200574590873431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187698683457069731151324965 35193503148200574590873431)
    ·
      refine ⟨52790254722300861886310147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35193503148200574590873431 52790254722300861886310147)
      ·
        refine ⟨79185382083451292829465221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52790254722300861886310147 79185382083451292829465221)
        ·
          refine ⟨14847259140647117405524729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79185382083451292829465221 14847259140647117405524729)
          ·
            refine ⟨11135444355485338054143547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14847259140647117405524729 11135444355485338054143547)
            ·
              refine ⟨16703166533228007081215321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11135444355485338054143547 16703166533228007081215321)
              ·
                refine ⟨12527374899921005310911491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16703166533228007081215321 12527374899921005310911491)
                ·
                  refine ⟨18791062349881507966367237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12527374899921005310911491 18791062349881507966367237)
                  ·
                    refine ⟨3523324190602782743693857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18791062349881507966367237 3523324190602782743693857)
                    ·
                      refine ⟨2642493142952087057770393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523324190602782743693857 2642493142952087057770393)
                      ·
                        rfl

theorem cell23_5146237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_5146237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146237 prefixEnd_5146237 := by exact prefixLift 5146237
  have htrace : WordTrace (prefixWord ++ tailWord_5146237) baseStart_5146237 baseEnd_5146237 := by
    simpa [prefixWord, tailWord_5146237, baseEnd_5146237] using wordTrace_append hprefix tailTrace_5146237
  have hstable : (prefixWord ++ tailWord_5146237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146237).length < 2 ^ (prefixWord ++ tailWord_5146237).sum := by decide
  have hdescent : baseEnd_5146237 < baseStart_5146237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146254 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_5146254 : Nat := 118140960795 + 5146254 * 2 ^ 59
def prefixEnd_5146254 : Nat := 4983230072969 + 3 ^ 40 * 5146254 * 2
def baseEnd_5146254 : Nat := 2642501872123213491257815

theorem tailTrace_5146254 : CollatzResearch.WordTrace tailWord_5146254 prefixEnd_5146254 2642501872123213491257815 := by
  unfold tailWord_5146254
  simp only [CollatzResearch.WordTrace]
  refine ⟨23462412937251017881836727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125132868998672095369795877 23462412937251017881836727)
  ·
    refine ⟨35193619405876526822755091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23462412937251017881836727 35193619405876526822755091)
    ·
      refine ⟨52790429108814790234132637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35193619405876526822755091 52790429108814790234132637)
      ·
        refine ⟨19796410915805546337799739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52790429108814790234132637 19796410915805546337799739)
        ·
          refine ⟨29694616373708319506699609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19796410915805546337799739 29694616373708319506699609)
          ·
            refine ⟨22270962280281239630024707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29694616373708319506699609 22270962280281239630024707)
            ·
              refine ⟨33406443420421859445037061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22270962280281239630024707 33406443420421859445037061)
              ·
                refine ⟨6263708141329098645944449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33406443420421859445037061 6263708141329098645944449)
                ·
                  refine ⟨4697781105996823984458337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6263708141329098645944449 4697781105996823984458337)
                  ·
                    refine ⟨3523335829497617988343753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4697781105996823984458337 3523335829497617988343753)
                    ·
                      refine ⟨2642501872123213491257815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523335829497617988343753 2642501872123213491257815)
                      ·
                        rfl

theorem cell23_5146254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_5146254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146254 prefixEnd_5146254 := by exact prefixLift 5146254
  have htrace : WordTrace (prefixWord ++ tailWord_5146254) baseStart_5146254 baseEnd_5146254 := by
    simpa [prefixWord, tailWord_5146254, baseEnd_5146254] using wordTrace_append hprefix tailTrace_5146254
  have hstable : (prefixWord ++ tailWord_5146254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146254).length < 2 ^ (prefixWord ++ tailWord_5146254).sum := by decide
  have hdescent : baseEnd_5146254 < baseStart_5146254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146290 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_5146290 : Nat := 118140960795 + 5146290 * 2 ^ 59
def prefixEnd_5146290 : Nat := 4983230072969 + 3 ^ 40 * 5146290 * 2
def baseEnd_5146290 : Nat := 880840119142258450135883

theorem tailTrace_5146290 : CollatzResearch.WordTrace tailWord_5146290 prefixEnd_5146290 880840119142258450135883 := by
  unfold tailWord_5146290
  simp only [CollatzResearch.WordTrace]
  refine ⟨46925154131469430300751081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125133744350585147468669549 46925154131469430300751081)
  ·
    refine ⟨35193865598602072725563311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46925154131469430300751081 35193865598602072725563311)
    ·
      refine ⟨52790798397903109088344967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35193865598602072725563311 52790798397903109088344967)
      ·
        refine ⟨79186197596854663632517451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52790798397903109088344967 79186197596854663632517451)
        ·
          refine ⟨118779296395281995448776177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79186197596854663632517451 118779296395281995448776177)
          ·
            refine ⟨89084472296461496586582133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118779296395281995448776177 89084472296461496586582133)
            ·
              refine ⟨8351669277793265304992075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89084472296461496586582133 8351669277793265304992075)
              ·
                refine ⟨12527503916689897957488113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8351669277793265304992075 12527503916689897957488113)
                ·
                  refine ⟨9395627937517423468116085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12527503916689897957488113 9395627937517423468116085)
                  ·
                    refine ⟨880840119142258450135883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9395627937517423468116085 880840119142258450135883)
                    ·
                      rfl

theorem cell23_5146290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_5146290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146290 prefixEnd_5146290 := by exact prefixLift 5146290
  have htrace : WordTrace (prefixWord ++ tailWord_5146290) baseStart_5146290 baseEnd_5146290 := by
    simpa [prefixWord, tailWord_5146290, baseEnd_5146290] using wordTrace_append hprefix tailTrace_5146290
  have hstable : (prefixWord ++ tailWord_5146290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146290).length < 2 ^ (prefixWord ++ tailWord_5146290).sum := by decide
  have hdescent : baseEnd_5146290 < baseStart_5146290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146294 : List Nat := [5, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_5146294 : Nat := 118140960795 + 5146294 * 2 ^ 59
def prefixEnd_5146294 : Nat := 4983230072969 + 3 ^ 40 * 5146294 * 2
def baseEnd_5146294 : Nat := 293613601261043703861959

theorem tailTrace_5146294 : CollatzResearch.WordTrace tailWord_5146294 prefixEnd_5146294 293613601261043703861959 := by
  unfold tailWord_5146294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11731297651116451867884371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125133841611908819924099957 11731297651116451867884371)
  ·
    refine ⟨17596946476674677801826557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11731297651116451867884371 17596946476674677801826557)
    ·
      refine ⟨6598854928753004175684959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17596946476674677801826557 6598854928753004175684959)
      ·
        refine ⟨9898282393129506263527439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598854928753004175684959 9898282393129506263527439)
        ·
          refine ⟨14847423589694259395291159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9898282393129506263527439 14847423589694259395291159)
          ·
            refine ⟨22271135384541389092936739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14847423589694259395291159 22271135384541389092936739)
            ·
              refine ⟨33406703076812083639405109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22271135384541389092936739 33406703076812083639405109)
              ·
                refine ⟨3131878413451132841194229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33406703076812083639405109 3131878413451132841194229)
                ·
                  refine ⟨293613601261043703861959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3131878413451132841194229 293613601261043703861959)
                  ·
                    rfl

theorem cell23_5146294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_5146294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146294 prefixEnd_5146294 := by exact prefixLift 5146294
  have htrace : WordTrace (prefixWord ++ tailWord_5146294) baseStart_5146294 baseEnd_5146294 := by
    simpa [prefixWord, tailWord_5146294, baseEnd_5146294] using wordTrace_append hprefix tailTrace_5146294
  have hstable : (prefixWord ++ tailWord_5146294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146294).length < 2 ^ (prefixWord ++ tailWord_5146294).sum := by decide
  have hdescent : baseEnd_5146294 < baseStart_5146294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146330 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_5146330 : Nat := 118140960795 + 5146330 * 2 ^ 59
def prefixEnd_5146330 : Nat := 4983230072969 + 3 ^ 40 * 5146330 * 2
def baseEnd_5146330 : Nat := 2642540896652955193907465

theorem tailTrace_5146330 : CollatzResearch.WordTrace tailWord_5146330 prefixEnd_5146330 2642540896652955193907465 := by
  unfold tailWord_5146330
  simp only [CollatzResearch.WordTrace]
  refine ⟨46925518861433202008615111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125134716963821872022973629 46925518861433202008615111)
  ·
    refine ⟨70388278292149803012922667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46925518861433202008615111 70388278292149803012922667)
    ·
      refine ⟨105582417438224704519384001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70388278292149803012922667 105582417438224704519384001)
      ·
        refine ⟨79186813078668528389538001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105582417438224704519384001 79186813078668528389538001)
        ·
          refine ⟨59390109809001396292153501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79186813078668528389538001 59390109809001396292153501)
          ·
            refine ⟨22271291178375523609557563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59390109809001396292153501 22271291178375523609557563)
            ·
              refine ⟨33406936767563285414336345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22271291178375523609557563 33406936767563285414336345)
              ·
                refine ⟨25055202575672464060752259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33406936767563285414336345 25055202575672464060752259)
                ·
                  refine ⟨37582803863508696091128389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25055202575672464060752259 37582803863508696091128389)
                  ·
                    refine ⟨7046775724407880517086573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37582803863508696091128389 7046775724407880517086573)
                    ·
                      refine ⟨2642540896652955193907465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7046775724407880517086573 2642540896652955193907465)
                      ·
                        rfl

theorem cell23_5146330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_5146330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146330 prefixEnd_5146330 := by exact prefixLift 5146330
  have htrace : WordTrace (prefixWord ++ tailWord_5146330) baseStart_5146330 baseEnd_5146330 := by
    simpa [prefixWord, tailWord_5146330, baseEnd_5146330] using wordTrace_append hprefix tailTrace_5146330
  have hstable : (prefixWord ++ tailWord_5146330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146330).length < 2 ^ (prefixWord ++ tailWord_5146330).sum := by decide
  have hdescent : baseEnd_5146330 < baseStart_5146330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146373 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_5146373 : Nat := 118140960795 + 5146373 * 2 ^ 59
def prefixEnd_5146373 : Nat := 4983230072969 + 3 ^ 40 * 5146373 * 2
def baseEnd_5146373 : Nat := 2642562976321098525669767

theorem tailTrace_5146373 : CollatzResearch.WordTrace tailWord_5146373 prefixEnd_5146373 2642562976321098525669767 := by
  unfold tailWord_5146373
  simp only [CollatzResearch.WordTrace]
  refine ⟨187703643784577026378275773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125135762523051350918850515 187703643784577026378275773)
  ·
    refine ⟨70388866419216384891853415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187703643784577026378275773 70388866419216384891853415)
    ·
      refine ⟨105583299628824577337780123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70388866419216384891853415 105583299628824577337780123)
      ·
        refine ⟨158374949443236866006670185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105583299628824577337780123 158374949443236866006670185)
        ·
          refine ⟨118781212082427649505002639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158374949443236866006670185 118781212082427649505002639)
          ·
            refine ⟨178171818123641474257503959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118781212082427649505002639 178171818123641474257503959)
            ·
              refine ⟨267257727185462211386255939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178171818123641474257503959 267257727185462211386255939)
              ·
                refine ⟨400886590778193317079383909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267257727185462211386255939 400886590778193317079383909)
                ·
                  refine ⟨75166235770911246952384483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400886590778193317079383909 75166235770911246952384483)
                  ·
                    refine ⟨112749353656366870428576725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75166235770911246952384483 112749353656366870428576725)
                    ·
                      refine ⟨2642562976321098525669767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112749353656366870428576725 2642562976321098525669767)
                      ·
                        rfl

theorem cell23_5146373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_5146373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146373 prefixEnd_5146373 := by exact prefixLift 5146373
  have htrace : WordTrace (prefixWord ++ tailWord_5146373) baseStart_5146373 baseEnd_5146373 := by
    simpa [prefixWord, tailWord_5146373, baseEnd_5146373] using wordTrace_append hprefix tailTrace_5146373
  have hstable : (prefixWord ++ tailWord_5146373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146373).length < 2 ^ (prefixWord ++ tailWord_5146373).sum := by decide
  have hdescent : baseEnd_5146373 < baseStart_5146373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146398 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5146398 : Nat := 118140960795 + 5146398 * 2 ^ 59
def prefixEnd_5146398 : Nat := 4983230072969 + 3 ^ 40 * 5146398 * 2
def baseEnd_5146398 : Nat := 2642575813337460927857153

theorem tailTrace_5146398 : CollatzResearch.WordTrace tailWord_5146398 prefixEnd_5146398 2642575813337460927857153 := by
  unfold tailWord_5146398
  simp only [CollatzResearch.WordTrace]
  refine ⟨23463069451185806955991981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125136370406324303765290565 23463069451185806955991981)
  ·
    refine ⟨8798651044194677608496993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23463069451185806955991981 8798651044194677608496993)
    ·
      refine ⟨6598988283146008206372745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8798651044194677608496993 6598988283146008206372745)
      ·
        refine ⟨4949241212359506154779559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6598988283146008206372745 4949241212359506154779559)
        ·
          refine ⟨7423861818539259232169339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949241212359506154779559 7423861818539259232169339)
          ·
            refine ⟨11135792727808888848254009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7423861818539259232169339 11135792727808888848254009)
            ·
              refine ⟨8351844545856666636190507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11135792727808888848254009 8351844545856666636190507)
              ·
                refine ⟨12527766818784999954285761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8351844545856666636190507 12527766818784999954285761)
                ·
                  refine ⟨9395825114088749965714321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12527766818784999954285761 9395825114088749965714321)
                  ·
                    refine ⟨7046868835566562474285741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9395825114088749965714321 7046868835566562474285741)
                    ·
                      refine ⟨2642575813337460927857153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7046868835566562474285741 2642575813337460927857153)
                      ·
                        rfl

theorem cell23_5146398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5146398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146398 prefixEnd_5146398 := by exact prefixLift 5146398
  have htrace : WordTrace (prefixWord ++ tailWord_5146398) baseStart_5146398 baseEnd_5146398 := by
    simpa [prefixWord, tailWord_5146398, baseEnd_5146398] using wordTrace_append hprefix tailTrace_5146398
  have hstable : (prefixWord ++ tailWord_5146398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146398).length < 2 ^ (prefixWord ++ tailWord_5146398).sum := by decide
  have hdescent : baseEnd_5146398 < baseStart_5146398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146404 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_5146404 : Nat := 118140960795 + 5146404 * 2 ^ 59
def prefixEnd_5146404 : Nat := 4983230072969 + 3 ^ 40 * 5146404 * 2
def baseEnd_5146404 : Nat := 2642578894221387904382125

theorem tailTrace_5146404 : CollatzResearch.WordTrace tailWord_5146404 prefixEnd_5146404 2642578894221387904382125 := by
  unfold tailWord_5146404
  simp only [CollatzResearch.WordTrace]
  refine ⟨93852387223732359336327133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125136516298309812448436177 93852387223732359336327133)
  ·
    refine ⟨35194645208899634751122675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93852387223732359336327133 35194645208899634751122675)
    ·
      refine ⟨52791967813349452126684013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35194645208899634751122675 52791967813349452126684013)
      ·
        refine ⟨19796987930006044547506505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52791967813349452126684013 19796987930006044547506505)
        ·
          refine ⟨14847740947504533410629879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19796987930006044547506505 14847740947504533410629879)
          ·
            refine ⟨22271611421256800115944819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14847740947504533410629879 22271611421256800115944819)
            ·
              refine ⟨33407417131885200173917229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22271611421256800115944819 33407417131885200173917229)
              ·
                refine ⟨12527781424456950065218961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33407417131885200173917229 12527781424456950065218961)
                ·
                  refine ⟨9395836068342712548914221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12527781424456950065218961 9395836068342712548914221)
                  ·
                    refine ⟨3523438525628517205842833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9395836068342712548914221 3523438525628517205842833)
                    ·
                      refine ⟨2642578894221387904382125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523438525628517205842833 2642578894221387904382125)
                      ·
                        rfl

theorem cell23_5146404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_5146404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146404 prefixEnd_5146404 := by exact prefixLift 5146404
  have htrace : WordTrace (prefixWord ++ tailWord_5146404) baseStart_5146404 baseEnd_5146404 := by
    simpa [prefixWord, tailWord_5146404, baseEnd_5146404] using wordTrace_append hprefix tailTrace_5146404
  have hstable : (prefixWord ++ tailWord_5146404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146404).length < 2 ^ (prefixWord ++ tailWord_5146404).sum := by decide
  have hdescent : baseEnd_5146404 < baseStart_5146404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146440 : List Nat := [2, 1, 3, 1, 1, 4, 3, 8]
def baseStart_5146440 : Nat := 118140960795 + 5146440 * 2 ^ 59
def prefixEnd_5146440 : Nat := 4983230072969 + 3 ^ 40 * 5146440 * 2
def baseEnd_5146440 : Nat := 97873977019442583834517

theorem tailTrace_5146440 : CollatzResearch.WordTrace tailWord_5146440 prefixEnd_5146440 97873977019442583834517 := by
  unfold tailWord_5146440
  simp only [CollatzResearch.WordTrace]
  refine ⟨93853043737667148410482387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125137391650222864547309849 93853043737667148410482387)
  ·
    refine ⟨140779565606500722615723581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93853043737667148410482387 140779565606500722615723581)
    ·
      refine ⟨52792337102437770980896343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140779565606500722615723581 52792337102437770980896343)
      ·
        refine ⟨79188505653656656471344515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52792337102437770980896343 79188505653656656471344515)
        ·
          refine ⟨118782758480484984707016773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79188505653656656471344515 118782758480484984707016773)
          ·
            refine ⟨22271767215090934632565645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118782758480484984707016773 22271767215090934632565645)
            ·
              refine ⟨8351912705659100487212117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22271767215090934632565645 8351912705659100487212117)
              ·
                refine ⟨97873977019442583834517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8351912705659100487212117 97873977019442583834517)
                ·
                  rfl

theorem cell23_5146440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 8].length) (baseStart_5146440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146440 prefixEnd_5146440 := by exact prefixLift 5146440
  have htrace : WordTrace (prefixWord ++ tailWord_5146440) baseStart_5146440 baseEnd_5146440 := by
    simpa [prefixWord, tailWord_5146440, baseEnd_5146440] using wordTrace_append hprefix tailTrace_5146440
  have hstable : (prefixWord ++ tailWord_5146440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146440).length < 2 ^ (prefixWord ++ tailWord_5146440).sum := by decide
  have hdescent : baseEnd_5146440 < baseStart_5146440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146468 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_5146468 : Nat := 118140960795 + 5146468 * 2 ^ 59
def prefixEnd_5146468 : Nat := 4983230072969 + 3 ^ 40 * 5146468 * 2
def baseEnd_5146468 : Nat := 2642611756983275653981831

theorem tailTrace_5146468 : CollatzResearch.WordTrace tailWord_5146468 prefixEnd_5146468 2642611756983275653981831 := by
  unfold tailWord_5146468
  simp only [CollatzResearch.WordTrace]
  refine ⟨93853554359616428801492029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125138072479488571735322705 93853554359616428801492029)
  ·
    refine ⟨35195082884856160800559511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93853554359616428801492029 35195082884856160800559511)
    ·
      refine ⟨52792624327284241200839267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35195082884856160800559511 52792624327284241200839267)
      ·
        refine ⟨79188936490926361801258901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52792624327284241200839267 79188936490926361801258901)
        ·
          refine ⟨3711981398012173209434011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79188936490926361801258901 3711981398012173209434011)
          ·
            refine ⟨5567972097018259814151017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711981398012173209434011 5567972097018259814151017)
            ·
              refine ⟨4175979072763694860613263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5567972097018259814151017 4175979072763694860613263)
              ·
                refine ⟨6263968609145542290919895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4175979072763694860613263 6263968609145542290919895)
                ·
                  refine ⟨9395952913718313436379843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6263968609145542290919895 9395952913718313436379843)
                  ·
                    refine ⟨14093929370577470154569765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9395952913718313436379843 14093929370577470154569765)
                    ·
                      refine ⟨2642611756983275653981831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14093929370577470154569765 2642611756983275653981831)
                      ·
                        rfl

theorem cell23_5146468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_5146468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146468 prefixEnd_5146468 := by exact prefixLift 5146468
  have htrace : WordTrace (prefixWord ++ tailWord_5146468) baseStart_5146468 baseEnd_5146468 := by
    simpa [prefixWord, tailWord_5146468, baseEnd_5146468] using wordTrace_append hprefix tailTrace_5146468
  have hstable : (prefixWord ++ tailWord_5146468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146468).length < 2 ^ (prefixWord ++ tailWord_5146468).sum := by decide
  have hdescent : baseEnd_5146468 < baseStart_5146468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146490 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_5146490 : Nat := 118140960795 + 5146490 * 2 ^ 59
def prefixEnd_5146490 : Nat := 4983230072969 + 3 ^ 40 * 5146490 * 2
def baseEnd_5146490 : Nat := 2642623053557674567906729

theorem tailTrace_5146490 : CollatzResearch.WordTrace tailWord_5146490 prefixEnd_5146490 2642623053557674567906729 := by
  unfold tailWord_5146490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46926977781288288840071231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125138607416768770240189949 46926977781288288840071231)
  ·
    refine ⟨70390466671932433260106847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46926977781288288840071231 70390466671932433260106847)
    ·
      refine ⟨105585700007898649890160271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70390466671932433260106847 105585700007898649890160271)
      ·
        refine ⟨158378550011847974835240407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105585700007898649890160271 158378550011847974835240407)
        ·
          refine ⟨237567825017771962252860611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158378550011847974835240407 237567825017771962252860611)
          ·
            refine ⟨356351737526657943379290917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237567825017771962252860611 356351737526657943379290917)
            ·
              refine ⟨66815950786248364383617047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 356351737526657943379290917 66815950786248364383617047)
              ·
                refine ⟨100223926179372546575425571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66815950786248364383617047 100223926179372546575425571)
                ·
                  refine ⟨150335889269058819863138357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100223926179372546575425571 150335889269058819863138357)
                  ·
                    refine ⟨14093989618974264362169221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 150335889269058819863138357 14093989618974264362169221)
                    ·
                      refine ⟨2642623053557674567906729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14093989618974264362169221 2642623053557674567906729)
                      ·
                        rfl

theorem cell23_5146490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_5146490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146490 prefixEnd_5146490 := by exact prefixLift 5146490
  have htrace : WordTrace (prefixWord ++ tailWord_5146490) baseStart_5146490 baseEnd_5146490 := by
    simpa [prefixWord, tailWord_5146490, baseEnd_5146490] using wordTrace_append hprefix tailTrace_5146490
  have hstable : (prefixWord ++ tailWord_5146490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146490).length < 2 ^ (prefixWord ++ tailWord_5146490).sum := by decide
  have hdescent : baseEnd_5146490 < baseStart_5146490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146501 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 2, 1, 3]
def baseStart_5146501 : Nat := 118140960795 + 5146501 * 2 ^ 59
def prefixEnd_5146501 : Nat := 4983230072969 + 3 ^ 40 * 5146501 * 2
def baseEnd_5146501 : Nat := 2642628701844874024869179

theorem tailTrace_5146501 : CollatzResearch.WordTrace tailWord_5146501 prefixEnd_5146501 2642628701844874024869179 := by
  unfold tailWord_5146501
  simp only [CollatzResearch.WordTrace]
  refine ⟨187708312328113304238935357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125138874885408869492623571 187708312328113304238935357)
  ·
    refine ⟨70390617123042489089600759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187708312328113304238935357 70390617123042489089600759)
    ·
      refine ⟨105585925684563733634401139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70390617123042489089600759 105585925684563733634401139)
      ·
        refine ⟨158378888526845600451601709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105585925684563733634401139 158378888526845600451601709)
        ·
          refine ⟨59392083197567100169350641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158378888526845600451601709 59392083197567100169350641)
          ·
            refine ⟨44544062398175325127012981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59392083197567100169350641 44544062398175325127012981)
            ·
              refine ⟨4176005849828936730657467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44544062398175325127012981 4176005849828936730657467)
              ·
                refine ⟨6264008774743405095986201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176005849828936730657467 6264008774743405095986201)
                ·
                  refine ⟨4698006581057553821989651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6264008774743405095986201 4698006581057553821989651)
                  ·
                    refine ⟨7047009871586330732984477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4698006581057553821989651 7047009871586330732984477)
                    ·
                      refine ⟨2642628701844874024869179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7047009871586330732984477 2642628701844874024869179)
                      ·
                        rfl

theorem cell23_5146501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_5146501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146501 prefixEnd_5146501 := by exact prefixLift 5146501
  have htrace : WordTrace (prefixWord ++ tailWord_5146501) baseStart_5146501 baseEnd_5146501 := by
    simpa [prefixWord, tailWord_5146501, baseEnd_5146501] using wordTrace_append hprefix tailTrace_5146501
  have hstable : (prefixWord ++ tailWord_5146501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146501).length < 2 ^ (prefixWord ++ tailWord_5146501).sum := by decide
  have hdescent : baseEnd_5146501 < baseStart_5146501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146558 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_5146558 : Nat := 118140960795 + 5146558 * 2 ^ 59
def prefixEnd_5146558 : Nat := 4983230072969 + 3 ^ 40 * 5146558 * 2
def baseEnd_5146558 : Nat := 2642657970242180301856417

theorem tailTrace_5146558 : CollatzResearch.WordTrace tailWord_5146558 prefixEnd_5146558 2642657970242180301856417 := by
  unfold tailWord_5146558
  simp only [CollatzResearch.WordTrace]
  refine ⟨23463798911113350371720041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125140260859271201982506885 23463798911113350371720041)
  ·
    refine ⟨17597849183335012778790031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23463798911113350371720041 17597849183335012778790031)
    ·
      refine ⟨26396773775002519168185047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17597849183335012778790031 26396773775002519168185047)
      ·
        refine ⟨39595160662503778752277571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26396773775002519168185047 39595160662503778752277571)
        ·
          refine ⟨59392740993755668128416357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39595160662503778752277571 59392740993755668128416357)
          ·
            refine ⟨11136138936329187774078067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59392740993755668128416357 11136138936329187774078067)
            ·
              refine ⟨16704208404493781661117101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11136138936329187774078067 16704208404493781661117101)
              ·
                refine ⟨6264078151685168122918913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16704208404493781661117101 6264078151685168122918913)
                ·
                  refine ⟨4698058613763876092189185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6264078151685168122918913 4698058613763876092189185)
                  ·
                    refine ⟨3523543960322907069141889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4698058613763876092189185 3523543960322907069141889)
                    ·
                      refine ⟨2642657970242180301856417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523543960322907069141889 2642657970242180301856417)
                      ·
                        rfl

theorem cell23_5146558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_5146558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146558 prefixEnd_5146558 := by exact prefixLift 5146558
  have htrace : WordTrace (prefixWord ++ tailWord_5146558) baseStart_5146558 baseEnd_5146558 := by
    simpa [prefixWord, tailWord_5146558, baseEnd_5146558] using wordTrace_append hprefix tailTrace_5146558
  have hstable : (prefixWord ++ tailWord_5146558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146558).length < 2 ^ (prefixWord ++ tailWord_5146558).sum := by decide
  have hdescent : baseEnd_5146558 < baseStart_5146558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146628 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_5146628 : Nat := 118140960795 + 5146628 * 2 ^ 59
def prefixEnd_5146628 : Nat := 4983230072969 + 3 ^ 40 * 5146628 * 2
def baseEnd_5146628 : Nat := 880897971295998342660365

theorem tailTrace_5146628 : CollatzResearch.WordTrace tailWord_5146628 prefixEnd_5146628 880897971295998342660365 := by
  unfold tailWord_5146628
  simp only [CollatzResearch.WordTrace]
  refine ⟨93856472199326602464404269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125141962932435469952539025 93856472199326602464404269)
  ·
    refine ⟨35196177074747475924151601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93856472199326602464404269 35196177074747475924151601)
    ·
      refine ⟨26397132806060606943113701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35196177074747475924151601 26397132806060606943113701)
      ·
        refine ⟨4949462401136363801833819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26397132806060606943113701 4949462401136363801833819)
        ·
          refine ⟨7424193601704545702750729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949462401136363801833819 7424193601704545702750729)
          ·
            refine ⟨5568145201278409277063047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7424193601704545702750729 5568145201278409277063047)
            ·
              refine ⟨8352217801917613915594571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568145201278409277063047 8352217801917613915594571)
              ·
                refine ⟨12528326702876420873391857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8352217801917613915594571 12528326702876420873391857)
                ·
                  refine ⟨9396245027157315655043893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12528326702876420873391857 9396245027157315655043893)
                  ·
                    refine ⟨880897971295998342660365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9396245027157315655043893 880897971295998342660365)
                    ·
                      rfl

theorem cell23_5146628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_5146628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146628 prefixEnd_5146628 := by exact prefixLift 5146628
  have htrace : WordTrace (prefixWord ++ tailWord_5146628) baseStart_5146628 baseEnd_5146628 := by
    simpa [prefixWord, tailWord_5146628, baseEnd_5146628] using wordTrace_append hprefix tailTrace_5146628
  have hstable : (prefixWord ++ tailWord_5146628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146628).length < 2 ^ (prefixWord ++ tailWord_5146628).sum := by decide
  have hdescent : baseEnd_5146628 < baseStart_5146628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146631 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_5146631 : Nat := 118140960795 + 5146631 * 2 ^ 59
def prefixEnd_5146631 : Nat := 4983230072969 + 3 ^ 40 * 5146631 * 2
def baseEnd_5146631 : Nat := 2642695454329958516243581

theorem tailTrace_5146631 : CollatzResearch.WordTrace tailWord_5146631 prefixEnd_5146631 2642695454329958516243581 := by
  unfold tailWord_5146631
  simp only [CollatzResearch.WordTrace]
  refine ⟨187713053817642336441167747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125142035878428224294111831 187713053817642336441167747)
  ·
    refine ⟨281569580726463504661751621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187713053817642336441167747 281569580726463504661751621)
    ·
      refine ⟨52794296386211907124078429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281569580726463504661751621 52794296386211907124078429)
      ·
        refine ⟨19797861144829465171529411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52794296386211907124078429 19797861144829465171529411)
        ·
          refine ⟨29696791717244197757294117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19797861144829465171529411 29696791717244197757294117)
          ·
            refine ⟨5568148446983287079492647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29696791717244197757294117 5568148446983287079492647)
            ·
              refine ⟨8352222670474930619238971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568148446983287079492647 8352222670474930619238971)
              ·
                refine ⟨12528334005712395928858457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8352222670474930619238971 12528334005712395928858457)
                ·
                  refine ⟨9396250504284296946643843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12528334005712395928858457 9396250504284296946643843)
                  ·
                    refine ⟨14094375756426445419965765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9396250504284296946643843 14094375756426445419965765)
                    ·
                      refine ⟨2642695454329958516243581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14094375756426445419965765 2642695454329958516243581)
                      ·
                        rfl

theorem cell23_5146631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_5146631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146631 prefixEnd_5146631 := by exact prefixLift 5146631
  have htrace : WordTrace (prefixWord ++ tailWord_5146631) baseStart_5146631 baseEnd_5146631 := by
    simpa [prefixWord, tailWord_5146631, baseEnd_5146631] using wordTrace_append hprefix tailTrace_5146631
  have hstable : (prefixWord ++ tailWord_5146631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146631).length < 2 ^ (prefixWord ++ tailWord_5146631).sum := by decide
  have hdescent : baseEnd_5146631 < baseStart_5146631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146667 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 3, 5]
def baseStart_5146667 : Nat := 118140960795 + 5146667 * 2 ^ 59
def prefixEnd_5146667 : Nat := 4983230072969 + 3 ^ 40 * 5146667 * 2
def baseEnd_5146667 : Nat := 880904646544506791797805

theorem tailTrace_5146667 : CollatzResearch.WordTrace tailWord_5146667 prefixEnd_5146667 880904646544506791797805 := by
  unfold tailWord_5146667
  simp only [CollatzResearch.WordTrace]
  refine ⟨187714366845511914589478255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125142911230341276392985503 187714366845511914589478255)
  ·
    refine ⟨281571550268267871884217383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187714366845511914589478255 281571550268267871884217383)
    ·
      refine ⟨422357325402401807826326075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281571550268267871884217383 422357325402401807826326075)
      ·
        refine ⟨633535988103602711739489113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422357325402401807826326075 633535988103602711739489113)
        ·
          refine ⟨475151991077702033804616835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633535988103602711739489113 475151991077702033804616835)
          ·
            refine ⟨712727986616553050706925253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475151991077702033804616835 712727986616553050706925253)
            ·
              refine ⟨133636497490603697007548485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 712727986616553050706925253 133636497490603697007548485)
              ·
                refine ⟨25056843279488193188915341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133636497490603697007548485 25056843279488193188915341)
                ·
                  refine ⟨9396316229808072445843253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25056843279488193188915341 9396316229808072445843253)
                  ·
                    refine ⟨880904646544506791797805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9396316229808072445843253 880904646544506791797805)
                    ·
                      rfl

theorem cell23_5146667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 5].length) (baseStart_5146667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146667 prefixEnd_5146667 := by exact prefixLift 5146667
  have htrace : WordTrace (prefixWord ++ tailWord_5146667) baseStart_5146667 baseEnd_5146667 := by
    simpa [prefixWord, tailWord_5146667, baseEnd_5146667] using wordTrace_append hprefix tailTrace_5146667
  have hstable : (prefixWord ++ tailWord_5146667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146667).length < 2 ^ (prefixWord ++ tailWord_5146667).sum := by decide
  have hdescent : baseEnd_5146667 < baseStart_5146667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146677 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_5146677 : Nat := 118140960795 + 5146677 * 2 ^ 59
def prefixEnd_5146677 : Nat := 4983230072969 + 3 ^ 40 * 5146677 * 2
def baseEnd_5146677 : Nat := 2642719074440065336268369

theorem tailTrace_5146677 : CollatzResearch.WordTrace tailWord_5146677 prefixEnd_5146677 2642719074440065336268369 := by
  unfold tailWord_5146677
  simp only [CollatzResearch.WordTrace]
  refine ⟨187714731575475686297342285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125143154383650457531561523 187714731575475686297342285)
  ·
    refine ⟨70393024340803382361503357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187714731575475686297342285 70393024340803382361503357)
    ·
      refine ⟨26397384127801268385563759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70393024340803382361503357 26397384127801268385563759)
      ·
        refine ⟨39596076191701902578345639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26397384127801268385563759 39596076191701902578345639)
        ·
          refine ⟨59394114287552853867518459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39596076191701902578345639 59394114287552853867518459)
          ·
            refine ⟨89091171431329280801277689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59394114287552853867518459 89091171431329280801277689)
            ·
              refine ⟨66818378573496960600958267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89091171431329280801277689 66818378573496960600958267)
              ·
                refine ⟨100227567860245440901437401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66818378573496960600958267 100227567860245440901437401)
                ·
                  refine ⟨75170675895184080676078051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100227567860245440901437401 75170675895184080676078051)
                  ·
                    refine ⟨112756013842776121014117077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75170675895184080676078051 112756013842776121014117077)
                    ·
                      refine ⟨2642719074440065336268369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112756013842776121014117077 2642719074440065336268369)
                      ·
                        rfl

theorem cell23_5146677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_5146677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146677 prefixEnd_5146677 := by exact prefixLift 5146677
  have htrace : WordTrace (prefixWord ++ tailWord_5146677) baseStart_5146677 baseEnd_5146677 := by
    simpa [prefixWord, tailWord_5146677, baseEnd_5146677] using wordTrace_append hprefix tailTrace_5146677
  have hstable : (prefixWord ++ tailWord_5146677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146677).length < 2 ^ (prefixWord ++ tailWord_5146677).sum := by decide
  have hdescent : baseEnd_5146677 < baseStart_5146677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146697 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 3, 6]
def baseStart_5146697 : Nat := 118140960795 + 5146697 * 2 ^ 59
def prefixEnd_5146697 : Nat := 4983230072969 + 3 ^ 40 * 5146697 * 2
def baseEnd_5146697 : Nat := 880909781351051752672759

theorem tailTrace_5146697 : CollatzResearch.WordTrace tailWord_5146697 prefixEnd_5146697 880909781351051752672759 := by
  unfold tailWord_5146697
  simp only [CollatzResearch.WordTrace]
  refine ⟨187715461035403229713070345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125143640690268819808713563 187715461035403229713070345)
  ·
    refine ⟨140786595776552422284802759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187715461035403229713070345 140786595776552422284802759)
    ·
      refine ⟨211179893664828633427204139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140786595776552422284802759 211179893664828633427204139)
      ·
        refine ⟨316769840497242950140806209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211179893664828633427204139 316769840497242950140806209)
        ·
          refine ⟨237577380372932212605604657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316769840497242950140806209 237577380372932212605604657)
          ·
            refine ⟨178183035279699159454203493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237577380372932212605604657 178183035279699159454203493)
            ·
              refine ⟨33409319114943592397663155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178183035279699159454203493 33409319114943592397663155)
              ·
                refine ⟨50113978672415388596494733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33409319114943592397663155 50113978672415388596494733)
                ·
                  refine ⟨18792742002155770723685525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50113978672415388596494733 18792742002155770723685525)
                  ·
                    refine ⟨880909781351051752672759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18792742002155770723685525 880909781351051752672759)
                    ·
                      rfl

theorem cell23_5146697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_5146697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146697 prefixEnd_5146697 := by exact prefixLift 5146697
  have htrace : WordTrace (prefixWord ++ tailWord_5146697) baseStart_5146697 baseEnd_5146697 := by
    simpa [prefixWord, tailWord_5146697, baseEnd_5146697] using wordTrace_append hprefix tailTrace_5146697
  have hstable : (prefixWord ++ tailWord_5146697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146697).length < 2 ^ (prefixWord ++ tailWord_5146697).sum := by decide
  have hdescent : baseEnd_5146697 < baseStart_5146697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146701 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5146701 : Nat := 118140960795 + 5146701 * 2 ^ 59
def prefixEnd_5146701 : Nat := 4983230072969 + 3 ^ 40 * 5146701 * 2
def baseEnd_5146701 : Nat := 880910465991924414122753

theorem tailTrace_5146701 : CollatzResearch.WordTrace tailWord_5146701 prefixEnd_5146701 880910465991924414122753 := by
  unfold tailWord_5146701
  simp only [CollatzResearch.WordTrace]
  refine ⟨187715606927388738396215957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125143737951592492264143971 187715606927388738396215957)
  ·
    refine ⟨8799169074721347112322623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187715606927388738396215957 8799169074721347112322623)
    ·
      refine ⟨13198753612082020668483935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8799169074721347112322623 13198753612082020668483935)
      ·
        refine ⟨19798130418123031002725903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13198753612082020668483935 19798130418123031002725903)
        ·
          refine ⟨29697195627184546504088855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19798130418123031002725903 29697195627184546504088855)
          ·
            refine ⟨44545793440776819756133283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29697195627184546504088855 44545793440776819756133283)
            ·
              refine ⟨66818690161165229634199925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44545793440776819756133283 66818690161165229634199925)
              ·
                refine ⟨6264252202609240278206243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66818690161165229634199925 6264252202609240278206243)
                ·
                  refine ⟨9396378303913860417309365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6264252202609240278206243 9396378303913860417309365)
                  ·
                    refine ⟨880910465991924414122753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9396378303913860417309365 880910465991924414122753)
                    ·
                      rfl

theorem cell23_5146701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5146701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146701 prefixEnd_5146701 := by exact prefixLift 5146701
  have htrace : WordTrace (prefixWord ++ tailWord_5146701) baseStart_5146701 baseEnd_5146701 := by
    simpa [prefixWord, tailWord_5146701, baseEnd_5146701] using wordTrace_append hprefix tailTrace_5146701
  have hstable : (prefixWord ++ tailWord_5146701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146701).length < 2 ^ (prefixWord ++ tailWord_5146701).sum := by decide
  have hdescent : baseEnd_5146701 < baseStart_5146701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146714 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_5146714 : Nat := 118140960795 + 5146714 * 2 ^ 59
def prefixEnd_5146714 : Nat := 4983230072969 + 3 ^ 40 * 5146714 * 2
def baseEnd_5146714 : Nat := 880912691074760563835233

theorem tailTrace_5146714 : CollatzResearch.WordTrace tailWord_5146714 prefixEnd_5146714 880912691074760563835233 := by
  unfold tailWord_5146714
  simp only [CollatzResearch.WordTrace]
  refine ⟨46929020269085410404109799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125144054050894427744292797 46929020269085410404109799)
  ·
    refine ⟨70393530403628115606164699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46929020269085410404109799 70393530403628115606164699)
    ·
      refine ⟨105590295605442173409247049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70393530403628115606164699 105590295605442173409247049)
      ·
        refine ⟨79192721704081630056935287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105590295605442173409247049 79192721704081630056935287)
        ·
          refine ⟨118789082556122445085402931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79192721704081630056935287 118789082556122445085402931)
          ·
            refine ⟨178183623834183667628104397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118789082556122445085402931 178183623834183667628104397)
            ·
              refine ⟨66818858937818875360539149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178183623834183667628104397 66818858937818875360539149)
              ·
                refine ⟨25057072101682078260202181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66818858937818875360539149 25057072101682078260202181)
                ·
                  refine ⟨4698201019065389673787909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25057072101682078260202181 4698201019065389673787909)
                  ·
                    refine ⟨880912691074760563835233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4698201019065389673787909 880912691074760563835233)
                    ·
                      rfl

theorem cell23_5146714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_5146714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146714 prefixEnd_5146714 := by exact prefixLift 5146714
  have htrace : WordTrace (prefixWord ++ tailWord_5146714) baseStart_5146714 baseEnd_5146714 := by
    simpa [prefixWord, tailWord_5146714, baseEnd_5146714] using wordTrace_append hprefix tailTrace_5146714
  have hstable : (prefixWord ++ tailWord_5146714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146714).length < 2 ^ (prefixWord ++ tailWord_5146714).sum := by decide
  have hdescent : baseEnd_5146714 < baseStart_5146714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146724 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_5146724 : Nat := 118140960795 + 5146724 * 2 ^ 59
def prefixEnd_5146724 : Nat := 4983230072969 + 3 ^ 40 * 5146724 * 2
def baseEnd_5146724 : Nat := 2642743208030826652380653

theorem tailTrace_5146724 : CollatzResearch.WordTrace tailWord_5146724 prefixEnd_5146724 2642743208030826652380653 := by
  unfold tailWord_5146724
  simp only [CollatzResearch.WordTrace]
  refine ⟨93858222903152706662151613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125144297204203608882868817 93858222903152706662151613)
  ·
    refine ⟨35196833588682264998306855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93858222903152706662151613 35196833588682264998306855)
    ·
      refine ⟨52795250383023397497460283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35196833588682264998306855 52795250383023397497460283)
      ·
        refine ⟨79192875574535096246190425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52795250383023397497460283 79192875574535096246190425)
        ·
          refine ⟨59394656680901322184642819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79192875574535096246190425 59394656680901322184642819)
          ·
            refine ⟨89091985021351983276964229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59394656680901322184642819 89091985021351983276964229)
            ·
              refine ⟨16704747191503496864430793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89091985021351983276964229 16704747191503496864430793)
              ·
                refine ⟨12528560393627622648323095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16704747191503496864430793 12528560393627622648323095)
                ·
                  refine ⟨18792840590441433972484643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12528560393627622648323095 18792840590441433972484643)
                  ·
                    refine ⟨28189260885662150958726965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18792840590441433972484643 28189260885662150958726965)
                    ·
                      refine ⟨2642743208030826652380653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28189260885662150958726965 2642743208030826652380653)
                      ·
                        rfl

theorem cell23_5146724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_5146724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146724 prefixEnd_5146724 := by exact prefixLift 5146724
  have htrace : WordTrace (prefixWord ++ tailWord_5146724) baseStart_5146724 baseEnd_5146724 := by
    simpa [prefixWord, tailWord_5146724, baseEnd_5146724] using wordTrace_append hprefix tailTrace_5146724
  have hstable : (prefixWord ++ tailWord_5146724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146724).length < 2 ^ (prefixWord ++ tailWord_5146724).sum := by decide
  have hdescent : baseEnd_5146724 < baseStart_5146724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146734 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_5146734 : Nat := 118140960795 + 5146734 * 2 ^ 59
def prefixEnd_5146734 : Nat := 4983230072969 + 3 ^ 40 * 5146734 * 2
def baseEnd_5146734 : Nat := 2642748342837371613255607

theorem tailTrace_5146734 : CollatzResearch.WordTrace tailWord_5146734 prefixEnd_5146734 2642748342837371613255607 := by
  unfold tailWord_5146734
  simp only [CollatzResearch.WordTrace]
  refine ⟨23464601317033648129020907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125144540357512790021444837 23464601317033648129020907)
  ·
    refine ⟨35196901975550472193531361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23464601317033648129020907 35196901975550472193531361)
    ·
      refine ⟨26397676481662854145148521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35196901975550472193531361 26397676481662854145148521)
      ·
        refine ⟨19798257361247140608861391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26397676481662854145148521 19798257361247140608861391)
        ·
          refine ⟨29697386041870710913292087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19798257361247140608861391 29697386041870710913292087)
          ·
            refine ⟨44546079062806066369938131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29697386041870710913292087 44546079062806066369938131)
            ·
              refine ⟨66819118594209099554907197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44546079062806066369938131 66819118594209099554907197)
              ·
                refine ⟨25057169472828412333090199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66819118594209099554907197 25057169472828412333090199)
                ·
                  refine ⟨37585754209242618499635299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25057169472828412333090199 37585754209242618499635299)
                  ·
                    refine ⟨56378631313863927749452949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37585754209242618499635299 56378631313863927749452949)
                    ·
                      refine ⟨2642748342837371613255607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56378631313863927749452949 2642748342837371613255607)
                      ·
                        rfl

theorem cell23_5146734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_5146734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146734 prefixEnd_5146734 := by exact prefixLift 5146734
  have htrace : WordTrace (prefixWord ++ tailWord_5146734) baseStart_5146734 baseEnd_5146734 := by
    simpa [prefixWord, tailWord_5146734, baseEnd_5146734] using wordTrace_append hprefix tailTrace_5146734
  have hstable : (prefixWord ++ tailWord_5146734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146734).length < 2 ^ (prefixWord ++ tailWord_5146734).sum := by decide
  have hdescent : baseEnd_5146734 < baseStart_5146734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146738 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_5146738 : Nat := 118140960795 + 5146738 * 2 ^ 59
def prefixEnd_5146738 : Nat := 4983230072969 + 3 ^ 40 * 5146738 * 2
def baseEnd_5146738 : Nat := 2642750396759989597605589

theorem tailTrace_5146738 : CollatzResearch.WordTrace tailWord_5146738 prefixEnd_5146738 2642750396759989597605589 := by
  unfold tailWord_5146738
  simp only [CollatzResearch.WordTrace]
  refine ⟨46929239107063673428828217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125144637618836462476875245 46929239107063673428828217)
  ·
    refine ⟨35196929330297755071621163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46929239107063673428828217 35196929330297755071621163)
    ·
      refine ⟨52795393995446632607431745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35196929330297755071621163 52795393995446632607431745)
      ·
        refine ⟨39596545496584974455573809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52795393995446632607431745 39596545496584974455573809)
        ·
          refine ⟨29697409122438730841680357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39596545496584974455573809 29697409122438730841680357)
          ·
            refine ⟨5568264210457262032815067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29697409122438730841680357 5568264210457262032815067)
            ·
              refine ⟨8352396315685893049222601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568264210457262032815067 8352396315685893049222601)
              ·
                refine ⟨6264297236764419786916951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8352396315685893049222601 6264297236764419786916951)
                ·
                  refine ⟨9396445855146629680375427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6264297236764419786916951 9396445855146629680375427)
                  ·
                    refine ⟨14094668782719944520563141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9396445855146629680375427 14094668782719944520563141)
                    ·
                      refine ⟨2642750396759989597605589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14094668782719944520563141 2642750396759989597605589)
                      ·
                        rfl

theorem cell23_5146738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_5146738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146738 prefixEnd_5146738 := by exact prefixLift 5146738
  have htrace : WordTrace (prefixWord ++ tailWord_5146738) baseStart_5146738 baseEnd_5146738 := by
    simpa [prefixWord, tailWord_5146738, baseEnd_5146738] using wordTrace_append hprefix tailTrace_5146738
  have hstable : (prefixWord ++ tailWord_5146738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146738).length < 2 ^ (prefixWord ++ tailWord_5146738).sum := by decide
  have hdescent : baseEnd_5146738 < baseStart_5146738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146778 : List Nat := [3, 1, 1, 5, 3, 1, 1, 8]
def baseStart_5146778 : Nat := 118140960795 + 5146778 * 2 ^ 59
def prefixEnd_5146778 : Nat := 4983230072969 + 3 ^ 40 * 5146778 * 2
def baseEnd_5146778 : Nat := 97880405036524794115015

theorem tailTrace_5146778 : CollatzResearch.WordTrace tailWord_5146778 prefixEnd_5146778 97880405036524794115015 := by
  unfold tailWord_5146778
  simp only [CollatzResearch.WordTrace]
  refine ⟨46929603837027445136692247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125145610232073187031179325 46929603837027445136692247)
  ·
    refine ⟨70394405755541167705038371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46929603837027445136692247 70394405755541167705038371)
    ·
      refine ⟨105591608633311751557557557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70394405755541167705038371 105591608633311751557557557)
      ·
        refine ⟨9899213309372976708521021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105591608633311751557557557 9899213309372976708521021)
        ·
          refine ⟨3712204991014866265695383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9899213309372976708521021 3712204991014866265695383)
          ·
            refine ⟨5568307486522299398543075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712204991014866265695383 5568307486522299398543075)
            ·
              refine ⟨8352461229783449097814613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568307486522299398543075 8352461229783449097814613)
              ·
                refine ⟨97880405036524794115015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8352461229783449097814613 97880405036524794115015)
                ·
                  rfl

theorem cell23_5146778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 8].length) (baseStart_5146778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146778 prefixEnd_5146778 := by exact prefixLift 5146778
  have htrace : WordTrace (prefixWord ++ tailWord_5146778) baseStart_5146778 baseEnd_5146778 := by
    simpa [prefixWord, tailWord_5146778, baseEnd_5146778] using wordTrace_append hprefix tailTrace_5146778
  have hstable : (prefixWord ++ tailWord_5146778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146778).length < 2 ^ (prefixWord ++ tailWord_5146778).sum := by decide
  have hdescent : baseEnd_5146778 < baseStart_5146778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146788 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_5146788 : Nat := 118140960795 + 5146788 * 2 ^ 59
def prefixEnd_5146788 : Nat := 4983230072969 + 3 ^ 40 * 5146788 * 2
def baseEnd_5146788 : Nat := 2642776070792714401980359

theorem tailTrace_5146788 : CollatzResearch.WordTrace tailWord_5146788 prefixEnd_5146788 2642776070792714401980359 := by
  unfold tailWord_5146788
  simp only [CollatzResearch.WordTrace]
  refine ⟨93859390039036776127316509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125145853385382368169755345 93859390039036776127316509)
  ·
    refine ⟨35197271264638791047743691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93859390039036776127316509 35197271264638791047743691)
    ·
      refine ⟨52795906896958186571615537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35197271264638791047743691 52795906896958186571615537)
      ·
        refine ⟨39596930172718639928711653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52795906896958186571615537 39596930172718639928711653)
        ·
          refine ⟨7424424407384744986633435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39596930172718639928711653 7424424407384744986633435)
          ·
            refine ⟨11136636611077117479950153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7424424407384744986633435 11136636611077117479950153)
            ·
              refine ⟨8352477458307838109962615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11136636611077117479950153 8352477458307838109962615)
              ·
                refine ⟨12528716187461757164943923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8352477458307838109962615 12528716187461757164943923)
                ·
                  refine ⟨18793074281192635747415885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12528716187461757164943923 18793074281192635747415885)
                  ·
                    refine ⟨7047402855447238405280957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18793074281192635747415885 7047402855447238405280957)
                    ·
                      refine ⟨2642776070792714401980359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7047402855447238405280957 2642776070792714401980359)
                      ·
                        rfl

theorem cell23_5146788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_5146788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146788 prefixEnd_5146788 := by exact prefixLift 5146788
  have htrace : WordTrace (prefixWord ++ tailWord_5146788) baseStart_5146788 baseEnd_5146788 := by
    simpa [prefixWord, tailWord_5146788, baseEnd_5146788] using wordTrace_append hprefix tailTrace_5146788
  have hstable : (prefixWord ++ tailWord_5146788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146788).length < 2 ^ (prefixWord ++ tailWord_5146788).sum := by decide
  have hdescent : baseEnd_5146788 < baseStart_5146788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146811 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 1, 4, 2]
def baseStart_5146811 : Nat := 118140960795 + 5146811 * 2 ^ 59
def prefixEnd_5146811 : Nat := 4983230072969 + 3 ^ 40 * 5146811 * 2
def baseEnd_5146811 : Nat := 2642787880847767811992753

theorem tailTrace_5146811 : CollatzResearch.WordTrace tailWord_5146811 prefixEnd_5146811 2642787880847767811992753 := by
  unfold tailWord_5146811
  simp only [CollatzResearch.WordTrace]
  refine ⟨187719618956990227182720287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125146412637993484788480191 187719618956990227182720287)
  ·
    refine ⟨281579428435485340774080431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187719618956990227182720287 281579428435485340774080431)
    ·
      refine ⟨422369142653228011161120647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281579428435485340774080431 422369142653228011161120647)
      ·
        refine ⟨633553713979842016741680971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422369142653228011161120647 633553713979842016741680971)
        ·
          refine ⟨950330570969763025112521457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633553713979842016741680971 950330570969763025112521457)
          ·
            refine ⟨712747928227322268834391093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950330570969763025112521457 712747928227322268834391093)
            ·
              refine ⟨66820118271311462703224165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 712747928227322268834391093 66820118271311462703224165)
              ·
                refine ⟨12528772175870899256854531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66820118271311462703224165 12528772175870899256854531)
                ·
                  refine ⟨18793158263806348885281797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12528772175870899256854531 18793158263806348885281797)
                  ·
                    refine ⟨3523717174463690415990337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18793158263806348885281797 3523717174463690415990337)
                    ·
                      refine ⟨2642787880847767811992753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523717174463690415990337 2642787880847767811992753)
                      ·
                        rfl

theorem cell23_5146811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 4, 2].length) (baseStart_5146811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146811 prefixEnd_5146811 := by exact prefixLift 5146811
  have htrace : WordTrace (prefixWord ++ tailWord_5146811) baseStart_5146811 baseEnd_5146811 := by
    simpa [prefixWord, tailWord_5146811, baseEnd_5146811] using wordTrace_append hprefix tailTrace_5146811
  have hstable : (prefixWord ++ tailWord_5146811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146811).length < 2 ^ (prefixWord ++ tailWord_5146811).sum := by decide
  have hdescent : baseEnd_5146811 < baseStart_5146811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146838 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_5146838 : Nat := 118140960795 + 5146838 * 2 ^ 59
def prefixEnd_5146838 : Nat := 4983230072969 + 3 ^ 40 * 5146838 * 2
def baseEnd_5146838 : Nat := 880933914941813068785043

theorem tailTrace_5146838 : CollatzResearch.WordTrace tailWord_5146838 prefixEnd_5146838 880933914941813068785043 := by
  unfold tailWord_5146838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732537732993275674622073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125147069151928273862635445 11732537732993275674622073)
  ·
    refine ⟨8799403299744956755966555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11732537732993275674622073 8799403299744956755966555)
    ·
      refine ⟨13199104949617435133949833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8799403299744956755966555 13199104949617435133949833)
      ·
        refine ⟨9899328712213076350462375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13199104949617435133949833 9899328712213076350462375)
        ·
          refine ⟨14848993068319614525693563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9899328712213076350462375 14848993068319614525693563)
          ·
            refine ⟨22273489602479421788540345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14848993068319614525693563 22273489602479421788540345)
            ·
              refine ⟨16705117201859566341405259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22273489602479421788540345 16705117201859566341405259)
              ·
                refine ⟨25057675802789349512107889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16705117201859566341405259 25057675802789349512107889)
                ·
                  refine ⟨18793256852092012134080917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25057675802789349512107889 18793256852092012134080917)
                  ·
                    refine ⟨880933914941813068785043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18793256852092012134080917 880933914941813068785043)
                    ·
                      rfl

theorem cell23_5146838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_5146838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146838 prefixEnd_5146838 := by exact prefixLift 5146838
  have htrace : WordTrace (prefixWord ++ tailWord_5146838) baseStart_5146838 baseEnd_5146838 := by
    simpa [prefixWord, tailWord_5146838, baseEnd_5146838] using wordTrace_append hprefix tailTrace_5146838
  have hstable : (prefixWord ++ tailWord_5146838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146838).length < 2 ^ (prefixWord ++ tailWord_5146838).sum := by decide
  have hdescent : baseEnd_5146838 < baseStart_5146838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146845 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_5146845 : Nat := 118140960795 + 5146845 * 2 ^ 59
def prefixEnd_5146845 : Nat := 4983230072969 + 3 ^ 40 * 5146845 * 2
def baseEnd_5146845 : Nat := 2642805339190020678967597

theorem tailTrace_5146845 : CollatzResearch.WordTrace tailWord_5146845 prefixEnd_5146845 2642805339190020678967597 := by
  unfold tailWord_5146845
  simp only [CollatzResearch.WordTrace]
  refine ⟨187720859038867050989457989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125147239359244700659638659 187720859038867050989457989)
  ·
    refine ⟨35197661069787572060523373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187720859038867050989457989 35197661069787572060523373)
    ·
      refine ⟨13199122901170339522696265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35197661069787572060523373 13199122901170339522696265)
      ·
        refine ⟨9899342175877754642022199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13199122901170339522696265 9899342175877754642022199)
        ·
          refine ⟨14849013263816631963033299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9899342175877754642022199 14849013263816631963033299)
          ·
            refine ⟨22273519895724947944549949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14849013263816631963033299 22273519895724947944549949)
            ·
              refine ⟨8352569960896855479206231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22273519895724947944549949 8352569960896855479206231)
              ·
                refine ⟨12528854941345283218809347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8352569960896855479206231 12528854941345283218809347)
                ·
                  refine ⟨18793282412017924828214021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12528854941345283218809347 18793282412017924828214021)
                  ·
                    refine ⟨3523740452253360905290129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18793282412017924828214021 3523740452253360905290129)
                    ·
                      refine ⟨2642805339190020678967597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3523740452253360905290129 2642805339190020678967597)
                      ·
                        rfl

theorem cell23_5146845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_5146845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146845 prefixEnd_5146845 := by exact prefixLift 5146845
  have htrace : WordTrace (prefixWord ++ tailWord_5146845) baseStart_5146845 baseEnd_5146845 := by
    simpa [prefixWord, tailWord_5146845, baseEnd_5146845] using wordTrace_append hprefix tailTrace_5146845
  have hstable : (prefixWord ++ tailWord_5146845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146845).length < 2 ^ (prefixWord ++ tailWord_5146845).sum := by decide
  have hdescent : baseEnd_5146845 < baseStart_5146845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146864 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 6, 5]
def baseStart_5146864 : Nat := 118140960795 + 5146864 * 2 ^ 59
def prefixEnd_5146864 : Nat := 4983230072969 + 3 ^ 40 * 5146864 * 2
def baseEnd_5146864 : Nat := 880938365107485368210003

theorem tailTrace_5146864 : CollatzResearch.WordTrace tailWord_5146864 prefixEnd_5146864 880938365107485368210003 := by
  unfold tailWord_5146864
  simp only [CollatzResearch.WordTrace]
  refine ⟨93860776012899108617199823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125147701350532144822933097 93860776012899108617199823)
  ·
    refine ⟨140791164019348662925799735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93860776012899108617199823 140791164019348662925799735)
    ·
      refine ⟨211186746029022994388699603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140791164019348662925799735 211186746029022994388699603)
      ·
        refine ⟨316780119043534491583049405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211186746029022994388699603 316780119043534491583049405)
        ·
          refine ⟨118792544641325434343643527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316780119043534491583049405 118792544641325434343643527)
          ·
            refine ⟨178188816961988151515465291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118792544641325434343643527 178188816961988151515465291)
            ·
              refine ⟨267283225442982227273197937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178188816961988151515465291 267283225442982227273197937)
              ·
                refine ⟨200462419082236670454898453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267283225442982227273197937 200462419082236670454898453)
                ·
                  refine ⟨9396675894479843927573365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 200462419082236670454898453 9396675894479843927573365)
                  ·
                    refine ⟨880938365107485368210003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9396675894479843927573365 880938365107485368210003)
                    ·
                      rfl

theorem cell23_5146864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_5146864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146864 prefixEnd_5146864 := by exact prefixLift 5146864
  have htrace : WordTrace (prefixWord ++ tailWord_5146864) baseStart_5146864 baseEnd_5146864 := by
    simpa [prefixWord, tailWord_5146864, baseEnd_5146864] using wordTrace_append hprefix tailTrace_5146864
  have hstable : (prefixWord ++ tailWord_5146864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146864).length < 2 ^ (prefixWord ++ tailWord_5146864).sum := by decide
  have hdescent : baseEnd_5146864 < baseStart_5146864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146881 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 2, 5]
def baseStart_5146881 : Nat := 118140960795 + 5146881 * 2 ^ 59
def prefixEnd_5146881 : Nat := 4983230072969 + 3 ^ 40 * 5146881 * 2
def baseEnd_5146881 : Nat := 880941274831194179372477

theorem tailTrace_5146881 : CollatzResearch.WordTrace tailWord_5146881 prefixEnd_5146881 880941274831194179372477 := by
  unfold tailWord_5146881
  simp only [CollatzResearch.WordTrace]
  refine ⟨187722172066736629137768497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125148114711157752758512331 187722172066736629137768497)
  ·
    refine ⟨140791629050052471853326373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187722172066736629137768497 140791629050052471853326373)
    ·
      refine ⟨26398430446884838472498695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140791629050052471853326373 26398430446884838472498695)
      ·
        refine ⟨39597645670327257708748043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26398430446884838472498695 39597645670327257708748043)
        ·
          refine ⟨59396468505490886563122065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39597645670327257708748043 59396468505490886563122065)
          ·
            refine ⟨44547351379118164922341549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59396468505490886563122065 44547351379118164922341549)
            ·
              refine ⟨16705256767169311845878081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44547351379118164922341549 16705256767169311845878081)
              ·
                refine ⟨12528942575376983884408561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16705256767169311845878081 12528942575376983884408561)
                ·
                  refine ⟨9396706931532737913306421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12528942575376983884408561 9396706931532737913306421)
                  ·
                    refine ⟨880941274831194179372477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9396706931532737913306421 880941274831194179372477)
                    ·
                      rfl

theorem cell23_5146881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_5146881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146881 prefixEnd_5146881 := by exact prefixLift 5146881
  have htrace : WordTrace (prefixWord ++ tailWord_5146881) baseStart_5146881 baseEnd_5146881 := by
    simpa [prefixWord, tailWord_5146881, baseEnd_5146881] using wordTrace_append hprefix tailTrace_5146881
  have hstable : (prefixWord ++ tailWord_5146881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146881).length < 2 ^ (prefixWord ++ tailWord_5146881).sum := by decide
  have hdescent : baseEnd_5146881 < baseStart_5146881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146924 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 10]
def baseStart_5146924 : Nat := 118140960795 + 5146924 * 2 ^ 59
def prefixEnd_5146924 : Nat := 4983230072969 + 3 ^ 40 * 5146924 * 2
def baseEnd_5146924 : Nat := 293649544906858429986637

theorem tailTrace_5146924 : CollatzResearch.WordTrace tailWord_5146924 prefixEnd_5146924 293649544906858429986637 := by
  unfold tailWord_5146924
  simp only [CollatzResearch.WordTrace]
  refine ⟨93861870202790423740791913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125149160270387231654389217 93861870202790423740791913)
  ·
    refine ⟨70396402652092817805593935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93861870202790423740791913 70396402652092817805593935)
    ·
      refine ⟨105594603978139226708390903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70396402652092817805593935 105594603978139226708390903)
      ·
        refine ⟨158391905967208840062586355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105594603978139226708390903 158391905967208840062586355)
        ·
          refine ⟨237587858950813260093879533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158391905967208840062586355 237587858950813260093879533)
          ·
            refine ⟨89095447106554972535204825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237587858950813260093879533 89095447106554972535204825)
            ·
              refine ⟨66821585329916229401403619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89095447106554972535204825 66821585329916229401403619)
              ·
                refine ⟨100232377994874344102105429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66821585329916229401403619 100232377994874344102105429)
                ·
                  refine ⟨293649544906858429986637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 100232377994874344102105429 293649544906858429986637)
                  ·
                    rfl

theorem cell23_5146924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_5146924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146924 prefixEnd_5146924 := by exact prefixLift 5146924
  have htrace : WordTrace (prefixWord ++ tailWord_5146924) baseStart_5146924 baseEnd_5146924 := by
    simpa [prefixWord, tailWord_5146924, baseEnd_5146924] using wordTrace_append hprefix tailTrace_5146924
  have hstable : (prefixWord ++ tailWord_5146924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146924).length < 2 ^ (prefixWord ++ tailWord_5146924).sum := by decide
  have hdescent : baseEnd_5146924 < baseStart_5146924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146938 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_5146938 : Nat := 118140960795 + 5146938 * 2 ^ 59
def prefixEnd_5146938 : Nat := 4983230072969 + 3 ^ 40 * 5146938 * 2
def baseEnd_5146938 : Nat := 2642853092890888815104669

theorem tailTrace_5146938 : CollatzResearch.WordTrace tailWord_5146938 prefixEnd_5146938 2642853092890888815104669 := by
  unfold tailWord_5146938
  simp only [CollatzResearch.WordTrace]
  refine ⟨46931062756882531968148367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125149500685020085248395645 46931062756882531968148367)
  ·
    refine ⟨70396594135323797952222551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46931062756882531968148367 70396594135323797952222551)
    ·
      refine ⟨105594891202985696928333827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70396594135323797952222551 105594891202985696928333827)
      ·
        refine ⟨158392336804478545392500741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105594891202985696928333827 158392336804478545392500741)
        ·
          refine ⟨29698563150839727261093889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158392336804478545392500741 29698563150839727261093889)
          ·
            refine ⟨22273922363129795445820417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29698563150839727261093889 22273922363129795445820417)
            ·
              refine ⟨16705441772347346584365313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22273922363129795445820417 16705441772347346584365313)
              ·
                refine ⟨12529081329260509938273985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16705441772347346584365313 12529081329260509938273985)
                ·
                  refine ⟨9396810996945382453705489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12529081329260509938273985 9396810996945382453705489)
                  ·
                    refine ⟨7047608247709036840279117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9396810996945382453705489 7047608247709036840279117)
                    ·
                      refine ⟨2642853092890888815104669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7047608247709036840279117 2642853092890888815104669)
                      ·
                        rfl

theorem cell23_5146938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_5146938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146938 prefixEnd_5146938 := by exact prefixLift 5146938
  have htrace : WordTrace (prefixWord ++ tailWord_5146938) baseStart_5146938 baseEnd_5146938 := by
    simpa [prefixWord, tailWord_5146938, baseEnd_5146938] using wordTrace_append hprefix tailTrace_5146938
  have hstable : (prefixWord ++ tailWord_5146938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146938).length < 2 ^ (prefixWord ++ tailWord_5146938).sum := by decide
  have hdescent : baseEnd_5146938 < baseStart_5146938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5146991 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_5146991 : Nat := 118140960795 + 5146991 * 2 ^ 59
def prefixEnd_5146991 : Nat := 4983230072969 + 3 ^ 40 * 5146991 * 2
def baseEnd_5146991 : Nat := 2642880307365577107741925

theorem tailTrace_5146991 : CollatzResearch.WordTrace tailWord_5146991 prefixEnd_5146991 2642880307365577107741925 := by
  unfold tailWord_5146991
  simp only [CollatzResearch.WordTrace]
  refine ⟨187726184096338117924272827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125150789397558745282848551 187726184096338117924272827)
  ·
    refine ⟨281589276144507176886409241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187726184096338117924272827 281589276144507176886409241)
    ·
      refine ⟨211191957108380382664806931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281589276144507176886409241 211191957108380382664806931)
      ·
        refine ⟨316787935662570573997210397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211191957108380382664806931 316787935662570573997210397)
        ·
          refine ⟨118795475873463965248953899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316787935662570573997210397 118795475873463965248953899)
          ·
            refine ⟨178193213810195947873430849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118795475873463965248953899 178193213810195947873430849)
            ·
              refine ⟨133644910357646960905073137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178193213810195947873430849 133644910357646960905073137)
              ·
                refine ⟨100233682768235220678804853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133644910357646960905073137 100233682768235220678804853)
                ·
                  refine ⟨9396907759522051938637955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100233682768235220678804853 9396907759522051938637955)
                  ·
                    refine ⟨14095361639283077907956933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9396907759522051938637955 14095361639283077907956933)
                    ·
                      refine ⟨2642880307365577107741925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14095361639283077907956933 2642880307365577107741925)
                      ·
                        rfl

theorem cell23_5146991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_5146991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5146991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5146991 prefixEnd_5146991 := by exact prefixLift 5146991
  have htrace : WordTrace (prefixWord ++ tailWord_5146991) baseStart_5146991 baseEnd_5146991 := by
    simpa [prefixWord, tailWord_5146991, baseEnd_5146991] using wordTrace_append hprefix tailTrace_5146991
  have hstable : (prefixWord ++ tailWord_5146991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5146991).length < 2 ^ (prefixWord ++ tailWord_5146991).sum := by decide
  have hdescent : baseEnd_5146991 < baseStart_5146991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5146991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147030 : List Nat := [5, 3, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_5147030 : Nat := 118140960795 + 5147030 * 2 ^ 59
def prefixEnd_5147030 : Nat := 4983230072969 + 3 ^ 40 * 5147030 * 2
def baseEnd_5147030 : Nat := 880966777703700818384749

theorem tailTrace_5147030 : CollatzResearch.WordTrace tailWord_5147030 prefixEnd_5147030 880966777703700818384749 := by
  unfold tailWord_5147030
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732975408949801724058909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125151737695464551723295029 11732975408949801724058909)
  ·
    refine ⟨4399865778356175646522091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11732975408949801724058909 4399865778356175646522091)
    ·
      refine ⟨6599798667534263469783137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399865778356175646522091 6599798667534263469783137)
      ·
        refine ⟨4949849000650697602337353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6599798667534263469783137 4949849000650697602337353)
        ·
          refine ⟨3712386750488023201753015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4949849000650697602337353 3712386750488023201753015)
          ·
            refine ⟨5568580125732034802629523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712386750488023201753015 5568580125732034802629523)
            ·
              refine ⟨8352870188598052203944285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568580125732034802629523 8352870188598052203944285)
              ·
                refine ⟨3132326320724269576479107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8352870188598052203944285 3132326320724269576479107)
                ·
                  refine ⟨4698489481086404364718661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132326320724269576479107 4698489481086404364718661)
                  ·
                    refine ⟨880966777703700818384749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4698489481086404364718661 880966777703700818384749)
                    ·
                      rfl

theorem cell23_5147030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_5147030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147030 prefixEnd_5147030 := by exact prefixLift 5147030
  have htrace : WordTrace (prefixWord ++ tailWord_5147030) baseStart_5147030 baseEnd_5147030 := by
    simpa [prefixWord, tailWord_5147030, baseEnd_5147030] using wordTrace_append hprefix tailTrace_5147030
  have hstable : (prefixWord ++ tailWord_5147030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147030).length < 2 ^ (prefixWord ++ tailWord_5147030).sum := by decide
  have hdescent : baseEnd_5147030 < baseStart_5147030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147048 : List Nat := [2, 1, 6, 1, 1, 1, 11]
def baseStart_5147048 : Nat := 118140960795 + 5147048 * 2 ^ 59
def prefixEnd_5147048 : Nat := 4983230072969 + 3 ^ 40 * 5147048 * 2
def baseEnd_5147048 : Nat := 32628513281023251663323

theorem tailTrace_5147048 : CollatzResearch.WordTrace tailWord_5147048 prefixEnd_5147048 32628513281023251663323 := by
  unfold tailWord_5147048
  simp only [CollatzResearch.WordTrace]
  refine ⟨93864131528565808329548899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125152175371421077772731865 93864131528565808329548899)
  ·
    refine ⟨140796197292848712494323349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93864131528565808329548899 140796197292848712494323349)
    ·
      refine ⟨6599821748102283398171407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140796197292848712494323349 6599821748102283398171407)
      ·
        refine ⟨9899732622153425097257111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6599821748102283398171407 9899732622153425097257111)
        ·
          refine ⟨14849598933230137645885667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9899732622153425097257111 14849598933230137645885667)
          ·
            refine ⟨22274398399845206468828501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14849598933230137645885667 22274398399845206468828501)
            ·
              refine ⟨32628513281023251663323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22274398399845206468828501 32628513281023251663323)
              ·
                rfl

theorem cell23_5147048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 11].length) (baseStart_5147048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147048 prefixEnd_5147048 := by exact prefixLift 5147048
  have htrace : WordTrace (prefixWord ++ tailWord_5147048) baseStart_5147048 baseEnd_5147048 := by
    simpa [prefixWord, tailWord_5147048, baseEnd_5147048] using wordTrace_append hprefix tailTrace_5147048
  have hstable : (prefixWord ++ tailWord_5147048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147048).length < 2 ^ (prefixWord ++ tailWord_5147048).sum := by decide
  have hdescent : baseEnd_5147048 < baseStart_5147048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147109 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_5147109 : Nat := 118140960795 + 5147109 * 2 ^ 59
def prefixEnd_5147109 : Nat := 4983230072969 + 3 ^ 40 * 5147109 * 2
def baseEnd_5147109 : Nat := 2642940898082807646066383

theorem tailTrace_5147109 : CollatzResearch.WordTrace tailWord_5147109 prefixEnd_5147109 2642940898082807646066383 := by
  unfold tailWord_5147109
  simp only [CollatzResearch.WordTrace]
  refine ⟨187730487909910624077068381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125153658606607082718045587 187730487909910624077068381)
  ·
    refine ⟨70398932966216484028900643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187730487909910624077068381 70398932966216484028900643)
    ·
      refine ⟨105598399449324726043350965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70398932966216484028900643 105598399449324726043350965)
      ·
        refine ⟨9899849948374193066564153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105598399449324726043350965 9899849948374193066564153)
        ·
          refine ⟨7424887461280644799923115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9899849948374193066564153 7424887461280644799923115)
          ·
            refine ⟨11137331191920967199884673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7424887461280644799923115 11137331191920967199884673)
            ·
              refine ⟨8352998393940725399913505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11137331191920967199884673 8352998393940725399913505)
              ·
                refine ⟨6264748795455544049935129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8352998393940725399913505 6264748795455544049935129)
                ·
                  refine ⟨4698561596591658037451347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6264748795455544049935129 4698561596591658037451347)
                  ·
                    refine ⟨7047842394887487056177021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4698561596591658037451347 7047842394887487056177021)
                    ·
                      refine ⟨2642940898082807646066383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7047842394887487056177021 2642940898082807646066383)
                      ·
                        rfl

theorem cell23_5147109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_5147109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147109 prefixEnd_5147109 := by exact prefixLift 5147109
  have htrace : WordTrace (prefixWord ++ tailWord_5147109) baseStart_5147109 baseEnd_5147109 := by
    simpa [prefixWord, tailWord_5147109, baseEnd_5147109] using wordTrace_append hprefix tailTrace_5147109
  have hstable : (prefixWord ++ tailWord_5147109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147109).length < 2 ^ (prefixWord ++ tailWord_5147109).sum := by decide
  have hdescent : baseEnd_5147109 < baseStart_5147109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147128 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_5147128 : Nat := 118140960795 + 5147128 * 2 ^ 59
def prefixEnd_5147128 : Nat := 4983230072969 + 3 ^ 40 * 5147128 * 2
def baseEnd_5147128 : Nat := 2642950654215243071728795

theorem tailTrace_5147128 : CollatzResearch.WordTrace tailWord_5147128 prefixEnd_5147128 2642950654215243071728795 := by
  unfold tailWord_5147128
  simp only [CollatzResearch.WordTrace]
  refine ⟨93865590448420895161005019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125154120597894526881340025 93865590448420895161005019)
  ·
    refine ⟨140798385672631342741507529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93865590448420895161005019 140798385672631342741507529)
    ·
      refine ⟨105598789254473507056130647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140798385672631342741507529 105598789254473507056130647)
      ·
        refine ⟨158398183881710260584195971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105598789254473507056130647 158398183881710260584195971)
        ·
          refine ⟨237597275822565390876293957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158398183881710260584195971 237597275822565390876293957)
          ·
            refine ⟨44549489216731010789305117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237597275822565390876293957 44549489216731010789305117)
            ·
              refine ⟨16706058456274129045989419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44549489216731010789305117 16706058456274129045989419)
              ·
                refine ⟨25059087684411193568984129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16706058456274129045989419 25059087684411193568984129)
                ·
                  refine ⟨18794315763308395176738097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25059087684411193568984129 18794315763308395176738097)
                  ·
                    refine ⟨14095736822481296382553573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18794315763308395176738097 14095736822481296382553573)
                    ·
                      refine ⟨2642950654215243071728795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14095736822481296382553573 2642950654215243071728795)
                      ·
                        rfl

theorem cell23_5147128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_5147128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147128 prefixEnd_5147128 := by exact prefixLift 5147128
  have htrace : WordTrace (prefixWord ++ tailWord_5147128) baseStart_5147128 baseEnd_5147128 := by
    simpa [prefixWord, tailWord_5147128, baseEnd_5147128] using wordTrace_append hprefix tailTrace_5147128
  have hstable : (prefixWord ++ tailWord_5147128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147128).length < 2 ^ (prefixWord ++ tailWord_5147128).sum := by decide
  have hdescent : baseEnd_5147128 < baseStart_5147128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147155 : List Nat := [1, 1, 1, 2, 1, 5, 4, 3, 5]
def baseStart_5147155 : Nat := 118140960795 + 5147155 * 2 ^ 59
def prefixEnd_5147155 : Nat := 4983230072969 + 3 ^ 40 * 5147155 * 2
def baseEnd_5147155 : Nat := 293662724243657162899019

theorem tailTrace_5147155 : CollatzResearch.WordTrace tailWord_5147155 prefixEnd_5147155 293662724243657162899019 := by
  unfold tailWord_5147155
  simp only [CollatzResearch.WordTrace]
  refine ⟨187732165667743973933242919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125154777111829315955495279 187732165667743973933242919)
  ·
    refine ⟨281598248501615960899864379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187732165667743973933242919 281598248501615960899864379)
    ·
      refine ⟨422397372752423941349796569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281598248501615960899864379 422397372752423941349796569)
      ·
        refine ⟨316798029564317956012347427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422397372752423941349796569 316798029564317956012347427)
        ·
          refine ⟨475197044346476934018521141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316798029564317956012347427 475197044346476934018521141)
          ·
            refine ⟨44549722907482212564236357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 475197044346476934018521141 44549722907482212564236357)
            ·
              refine ⟨8353073045152914855794317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44549722907482212564236357 8353073045152914855794317)
              ·
                refine ⟨3132402391932343070922869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8353073045152914855794317 3132402391932343070922869)
                ·
                  refine ⟨293662724243657162899019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3132402391932343070922869 293662724243657162899019)
                  ·
                    rfl

theorem cell23_5147155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 5].length) (baseStart_5147155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147155 prefixEnd_5147155 := by exact prefixLift 5147155
  have htrace : WordTrace (prefixWord ++ tailWord_5147155) baseStart_5147155 baseEnd_5147155 := by
    simpa [prefixWord, tailWord_5147155, baseEnd_5147155] using wordTrace_append hprefix tailTrace_5147155
  have hstable : (prefixWord ++ tailWord_5147155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147155).length < 2 ^ (prefixWord ++ tailWord_5147155).sum := by decide
  have hdescent : baseEnd_5147155 < baseStart_5147155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147165 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_5147165 : Nat := 118140960795 + 5147165 * 2 ^ 59
def prefixEnd_5147165 : Nat := 4983230072969 + 3 ^ 40 * 5147165 * 2
def baseEnd_5147165 : Nat := 2642969652999459426966125

theorem tailTrace_5147165 : CollatzResearch.WordTrace tailWord_5147165 prefixEnd_5147165 2642969652999459426966125 := by
  unfold tailWord_5147165
  simp only [CollatzResearch.WordTrace]
  refine ⟨187732530397707745641106949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125155020265138497094071299 187732530397707745641106949)
  ·
    refine ⟨35199849449570202307707553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187732530397707745641106949 35199849449570202307707553)
    ·
      refine ⟨26399887087177651730780665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35199849449570202307707553 26399887087177651730780665)
      ·
        refine ⟨19799915315383238798085499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26399887087177651730780665 19799915315383238798085499)
        ·
          refine ⟨29699872973074858197128249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19799915315383238798085499 29699872973074858197128249)
          ·
            refine ⟨22274904729806143647846187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29699872973074858197128249 22274904729806143647846187)
            ·
              refine ⟨33412357094709215471769281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22274904729806143647846187 33412357094709215471769281)
              ·
                refine ⟨25059267821031911603826961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33412357094709215471769281 25059267821031911603826961)
                ·
                  refine ⟨18794450865773933702870221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25059267821031911603826961 18794450865773933702870221)
                  ·
                    refine ⟨7047919074665225138576333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18794450865773933702870221 7047919074665225138576333)
                    ·
                      refine ⟨2642969652999459426966125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7047919074665225138576333 2642969652999459426966125)
                      ·
                        rfl

theorem cell23_5147165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_5147165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147165 prefixEnd_5147165 := by exact prefixLift 5147165
  have htrace : WordTrace (prefixWord ++ tailWord_5147165) baseStart_5147165 baseEnd_5147165 := by
    simpa [prefixWord, tailWord_5147165, baseEnd_5147165] using wordTrace_append hprefix tailTrace_5147165
  have hstable : (prefixWord ++ tailWord_5147165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147165).length < 2 ^ (prefixWord ++ tailWord_5147165).sum := by decide
  have hdescent : baseEnd_5147165 < baseStart_5147165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147172 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 7]
def baseStart_5147172 : Nat := 118140960795 + 5147172 * 2 ^ 59
def prefixEnd_5147172 : Nat := 4983230072969 + 3 ^ 40 * 5147172 * 2
def baseEnd_5147172 : Nat := 293663694151560099953177

theorem tailTrace_5147172 : CollatzResearch.WordTrace tailWord_5147172 prefixEnd_5147172 293663694151560099953177 := by
  unfold tailWord_5147172
  simp only [CollatzResearch.WordTrace]
  refine ⟨93866392854341192918305885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125155190472454923891074513 93866392854341192918305885)
  ·
    refine ⟨35199897320377947344364707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93866392854341192918305885 35199897320377947344364707)
    ·
      refine ⟨52799845980566921016547061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35199897320377947344364707 52799845980566921016547061)
      ·
        refine ⟨4949985560678148845301287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52799845980566921016547061 4949985560678148845301287)
        ·
          refine ⟨7424978341017223267951931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949985560678148845301287 7424978341017223267951931)
          ·
            refine ⟨11137467511525834901927897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7424978341017223267951931 11137467511525834901927897)
            ·
              refine ⟨8353100633644376176445923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11137467511525834901927897 8353100633644376176445923)
              ·
                refine ⟨12529650950466564264668885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8353100633644376176445923 12529650950466564264668885)
                ·
                  refine ⟨293663694151560099953177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12529650950466564264668885 293663694151560099953177)
                  ·
                    rfl

theorem cell23_5147172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_5147172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147172 prefixEnd_5147172 := by exact prefixLift 5147172
  have htrace : WordTrace (prefixWord ++ tailWord_5147172) baseStart_5147172 baseEnd_5147172 := by
    simpa [prefixWord, tailWord_5147172, baseEnd_5147172] using wordTrace_append hprefix tailTrace_5147172
  have hstable : (prefixWord ++ tailWord_5147172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147172).length < 2 ^ (prefixWord ++ tailWord_5147172).sum := by decide
  have hdescent : baseEnd_5147172 < baseStart_5147172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147206 : List Nat := [6, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_5147206 : Nat := 118140960795 + 5147206 * 2 ^ 59
def prefixEnd_5147206 : Nat := 4983230072969 + 3 ^ 40 * 5147206 * 2
def baseEnd_5147206 : Nat := 293665633967365974061493

theorem tailTrace_5147206 : CollatzResearch.WordTrace tailWord_5147206 prefixEnd_5147206 293665633967365974061493 := by
  unfold tailWord_5147206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866688305954975301354671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125156017193706139762232981 5866688305954975301354671)
  ·
    refine ⟨8800032458932462952032007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5866688305954975301354671 8800032458932462952032007)
    ·
      refine ⟨13200048688398694428048011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8800032458932462952032007 13200048688398694428048011)
      ·
        refine ⟨19800073032598041642072017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13200048688398694428048011 19800073032598041642072017)
        ·
          refine ⟨14850054774448531231554013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19800073032598041642072017 14850054774448531231554013)
          ·
            refine ⟨5568770540418199211832755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14850054774448531231554013 5568770540418199211832755)
            ·
              refine ⟨8353155810627298817749133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568770540418199211832755 8353155810627298817749133)
              ·
                refine ⟨3132433428985237056655925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8353155810627298817749133 3132433428985237056655925)
                ·
                  refine ⟨293665633967365974061493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3132433428985237056655925 293665633967365974061493)
                  ·
                    rfl

theorem cell23_5147206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_5147206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147206 prefixEnd_5147206 := by exact prefixLift 5147206
  have htrace : WordTrace (prefixWord ++ tailWord_5147206) baseStart_5147206 baseEnd_5147206 := by
    simpa [prefixWord, tailWord_5147206, baseEnd_5147206] using wordTrace_append hprefix tailTrace_5147206
  have hstable : (prefixWord ++ tailWord_5147206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147206).length < 2 ^ (prefixWord ++ tailWord_5147206).sum := by decide
  have hdescent : baseEnd_5147206 < baseStart_5147206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147232 : List Nat := [2, 1, 1, 3, 2, 1, 2, 6, 1, 4]
def baseStart_5147232 : Nat := 118140960795 + 5147232 * 2 ^ 59
def prefixEnd_5147232 : Nat := 4983230072969 + 3 ^ 40 * 5147232 * 2
def baseEnd_5147232 : Nat := 881001352067770221609439

theorem tailTrace_5147232 : CollatzResearch.WordTrace tailWord_5147232 prefixEnd_5147232 881001352067770221609439 := by
  unfold tailWord_5147232
  simp only [CollatzResearch.WordTrace]
  refine ⟨93867487044232508041897975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125156649392310010722530633 93867487044232508041897975)
  ·
    refine ⟨140801230566348762062846963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93867487044232508041897975 140801230566348762062846963)
    ·
      refine ⟨211201845849523143094270445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140801230566348762062846963 211201845849523143094270445)
      ·
        refine ⟨79200692193571178660351417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211201845849523143094270445 79200692193571178660351417)
        ·
          refine ⟨59400519145178383995263563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79200692193571178660351417 59400519145178383995263563)
          ·
            refine ⟨89100778717767575992895345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59400519145178383995263563 89100778717767575992895345)
            ·
              refine ⟨66825584038325681994671509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89100778717767575992895345 66825584038325681994671509)
              ·
                refine ⟨3132449251796516343500227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66825584038325681994671509 3132449251796516343500227)
                ·
                  refine ⟨4698673877694774515250341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132449251796516343500227 4698673877694774515250341)
                  ·
                    refine ⟨881001352067770221609439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4698673877694774515250341 881001352067770221609439)
                    ·
                      rfl

theorem cell23_5147232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 4].length) (baseStart_5147232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147232 prefixEnd_5147232 := by exact prefixLift 5147232
  have htrace : WordTrace (prefixWord ++ tailWord_5147232) baseStart_5147232 baseEnd_5147232 := by
    simpa [prefixWord, tailWord_5147232, baseEnd_5147232] using wordTrace_append hprefix tailTrace_5147232
  have hstable : (prefixWord ++ tailWord_5147232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147232).length < 2 ^ (prefixWord ++ tailWord_5147232).sum := by decide
  have hdescent : baseEnd_5147232 < baseStart_5147232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147289 : List Nat := [1, 2, 1, 2, 1, 2, 5, 4, 1, 1, 3]
def baseStart_5147289 : Nat := 118140960795 + 5147289 * 2 ^ 59
def prefixEnd_5147289 : Nat := 4983230072969 + 3 ^ 40 * 5147289 * 2
def baseEnd_5147289 : Nat := 2643033324600616941815555

theorem tailTrace_5147289 : CollatzResearch.WordTrace tailWord_5147289 prefixEnd_5147289 2643033324600616941815555 := by
  unfold tailWord_5147289
  simp only [CollatzResearch.WordTrace]
  refine ⟨187737053049258514818620921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125158035366172343212413947 187737053049258514818620921)
  ·
    refine ⟨140802789786943886113965691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187737053049258514818620921 140802789786943886113965691)
    ·
      refine ⟨211204184680415829170948537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140802789786943886113965691 211204184680415829170948537)
      ·
        refine ⟨158403138510311871878211403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211204184680415829170948537 158403138510311871878211403)
        ·
          refine ⟨237604707765467807817317105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158403138510311871878211403 237604707765467807817317105)
          ·
            refine ⟨178203530824100855862987829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237604707765467807817317105 178203530824100855862987829)
            ·
              refine ⟨16706581014759455237155109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178203530824100855862987829 16706581014759455237155109)
              ·
                refine ⟨3132483940267397856966583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16706581014759455237155109 3132483940267397856966583)
                ·
                  refine ⟨4698725910401096785449875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132483940267397856966583 4698725910401096785449875)
                  ·
                    refine ⟨7048088865601645178174813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4698725910401096785449875 7048088865601645178174813)
                    ·
                      refine ⟨2643033324600616941815555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7048088865601645178174813 2643033324600616941815555)
                      ·
                        rfl

theorem cell23_5147289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_5147289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147289 prefixEnd_5147289 := by exact prefixLift 5147289
  have htrace : WordTrace (prefixWord ++ tailWord_5147289) baseStart_5147289 baseEnd_5147289 := by
    simpa [prefixWord, tailWord_5147289, baseEnd_5147289] using wordTrace_append hprefix tailTrace_5147289
  have hstable : (prefixWord ++ tailWord_5147289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147289).length < 2 ^ (prefixWord ++ tailWord_5147289).sum := by decide
  have hdescent : baseEnd_5147289 < baseStart_5147289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147349 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5147349 : Nat := 118140960795 + 5147349 * 2 ^ 59
def prefixEnd_5147349 : Nat := 4983230072969 + 3 ^ 40 * 5147349 * 2
def baseEnd_5147349 : Nat := 2643064133439886707065279

theorem tailTrace_5147349 : CollatzResearch.WordTrace tailWord_5147349 prefixEnd_5147349 2643064133439886707065279 := by
  unfold tailWord_5147349
  simp only [CollatzResearch.WordTrace]
  refine ⟨187739241429041145065805101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125159494286027430043870067 187739241429041145065805101)
  ·
    refine ⟨70402215535890429399676913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187739241429041145065805101 70402215535890429399676913)
    ·
      refine ⟨52801661651917822049757685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70402215535890429399676913 52801661651917822049757685)
      ·
        refine ⟨4950155779867295817164783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52801661651917822049757685 4950155779867295817164783)
        ·
          refine ⟨7425233669800943725747175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950155779867295817164783 7425233669800943725747175)
          ·
            refine ⟨11137850504701415588620763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7425233669800943725747175 11137850504701415588620763)
            ·
              refine ⟨16706775757052123382931145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11137850504701415588620763 16706775757052123382931145)
              ·
                refine ⟨12530081817789092537198359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16706775757052123382931145 12530081817789092537198359)
                ·
                  refine ⟨18795122726683638805797539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12530081817789092537198359 18795122726683638805797539)
                  ·
                    refine ⟨28192684090025458208696309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18795122726683638805797539 28192684090025458208696309)
                    ·
                      refine ⟨2643064133439886707065279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28192684090025458208696309 2643064133439886707065279)
                      ·
                        rfl

theorem cell23_5147349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5147349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147349 prefixEnd_5147349 := by exact prefixLift 5147349
  have htrace : WordTrace (prefixWord ++ tailWord_5147349) baseStart_5147349 baseEnd_5147349 := by
    simpa [prefixWord, tailWord_5147349, baseEnd_5147349] using wordTrace_append hprefix tailTrace_5147349
  have hstable : (prefixWord ++ tailWord_5147349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147349).length < 2 ^ (prefixWord ++ tailWord_5147349).sum := by decide
  have hdescent : baseEnd_5147349 < baseStart_5147349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147375 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_5147375 : Nat := 118140960795 + 5147375 * 2 ^ 59
def prefixEnd_5147375 : Nat := 4983230072969 + 3 ^ 40 * 5147375 * 2
def baseEnd_5147375 : Nat := 2643077483936903605340159

theorem tailTrace_5147375 : CollatzResearch.WordTrace tailWord_5147375 prefixEnd_5147375 2643077483936903605340159 := by
  unfold tailWord_5147375
  simp only [CollatzResearch.WordTrace]
  refine ⟨187740189726946951506251579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125160126484631301004167719 187740189726946951506251579)
  ·
    refine ⟨281610284590420427259377369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187740189726946951506251579 281610284590420427259377369)
    ·
      refine ⟨211207713442815320444533027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281610284590420427259377369 211207713442815320444533027)
      ·
        refine ⟨316811570164222980666799541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211207713442815320444533027 316811570164222980666799541)
        ·
          refine ⟨29701084702895904437512457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 316811570164222980666799541 29701084702895904437512457)
          ·
            refine ⟨22275813527171928328134343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29701084702895904437512457 22275813527171928328134343)
            ·
              refine ⟨33413720290757892492201515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22275813527171928328134343 33413720290757892492201515)
              ·
                refine ⟨50120580436136838738302273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33413720290757892492201515 50120580436136838738302273)
                ·
                  refine ⟨37590435327102629053726705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50120580436136838738302273 37590435327102629053726705)
                  ·
                    refine ⟨28192826495326971790295029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37590435327102629053726705 28192826495326971790295029)
                    ·
                      refine ⟨2643077483936903605340159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28192826495326971790295029 2643077483936903605340159)
                      ·
                        rfl

theorem cell23_5147375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_5147375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147375 prefixEnd_5147375 := by exact prefixLift 5147375
  have htrace : WordTrace (prefixWord ++ tailWord_5147375) baseStart_5147375 baseEnd_5147375 := by
    simpa [prefixWord, tailWord_5147375, baseEnd_5147375] using wordTrace_append hprefix tailTrace_5147375
  have hstable : (prefixWord ++ tailWord_5147375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147375).length < 2 ^ (prefixWord ++ tailWord_5147375).sum := by decide
  have hdescent : baseEnd_5147375 < baseStart_5147375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147389 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_5147389 : Nat := 118140960795 + 5147389 * 2 ^ 59
def prefixEnd_5147389 : Nat := 4983230072969 + 3 ^ 40 * 5147389 * 2
def baseEnd_5147389 : Nat := 2643084672666066550565095

theorem tailTrace_5147389 : CollatzResearch.WordTrace tailWord_5147389 prefixEnd_5147389 2643084672666066550565095 := by
  unfold tailWord_5147389
  simp only [CollatzResearch.WordTrace]
  refine ⟨187740700348896231897261221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125160466899264154598174147 187740700348896231897261221)
  ·
    refine ⟨35201381315418043480736479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187740700348896231897261221 35201381315418043480736479)
    ·
      refine ⟨52802071973127065221104719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35201381315418043480736479 52802071973127065221104719)
      ·
        refine ⟨79203107959690597831657079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52802071973127065221104719 79203107959690597831657079)
        ·
          refine ⟨118804661939535896747485619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79203107959690597831657079 118804661939535896747485619)
          ·
            refine ⟨178206992909303845121228429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118804661939535896747485619 178206992909303845121228429)
            ·
              refine ⟨66827622340988941920460661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178206992909303845121228429 66827622340988941920460661)
              ·
                refine ⟨6265089594467713305043187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66827622340988941920460661 6265089594467713305043187)
                ·
                  refine ⟨9397634391701569957564781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265089594467713305043187 9397634391701569957564781)
                  ·
                    refine ⟨3524112896888088734086793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9397634391701569957564781 3524112896888088734086793)
                    ·
                      refine ⟨2643084672666066550565095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524112896888088734086793 2643084672666066550565095)
                      ·
                        rfl

theorem cell23_5147389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_5147389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147389 prefixEnd_5147389 := by exact prefixLift 5147389
  have htrace : WordTrace (prefixWord ++ tailWord_5147389) baseStart_5147389 baseEnd_5147389 := by
    simpa [prefixWord, tailWord_5147389, baseEnd_5147389] using wordTrace_append hprefix tailTrace_5147389
  have hstable : (prefixWord ++ tailWord_5147389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147389).length < 2 ^ (prefixWord ++ tailWord_5147389).sum := by decide
  have hdescent : baseEnd_5147389 < baseStart_5147389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147425 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 9]
def baseStart_5147425 : Nat := 118140960795 + 5147425 * 2 ^ 59
def prefixEnd_5147425 : Nat := 4983230072969 + 3 ^ 40 * 5147425 * 2
def baseEnd_5147425 : Nat := 293678128663292045523881

theorem tailTrace_5147425 : CollatzResearch.WordTrace tailWord_5147425 prefixEnd_5147425 293678128663292045523881 := by
  unfold tailWord_5147425
  simp only [CollatzResearch.WordTrace]
  refine ⟨187742013376765810045571729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125161342251177206697047819 187742013376765810045571729)
  ·
    refine ⟨140806510032574357534178797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187742013376765810045571729 140806510032574357534178797)
    ·
      refine ⟨52802441262215384075317049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140806510032574357534178797 52802441262215384075317049)
      ·
        refine ⟨39601830946661538056487787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52802441262215384075317049 39601830946661538056487787)
        ·
          refine ⟨59402746419992307084731681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39601830946661538056487787 59402746419992307084731681)
          ·
            refine ⟨44552059814994230313548761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59402746419992307084731681 44552059814994230313548761)
            ·
              refine ⟨33414044861245672735161571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44552059814994230313548761 33414044861245672735161571)
              ·
                refine ⟨50121067291868509102742357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33414044861245672735161571 50121067291868509102742357)
                ·
                  refine ⟨293678128663292045523881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50121067291868509102742357 293678128663292045523881)
                  ·
                    rfl

theorem cell23_5147425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 9].length) (baseStart_5147425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147425 prefixEnd_5147425 := by exact prefixLift 5147425
  have htrace : WordTrace (prefixWord ++ tailWord_5147425) baseStart_5147425 baseEnd_5147425 := by
    simpa [prefixWord, tailWord_5147425, baseEnd_5147425] using wordTrace_append hprefix tailTrace_5147425
  have hstable : (prefixWord ++ tailWord_5147425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147425).length < 2 ^ (prefixWord ++ tailWord_5147425).sum := by decide
  have hdescent : baseEnd_5147425 < baseStart_5147425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147452 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_5147452 : Nat := 118140960795 + 5147452 * 2 ^ 59
def prefixEnd_5147452 : Nat := 4983230072969 + 3 ^ 40 * 5147452 * 2
def baseEnd_5147452 : Nat := 2643117021947299804077305

theorem tailTrace_5147452 : CollatzResearch.WordTrace tailWord_5147452 prefixEnd_5147452 2643117021947299804077305 := by
  unfold tailWord_5147452
  simp only [CollatzResearch.WordTrace]
  refine ⟨93871499073833996828402305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125161998765111995771203073 93871499073833996828402305)
  ·
    refine ⟨70403624305375497621301729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93871499073833996828402305 70403624305375497621301729)
    ·
      refine ⟨52802718229031623215976297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70403624305375497621301729 52802718229031623215976297)
      ·
        refine ⟨39602038671773717411982223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52802718229031623215976297 39602038671773717411982223)
        ·
          refine ⟨59403058007660576117973335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39602038671773717411982223 59403058007660576117973335)
          ·
            refine ⟨89104587011490864176960003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59403058007660576117973335 89104587011490864176960003)
            ·
              refine ⟨133656880517236296265440005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89104587011490864176960003 133656880517236296265440005)
              ·
                refine ⟨25060665096981805549770001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133656880517236296265440005 25060665096981805549770001)
                ·
                  refine ⟨18795498822736354162327501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25060665096981805549770001 18795498822736354162327501)
                  ·
                    refine ⟨7048312058526132810872813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18795498822736354162327501 7048312058526132810872813)
                    ·
                      refine ⟨2643117021947299804077305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7048312058526132810872813 2643117021947299804077305)
                      ·
                        rfl

theorem cell23_5147452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_5147452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147452 prefixEnd_5147452 := by exact prefixLift 5147452
  have htrace : WordTrace (prefixWord ++ tailWord_5147452) baseStart_5147452 baseEnd_5147452 := by
    simpa [prefixWord, tailWord_5147452, baseEnd_5147452] using wordTrace_append hprefix tailTrace_5147452
  have hstable : (prefixWord ++ tailWord_5147452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147452).length < 2 ^ (prefixWord ++ tailWord_5147452).sum := by decide
  have hdescent : baseEnd_5147452 < baseStart_5147452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147532 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 6]
def baseStart_5147532 : Nat := 118140960795 + 5147532 * 2 ^ 59
def prefixEnd_5147532 : Nat := 4983230072969 + 3 ^ 40 * 5147532 * 2
def baseEnd_5147532 : Nat := 293684233377739943452993

theorem tailTrace_5147532 : CollatzResearch.WordTrace tailWord_5147532 prefixEnd_5147532 293684233377739943452993 := by
  unfold tailWord_5147532
  simp only [CollatzResearch.WordTrace]
  refine ⟨93872957993689083659858425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125163943991585444879811233 93872957993689083659858425)
  ·
    refine ⟨70404718495266812744893819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93872957993689083659858425 70404718495266812744893819)
    ·
      refine ⟨105607077742900219117340729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70404718495266812744893819 105607077742900219117340729)
      ·
        refine ⟨79205308307175164338005547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105607077742900219117340729 79205308307175164338005547)
        ·
          refine ⟨118807962460762746507008321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79205308307175164338005547 118807962460762746507008321)
          ·
            refine ⟨89105971845572059880256241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118807962460762746507008321 89105971845572059880256241)
            ·
              refine ⟨66829478884179044910192181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89105971845572059880256241 66829478884179044910192181)
              ·
                refine ⟨6265263645391785460330517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66829478884179044910192181 6265263645391785460330517)
                ·
                  refine ⟨293684233377739943452993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6265263645391785460330517 293684233377739943452993)
                  ·
                    rfl

theorem cell23_5147532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_5147532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147532 prefixEnd_5147532 := by exact prefixLift 5147532
  have htrace : WordTrace (prefixWord ++ tailWord_5147532) baseStart_5147532 baseEnd_5147532 := by
    simpa [prefixWord, tailWord_5147532, baseEnd_5147532] using wordTrace_append hprefix tailTrace_5147532
  have hstable : (prefixWord ++ tailWord_5147532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147532).length < 2 ^ (prefixWord ++ tailWord_5147532).sum := by decide
  have hdescent : baseEnd_5147532 < baseStart_5147532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147553 : List Nat := [1, 2, 3, 4, 1, 1, 3, 3, 1, 4]
def baseStart_5147553 : Nat := 118140960795 + 5147553 * 2 ^ 59
def prefixEnd_5147553 : Nat := 4983230072969 + 3 ^ 40 * 5147553 * 2
def baseEnd_5147553 : Nat := 881056294497801302971447

theorem tailTrace_5147553 : CollatzResearch.WordTrace tailWord_5147553 prefixEnd_5147553 881056294497801302971447 := by
  unfold tailWord_5147553
  simp only [CollatzResearch.WordTrace]
  refine ⟨187746681920302087906231313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125164454613534725270820875 187746681920302087906231313)
  ·
    refine ⟨140810011440226565929673485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187746681920302087906231313 140810011440226565929673485)
    ·
      refine ⟨52803754290084962223627557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140810011440226565929673485 52803754290084962223627557)
      ·
        refine ⟨9900703929390930416930167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52803754290084962223627557 9900703929390930416930167)
        ·
          refine ⟨14851055894086395625395251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9900703929390930416930167 14851055894086395625395251)
          ·
            refine ⟨22276583841129593438092877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14851055894086395625395251 22276583841129593438092877)
            ·
              refine ⟨8353718940423597539284829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22276583841129593438092877 8353718940423597539284829)
              ·
                refine ⟨3132644602658849077231811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8353718940423597539284829 3132644602658849077231811)
                ·
                  refine ⟨4698966903988273615847717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132644602658849077231811 4698966903988273615847717)
                  ·
                    refine ⟨881056294497801302971447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4698966903988273615847717 881056294497801302971447)
                    ·
                      rfl

theorem cell23_5147553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_5147553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147553 prefixEnd_5147553 := by exact prefixLift 5147553
  have htrace : WordTrace (prefixWord ++ tailWord_5147553) baseStart_5147553 baseEnd_5147553 := by
    simpa [prefixWord, tailWord_5147553, baseEnd_5147553] using wordTrace_append hprefix tailTrace_5147553
  have hstable : (prefixWord ++ tailWord_5147553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147553).length < 2 ^ (prefixWord ++ tailWord_5147553).sum := by decide
  have hdescent : baseEnd_5147553 < baseStart_5147553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147576 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_5147576 : Nat := 118140960795 + 5147576 * 2 ^ 59
def prefixEnd_5147576 : Nat := 4983230072969 + 3 ^ 40 * 5147576 * 2
def baseEnd_5147576 : Nat := 2643180693548457318926735

theorem tailTrace_5147576 : CollatzResearch.WordTrace tailWord_5147576 prefixEnd_5147576 2643180693548457318926735 := by
  unfold tailWord_5147576
  simp only [CollatzResearch.WordTrace]
  refine ⟨93873760399609381417159291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125165013866145841889545721 93873760399609381417159291)
  ·
    refine ⟨140810640599414072125738937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93873760399609381417159291 140810640599414072125738937)
    ·
      refine ⟨105607980449560554094304203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140810640599414072125738937 105607980449560554094304203)
      ·
        refine ⟨158411970674340831141456305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105607980449560554094304203 158411970674340831141456305)
        ·
          refine ⟨118808978005755623356092229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158411970674340831141456305 118808978005755623356092229)
          ·
            refine ⟨22276683376079179379267293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118808978005755623356092229 22276683376079179379267293)
            ·
              refine ⟨8353756266029692267225235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22276683376079179379267293 8353756266029692267225235)
              ·
                refine ⟨12530634399044538400837853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8353756266029692267225235 12530634399044538400837853)
                ·
                  refine ⟨4698987899641701900314195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12530634399044538400837853 4698987899641701900314195)
                  ·
                    refine ⟨7048481849462552850471293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4698987899641701900314195 7048481849462552850471293)
                    ·
                      refine ⟨2643180693548457318926735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7048481849462552850471293 2643180693548457318926735)
                      ·
                        rfl

theorem cell23_5147576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_5147576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147576 prefixEnd_5147576 := by exact prefixLift 5147576
  have htrace : WordTrace (prefixWord ++ tailWord_5147576) baseStart_5147576 baseEnd_5147576 := by
    simpa [prefixWord, tailWord_5147576, baseEnd_5147576] using wordTrace_append hprefix tailTrace_5147576
  have hstable : (prefixWord ++ tailWord_5147576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147576).length < 2 ^ (prefixWord ++ tailWord_5147576).sum := by decide
  have hdescent : baseEnd_5147576 < baseStart_5147576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147597 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5147597 : Nat := 118140960795 + 5147597 * 2 ^ 59
def prefixEnd_5147597 : Nat := 4983230072969 + 3 ^ 40 * 5147597 * 2
def baseEnd_5147597 : Nat := 2643191476642201736764139

theorem tailTrace_5147597 : CollatzResearch.WordTrace tailWord_5147597 prefixEnd_5147597 2643191476642201736764139 := by
  unfold tailWord_5147597
  simp only [CollatzResearch.WordTrace]
  refine ⟨187748286732142683420833045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125165524488095122280555363 187748286732142683420833045)
  ·
    refine ⟨8800700940569188285351549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187748286732142683420833045 8800700940569188285351549)
    ·
      refine ⟨3300262852713445607006831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8800700940569188285351549 3300262852713445607006831)
      ·
        refine ⟨4950394279070168410510247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300262852713445607006831 4950394279070168410510247)
        ·
          refine ⟨7425591418605252615765371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950394279070168410510247 7425591418605252615765371)
          ·
            refine ⟨11138387127907878923648057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7425591418605252615765371 11138387127907878923648057)
            ·
              refine ⟨8353790345930909192736043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11138387127907878923648057 8353790345930909192736043)
              ·
                refine ⟨12530685518896363789104065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8353790345930909192736043 12530685518896363789104065)
                ·
                  refine ⟨9398014139172272841828049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12530685518896363789104065 9398014139172272841828049)
                  ·
                    refine ⟨7048510604379204631371037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9398014139172272841828049 7048510604379204631371037)
                    ·
                      refine ⟨2643191476642201736764139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7048510604379204631371037 2643191476642201736764139)
                      ·
                        rfl

theorem cell23_5147597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5147597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147597 prefixEnd_5147597 := by exact prefixLift 5147597
  have htrace : WordTrace (prefixWord ++ tailWord_5147597) baseStart_5147597 baseEnd_5147597 := by
    simpa [prefixWord, tailWord_5147597, baseEnd_5147597] using wordTrace_append hprefix tailTrace_5147597
  have hstable : (prefixWord ++ tailWord_5147597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147597).length < 2 ^ (prefixWord ++ tailWord_5147597).sum := by decide
  have hdescent : baseEnd_5147597 < baseStart_5147597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147599 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_5147599 : Nat := 118140960795 + 5147599 * 2 ^ 59
def prefixEnd_5147599 : Nat := 4983230072969 + 3 ^ 40 * 5147599 * 2
def baseEnd_5147599 : Nat := 2643192503603510728939129

theorem tailTrace_5147599 : CollatzResearch.WordTrace tailWord_5147599 prefixEnd_5147599 2643192503603510728939129 := by
  unfold tailWord_5147599
  simp only [CollatzResearch.WordTrace]
  refine ⟨187748359678135437762405851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125165573118756958508270567 187748359678135437762405851)
  ·
    refine ⟨281622539517203156643608777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187748359678135437762405851 281622539517203156643608777)
    ·
      refine ⟨211216904637902367482706583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281622539517203156643608777 211216904637902367482706583)
      ·
        refine ⟨316825356956853551224059875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211216904637902367482706583 316825356956853551224059875)
        ·
          refine ⟨475238035435280326836089813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316825356956853551224059875 475238035435280326836089813)
          ·
            refine ⟨11138391455514382660220855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 475238035435280326836089813 11138391455514382660220855)
            ·
              refine ⟨16707587183271573990331283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11138391455514382660220855 16707587183271573990331283)
              ·
                refine ⟨25061380774907360985496925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16707587183271573990331283 25061380774907360985496925)
                ·
                  refine ⟨9398017790590260369561347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25061380774907360985496925 9398017790590260369561347)
                  ·
                    refine ⟨14097026685885390554342021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9398017790590260369561347 14097026685885390554342021)
                    ·
                      refine ⟨2643192503603510728939129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14097026685885390554342021 2643192503603510728939129)
                      ·
                        rfl

theorem cell23_5147599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_5147599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147599 prefixEnd_5147599 := by exact prefixLift 5147599
  have htrace : WordTrace (prefixWord ++ tailWord_5147599) baseStart_5147599 baseEnd_5147599 := by
    simpa [prefixWord, tailWord_5147599, baseEnd_5147599] using wordTrace_append hprefix tailTrace_5147599
  have hstable : (prefixWord ++ tailWord_5147599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147599).length < 2 ^ (prefixWord ++ tailWord_5147599).sum := by decide
  have hdescent : baseEnd_5147599 < baseStart_5147599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147609 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 1, 6]
def baseStart_5147609 : Nat := 118140960795 + 5147609 * 2 ^ 59
def prefixEnd_5147609 : Nat := 4983230072969 + 3 ^ 40 * 5147609 * 2
def baseEnd_5147609 : Nat := 881065879470018563271361

theorem tailTrace_5147609 : CollatzResearch.WordTrace tailWord_5147609 prefixEnd_5147609 881065879470018563271361 := by
  unfold tailWord_5147609
  simp only [CollatzResearch.WordTrace]
  refine ⟨187748724408099209470269881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125165816272066139646846587 187748724408099209470269881)
  ·
    refine ⟨140811543306074407102702411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187748724408099209470269881 140811543306074407102702411)
    ·
      refine ⟨211217314959111610654053617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140811543306074407102702411 211217314959111610654053617)
      ·
        refine ⟨158412986219333707990540213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211217314959111610654053617 158412986219333707990540213)
        ·
          refine ⟨14851217458062535124113145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158412986219333707990540213 14851217458062535124113145)
          ·
            refine ⟨11138413093546901343084859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14851217458062535124113145 11138413093546901343084859)
            ·
              refine ⟨16707619640320352014627289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11138413093546901343084859 16707619640320352014627289)
              ·
                refine ⟨12530714730240264010970467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16707619640320352014627289 12530714730240264010970467)
                ·
                  refine ⟨18796072095360396016455701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12530714730240264010970467 18796072095360396016455701)
                  ·
                    refine ⟨881065879470018563271361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18796072095360396016455701 881065879470018563271361)
                    ·
                      rfl

theorem cell23_5147609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_5147609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147609 prefixEnd_5147609 := by exact prefixLift 5147609
  have htrace : WordTrace (prefixWord ++ tailWord_5147609) baseStart_5147609 baseEnd_5147609 := by
    simpa [prefixWord, tailWord_5147609, baseEnd_5147609] using wordTrace_append hprefix tailTrace_5147609
  have hstable : (prefixWord ++ tailWord_5147609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147609).length < 2 ^ (prefixWord ++ tailWord_5147609).sum := by decide
  have hdescent : baseEnd_5147609 < baseStart_5147609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147613 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_5147613 : Nat := 118140960795 + 5147613 * 2 ^ 59
def prefixEnd_5147613 : Nat := 4983230072969 + 3 ^ 40 * 5147613 * 2
def baseEnd_5147613 : Nat := 881066564110891224721355

theorem tailTrace_5147613 : CollatzResearch.WordTrace tailWord_5147613 prefixEnd_5147613 881066564110891224721355 := by
  unfold tailWord_5147613
  simp only [CollatzResearch.WordTrace]
  refine ⟨187748870300084718153415493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125165913533389812102276995 187748870300084718153415493)
  ·
    refine ⟨35202913181265884653765405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187748870300084718153415493 35202913181265884653765405)
    ·
      refine ⟨13201092442974706745162027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35202913181265884653765405 13201092442974706745162027)
      ·
        refine ⟨19801638664462060117743041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13201092442974706745162027 19801638664462060117743041)
        ·
          refine ⟨14851228998346545088307281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19801638664462060117743041 14851228998346545088307281)
          ·
            refine ⟨11138421748759908816230461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14851228998346545088307281 11138421748759908816230461)
            ·
              refine ⟨4176908155784965806086423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11138421748759908816230461 4176908155784965806086423)
              ·
                refine ⟨6265362233677448709129635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176908155784965806086423 6265362233677448709129635)
                ·
                  refine ⟨9398043350516173063694453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265362233677448709129635 9398043350516173063694453)
                  ·
                    refine ⟨881066564110891224721355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9398043350516173063694453 881066564110891224721355)
                    ·
                      rfl

theorem cell23_5147613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_5147613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147613 prefixEnd_5147613 := by exact prefixLift 5147613
  have htrace : WordTrace (prefixWord ++ tailWord_5147613) baseStart_5147613 baseEnd_5147613 := by
    simpa [prefixWord, tailWord_5147613, baseEnd_5147613] using wordTrace_append hprefix tailTrace_5147613
  have hstable : (prefixWord ++ tailWord_5147613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147613).length < 2 ^ (prefixWord ++ tailWord_5147613).sum := by decide
  have hdescent : baseEnd_5147613 < baseStart_5147613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147626 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_5147626 : Nat := 118140960795 + 5147626 * 2 ^ 59
def prefixEnd_5147626 : Nat := 4983230072969 + 3 ^ 40 * 5147626 * 2
def baseEnd_5147626 : Nat := 881068789193727374433835

theorem tailTrace_5147626 : CollatzResearch.WordTrace tailWord_5147626 prefixEnd_5147626 881068789193727374433835 := by
  unfold tailWord_5147626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46937336112259405343409683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125166229632691747582425821 46937336112259405343409683)
  ·
    refine ⟨70406004168389108015114525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46937336112259405343409683 70406004168389108015114525)
    ·
      refine ⟨26402251563145915505667947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70406004168389108015114525 26402251563145915505667947)
      ·
        refine ⟨39603377344718873258501921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26402251563145915505667947 39603377344718873258501921)
        ·
          refine ⟨29702533008539154943876441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39603377344718873258501921 29702533008539154943876441)
          ·
            refine ⟨22276899756404366207907331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29702533008539154943876441 22276899756404366207907331)
            ·
              refine ⟨33415349634606549311860997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22276899756404366207907331 33415349634606549311860997)
              ·
                refine ⟨6265378056488727995973937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33415349634606549311860997 6265378056488727995973937)
                ·
                  refine ⟨4699033542366545996980453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265378056488727995973937 4699033542366545996980453)
                  ·
                    refine ⟨881068789193727374433835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699033542366545996980453 881068789193727374433835)
                    ·
                      rfl

theorem cell23_5147626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_5147626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147626 prefixEnd_5147626 := by exact prefixLift 5147626
  have htrace : WordTrace (prefixWord ++ tailWord_5147626) baseStart_5147626 baseEnd_5147626 := by
    simpa [prefixWord, tailWord_5147626, baseEnd_5147626] using wordTrace_append hprefix tailTrace_5147626
  have hstable : (prefixWord ++ tailWord_5147626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147626).length < 2 ^ (prefixWord ++ tailWord_5147626).sum := by decide
  have hdescent : baseEnd_5147626 < baseStart_5147626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147642 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_5147642 : Nat := 118140960795 + 5147642 * 2 ^ 59
def prefixEnd_5147642 : Nat := 4983230072969 + 3 ^ 40 * 5147642 * 2
def baseEnd_5147642 : Nat := 2643214583271654060701431

theorem tailTrace_5147642 : CollatzResearch.WordTrace tailWord_5147642 prefixEnd_5147642 2643214583271654060701431 := by
  unfold tailWord_5147642
  simp only [CollatzResearch.WordTrace]
  refine ⟨46937482004244914026555295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125166618677986437404147453 46937482004244914026555295)
  ·
    refine ⟨70406223006367371039832943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46937482004244914026555295 70406223006367371039832943)
    ·
      refine ⟨105609334509551056559749415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70406223006367371039832943 105609334509551056559749415)
      ·
        refine ⟨158414001764326584839624123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105609334509551056559749415 158414001764326584839624123)
        ·
          refine ⟨237621002646489877259436185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158414001764326584839624123 237621002646489877259436185)
          ·
            refine ⟨178215751984867407944577139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237621002646489877259436185 178215751984867407944577139)
            ·
              refine ⟨267323627977301111916865709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178215751984867407944577139 267323627977301111916865709)
              ·
                refine ⟨100246360491487916968824641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267323627977301111916865709 100246360491487916968824641)
                ·
                  refine ⟨75184770368615937726618481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100246360491487916968824641 75184770368615937726618481)
                  ·
                    refine ⟨56388577776461953294963861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75184770368615937726618481 56388577776461953294963861)
                    ·
                      refine ⟨2643214583271654060701431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56388577776461953294963861 2643214583271654060701431)
                      ·
                        rfl

theorem cell23_5147642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_5147642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147642 prefixEnd_5147642 := by exact prefixLift 5147642
  have htrace : WordTrace (prefixWord ++ tailWord_5147642) baseStart_5147642 baseEnd_5147642 := by
    simpa [prefixWord, tailWord_5147642, baseEnd_5147642] using wordTrace_append hprefix tailTrace_5147642
  have hstable : (prefixWord ++ tailWord_5147642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147642).length < 2 ^ (prefixWord ++ tailWord_5147642).sum := by decide
  have hdescent : baseEnd_5147642 < baseStart_5147642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147683 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 3]
def baseStart_5147683 : Nat := 118140960795 + 5147683 * 2 ^ 59
def prefixEnd_5147683 : Nat := 4983230072969 + 3 ^ 40 * 5147683 * 2
def baseEnd_5147683 : Nat := 2643235635978488400288743

theorem tailTrace_5147683 : CollatzResearch.WordTrace tailWord_5147683 prefixEnd_5147683 2643235635978488400288743 := by
  unfold tailWord_5147683
  simp only [CollatzResearch.WordTrace]
  refine ⟨187751423409831120108463703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125167615606554080072309135 187751423409831120108463703)
  ·
    refine ⟨281627135114746680162695555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187751423409831120108463703 281627135114746680162695555)
    ·
      refine ⟨422440702672120020244043333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281627135114746680162695555 422440702672120020244043333)
      ·
        refine ⟨79207631751022503795758125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 422440702672120020244043333 79207631751022503795758125)
        ·
          refine ⟨29702861906633438923409297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79207631751022503795758125 29702861906633438923409297)
          ·
            refine ⟨22277146429975079192556973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29702861906633438923409297 22277146429975079192556973)
            ·
              refine ⟨8353929911240654697208865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22277146429975079192556973 8353929911240654697208865)
              ·
                refine ⟨6265447433430491022906649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8353929911240654697208865 6265447433430491022906649)
                ·
                  refine ⟨4699085575072868267179987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265447433430491022906649 4699085575072868267179987)
                  ·
                    refine ⟨7048628362609302400769981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699085575072868267179987 7048628362609302400769981)
                    ·
                      refine ⟨2643235635978488400288743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7048628362609302400769981 2643235635978488400288743)
                      ·
                        rfl

theorem cell23_5147683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_5147683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147683 prefixEnd_5147683 := by exact prefixLift 5147683
  have htrace : WordTrace (prefixWord ++ tailWord_5147683) baseStart_5147683 baseEnd_5147683 := by
    simpa [prefixWord, tailWord_5147683, baseEnd_5147683] using wordTrace_append hprefix tailTrace_5147683
  have hstable : (prefixWord ++ tailWord_5147683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147683).length < 2 ^ (prefixWord ++ tailWord_5147683).sum := by decide
  have hdescent : baseEnd_5147683 < baseStart_5147683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147700 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5147700 : Nat := 118140960795 + 5147700 * 2 ^ 59
def prefixEnd_5147700 : Nat := 4983230072969 + 3 ^ 40 * 5147700 * 2
def baseEnd_5147700 : Nat := 2643244365149614833776165

theorem tailTrace_5147700 : CollatzResearch.WordTrace tailWord_5147700 prefixEnd_5147700 2643244365149614833776165 := by
  unfold tailWord_5147700
  simp only [CollatzResearch.WordTrace]
  refine ⟨93876021725384766005916277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125168028967179688007888369 93876021725384766005916277)
  ·
    refine ⟨8800877036754821813054651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93876021725384766005916277 8800877036754821813054651)
    ·
      refine ⟨13201315555132232719581977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8800877036754821813054651 13201315555132232719581977)
      ·
        refine ⟨9900986666349174539686483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13201315555132232719581977 9900986666349174539686483)
        ·
          refine ⟨14851479999523761809529725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9900986666349174539686483 14851479999523761809529725)
          ·
            refine ⟨5569304999821410678573647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14851479999523761809529725 5569304999821410678573647)
            ·
              refine ⟨8353957499732116017860471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569304999821410678573647 8353957499732116017860471)
              ·
                refine ⟨12530936249598174026790707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8353957499732116017860471 12530936249598174026790707)
                ·
                  refine ⟨18796404374397261040186061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12530936249598174026790707 18796404374397261040186061)
                  ·
                    refine ⟨7048651640398972890069773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18796404374397261040186061 7048651640398972890069773)
                    ·
                      refine ⟨2643244365149614833776165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7048651640398972890069773 2643244365149614833776165)
                      ·
                        rfl

theorem cell23_5147700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5147700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147700 prefixEnd_5147700 := by exact prefixLift 5147700
  have htrace : WordTrace (prefixWord ++ tailWord_5147700) baseStart_5147700 baseEnd_5147700 := by
    simpa [prefixWord, tailWord_5147700, baseEnd_5147700] using wordTrace_append hprefix tailTrace_5147700
  have hstable : (prefixWord ++ tailWord_5147700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147700).length < 2 ^ (prefixWord ++ tailWord_5147700).sum := by decide
  have hdescent : baseEnd_5147700 < baseStart_5147700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147710 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_5147710 : Nat := 118140960795 + 5147710 * 2 ^ 59
def prefixEnd_5147710 : Nat := 4983230072969 + 3 ^ 40 * 5147710 * 2
def baseEnd_5147710 : Nat := 2643249499956159794651119

theorem tailTrace_5147710 : CollatzResearch.WordTrace tailWord_5147710 prefixEnd_5147710 2643249499956159794651119 := by
  unfold tailWord_5147710
  simp only [CollatzResearch.WordTrace]
  refine ⟨23469051022591662964962073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125168272120488869146464389 23469051022591662964962073)
  ·
    refine ⟨17601788266943747223721555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23469051022591662964962073 17601788266943747223721555)
    ·
      refine ⟨26402682400415620835582333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17601788266943747223721555 26402682400415620835582333)
      ·
        refine ⟨9901005900155857813343375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26402682400415620835582333 9901005900155857813343375)
        ·
          refine ⟨14851508850233786720015063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9901005900155857813343375 14851508850233786720015063)
          ·
            refine ⟨22277263275350680080022595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14851508850233786720015063 22277263275350680080022595)
            ·
              refine ⟨33415894913026020120033893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22277263275350680080022595 33415894913026020120033893)
              ·
                refine ⟨6265480296192378772506355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33415894913026020120033893 6265480296192378772506355)
                ·
                  refine ⟨9398220444288568158759533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265480296192378772506355 9398220444288568158759533)
                  ·
                    refine ⟨3524332666608213059534825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9398220444288568158759533 3524332666608213059534825)
                    ·
                      refine ⟨2643249499956159794651119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524332666608213059534825 2643249499956159794651119)
                      ·
                        rfl

theorem cell23_5147710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_5147710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147710 prefixEnd_5147710 := by exact prefixLift 5147710
  have htrace : WordTrace (prefixWord ++ tailWord_5147710) baseStart_5147710 baseEnd_5147710 := by
    simpa [prefixWord, tailWord_5147710, baseEnd_5147710] using wordTrace_append hprefix tailTrace_5147710
  have hstable : (prefixWord ++ tailWord_5147710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147710).length < 2 ^ (prefixWord ++ tailWord_5147710).sum := by decide
  have hdescent : baseEnd_5147710 < baseStart_5147710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147740 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_5147740 : Nat := 118140960795 + 5147740 * 2 ^ 59
def prefixEnd_5147740 : Nat := 4983230072969 + 3 ^ 40 * 5147740 * 2
def baseEnd_5147740 : Nat := 2643264904375794677275981

theorem tailTrace_5147740 : CollatzResearch.WordTrace tailWord_5147740 prefixEnd_5147740 2643264904375794677275981 := by
  unfold tailWord_5147740
  simp only [CollatzResearch.WordTrace]
  refine ⟨93876751185312309421644337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125169001580416412562192449 93876751185312309421644337)
  ·
    refine ⟨70407563388984232066233253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93876751185312309421644337 70407563388984232066233253)
    ·
      refine ⟨13201418135434543512418735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70407563388984232066233253 13201418135434543512418735)
      ·
        refine ⟨19802127203151815268628103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13201418135434543512418735 19802127203151815268628103)
        ·
          refine ⟨29703190804727722902942155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19802127203151815268628103 29703190804727722902942155)
          ·
            refine ⟨44554786207091584354413233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29703190804727722902942155 44554786207091584354413233)
            ·
              refine ⟨33416089655318688265809925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44554786207091584354413233 33416089655318688265809925)
              ·
                refine ⟨6265516810372254049839361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33416089655318688265809925 6265516810372254049839361)
                ·
                  refine ⟨4699137607779190537379521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265516810372254049839361 4699137607779190537379521)
                  ·
                    refine ⟨3524353205834392903034641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4699137607779190537379521 3524353205834392903034641)
                    ·
                      refine ⟨2643264904375794677275981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524353205834392903034641 2643264904375794677275981)
                      ·
                        rfl

theorem cell23_5147740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_5147740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147740 prefixEnd_5147740 := by exact prefixLift 5147740
  have htrace : WordTrace (prefixWord ++ tailWord_5147740) baseStart_5147740 baseEnd_5147740 := by
    simpa [prefixWord, tailWord_5147740, baseEnd_5147740] using wordTrace_append hprefix tailTrace_5147740
  have hstable : (prefixWord ++ tailWord_5147740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147740).length < 2 ^ (prefixWord ++ tailWord_5147740).sum := by decide
  have hdescent : baseEnd_5147740 < baseStart_5147740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147757 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_5147757 : Nat := 118140960795 + 5147757 * 2 ^ 59
def prefixEnd_5147757 : Nat := 4983230072969 + 3 ^ 40 * 5147757 * 2
def baseEnd_5147757 : Nat := 2643273633546921110763403

theorem tailTrace_5147757 : CollatzResearch.WordTrace tailWord_5147757 prefixEnd_5147757 2643273633546921110763403 := by
  unfold tailWord_5147757
  simp only [CollatzResearch.WordTrace]
  refine ⟨187754122411563030746657525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125169414941042020497771683 187754122411563030746657525)
  ·
    refine ⟨17601948976084034132499143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187754122411563030746657525 17601948976084034132499143)
    ·
      refine ⟨26402923464126051198748715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17601948976084034132499143 26402923464126051198748715)
      ·
        refine ⟨39604385196189076798123073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26402923464126051198748715 39604385196189076798123073)
        ·
          refine ⟨29703288897141807598592305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39604385196189076798123073 29703288897141807598592305)
          ·
            refine ⟨22277466672856355698944229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29703288897141807598592305 22277466672856355698944229)
            ·
              refine ⟨4177025001160566693552043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22277466672856355698944229 4177025001160566693552043)
              ·
                refine ⟨6265537501740850040328065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177025001160566693552043 6265537501740850040328065)
                ·
                  refine ⟨4699153126305637530246049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265537501740850040328065 4699153126305637530246049)
                  ·
                    refine ⟨3524364844729228147684537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4699153126305637530246049 3524364844729228147684537)
                    ·
                      refine ⟨2643273633546921110763403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524364844729228147684537 2643273633546921110763403)
                      ·
                        rfl

theorem cell23_5147757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_5147757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147757 prefixEnd_5147757 := by exact prefixLift 5147757
  have htrace : WordTrace (prefixWord ++ tailWord_5147757) baseStart_5147757 baseEnd_5147757 := by
    simpa [prefixWord, tailWord_5147757, baseEnd_5147757] using wordTrace_append hprefix tailTrace_5147757
  have hstable : (prefixWord ++ tailWord_5147757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147757).length < 2 ^ (prefixWord ++ tailWord_5147757).sum := by decide
  have hdescent : baseEnd_5147757 < baseStart_5147757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147759 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 4, 5]
def baseStart_5147759 : Nat := 118140960795 + 5147759 * 2 ^ 59
def prefixEnd_5147759 : Nat := 4983230072969 + 3 ^ 40 * 5147759 * 2
def baseEnd_5147759 : Nat := 881091553502743367646131

theorem tailTrace_5147759 : CollatzResearch.WordTrace tailWord_5147759 prefixEnd_5147759 881091553502743367646131 := by
  unfold tailWord_5147759
  simp only [CollatzResearch.WordTrace]
  refine ⟨187754195357555785088230331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125169463571703856725486887 187754195357555785088230331)
  ·
    refine ⟨281631293036333677632345497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187754195357555785088230331 281631293036333677632345497)
    ·
      refine ⟨211223469777250258224259123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281631293036333677632345497 211223469777250258224259123)
      ·
        refine ⟨316835204665875387336388685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211223469777250258224259123 316835204665875387336388685)
        ·
          refine ⟨118813201749703270251145757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316835204665875387336388685 118813201749703270251145757)
          ·
            refine ⟨44554950656138726344179659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118813201749703270251145757 44554950656138726344179659)
            ·
              refine ⟨66832425984208089516269489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44554950656138726344179659 66832425984208089516269489)
              ·
                refine ⟨50124319488156067137202117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66832425984208089516269489 50124319488156067137202117)
                ·
                  refine ⟨9398309904029262588225397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50124319488156067137202117 9398309904029262588225397)
                  ·
                    refine ⟨881091553502743367646131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9398309904029262588225397 881091553502743367646131)
                    ·
                      rfl

theorem cell23_5147759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_5147759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147759 prefixEnd_5147759 := by exact prefixLift 5147759
  have htrace : WordTrace (prefixWord ++ tailWord_5147759) baseStart_5147759 baseEnd_5147759 := by
    simpa [prefixWord, tailWord_5147759, baseEnd_5147759] using wordTrace_append hprefix tailTrace_5147759
  have hstable : (prefixWord ++ tailWord_5147759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147759).length < 2 ^ (prefixWord ++ tailWord_5147759).sum := by decide
  have hdescent : baseEnd_5147759 < baseStart_5147759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147774 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5147774 : Nat := 118140960795 + 5147774 * 2 ^ 59
def prefixEnd_5147774 : Nat := 4983230072969 + 3 ^ 40 * 5147774 * 2
def baseEnd_5147774 : Nat := 2643282362718047544250825

theorem tailTrace_5147774 : CollatzResearch.WordTrace tailWord_5147774 prefixEnd_5147774 2643282362718047544250825 := by
  unfold tailWord_5147774
  simp only [CollatzResearch.WordTrace]
  refine ⟨23469342806562680331253297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125169828301667628433350917 23469342806562680331253297)
  ·
    refine ⟨17602007104922010248439973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23469342806562680331253297 17602007104922010248439973)
    ·
      refine ⟨3300376332172876921582495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17602007104922010248439973 3300376332172876921582495)
      ·
        refine ⟨4950564498259315382373743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300376332172876921582495 4950564498259315382373743)
        ·
          refine ⟨7425846747388973073560615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950564498259315382373743 7425846747388973073560615)
          ·
            refine ⟨11138770121083459610340923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7425846747388973073560615 11138770121083459610340923)
            ·
              refine ⟨16708155181625189415511385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11138770121083459610340923 16708155181625189415511385)
              ·
                refine ⟨12531116386218892061633539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16708155181625189415511385 12531116386218892061633539)
                ·
                  refine ⟨18796674579328338092450309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12531116386218892061633539 18796674579328338092450309)
                  ·
                    refine ⟨3524376483624063392334433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18796674579328338092450309 3524376483624063392334433)
                    ·
                      refine ⟨2643282362718047544250825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524376483624063392334433 2643282362718047544250825)
                      ·
                        rfl

theorem cell23_5147774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5147774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147774 prefixEnd_5147774 := by exact prefixLift 5147774
  have htrace : WordTrace (prefixWord ++ tailWord_5147774) baseStart_5147774 baseEnd_5147774 := by
    simpa [prefixWord, tailWord_5147774, baseEnd_5147774] using wordTrace_append hprefix tailTrace_5147774
  have hstable : (prefixWord ++ tailWord_5147774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147774).length < 2 ^ (prefixWord ++ tailWord_5147774).sum := by decide
  have hdescent : baseEnd_5147774 < baseStart_5147774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147813 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 2, 4, 2]
def baseStart_5147813 : Nat := 118140960795 + 5147813 * 2 ^ 59
def prefixEnd_5147813 : Nat := 4983230072969 + 3 ^ 40 * 5147813 * 2
def baseEnd_5147813 : Nat := 2643302388463572891663145

theorem tailTrace_5147813 : CollatzResearch.WordTrace tailWord_5147813 prefixEnd_5147813 2643302388463572891663145 := by
  unfold tailWord_5147813
  simp only [CollatzResearch.WordTrace]
  refine ⟨187756164899360152310696093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125170776599573434873797395 187756164899360152310696093)
  ·
    refine ⟨70408561837260057116511035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187756164899360152310696093 70408561837260057116511035)
    ·
      refine ⟨105612842755890085674766553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70408561837260057116511035 105612842755890085674766553)
      ·
        refine ⟨79209632066917564256074915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105612842755890085674766553 79209632066917564256074915)
        ·
          refine ⟨118814448100376346384112373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79209632066917564256074915 118814448100376346384112373)
          ·
            refine ⟨11138854509410282473510535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118814448100376346384112373 11138854509410282473510535)
            ·
              refine ⟨16708281764115423710265803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11138854509410282473510535 16708281764115423710265803)
              ·
                refine ⟨25062422646173135565398705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16708281764115423710265803 25062422646173135565398705)
                ·
                  refine ⟨18796816984629851674049029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25062422646173135565398705 18796816984629851674049029)
                  ·
                    refine ⟨3524403184618097188884193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18796816984629851674049029 3524403184618097188884193)
                    ·
                      refine ⟨2643302388463572891663145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524403184618097188884193 2643302388463572891663145)
                      ·
                        rfl

theorem cell23_5147813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_5147813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147813 prefixEnd_5147813 := by exact prefixLift 5147813
  have htrace : WordTrace (prefixWord ++ tailWord_5147813) baseStart_5147813 baseEnd_5147813 := by
    simpa [prefixWord, tailWord_5147813, baseEnd_5147813] using wordTrace_append hprefix tailTrace_5147813
  have hstable : (prefixWord ++ tailWord_5147813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147813).length < 2 ^ (prefixWord ++ tailWord_5147813).sum := by decide
  have hdescent : baseEnd_5147813 < baseStart_5147813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147833 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 3]
def baseStart_5147833 : Nat := 118140960795 + 5147833 * 2 ^ 59
def prefixEnd_5147833 : Nat := 4983230072969 + 3 ^ 40 * 5147833 * 2
def baseEnd_5147833 : Nat := 2643312658076662813413053

theorem tailTrace_5147833 : CollatzResearch.WordTrace tailWord_5147833 prefixEnd_5147833 2643312658076662813413053 := by
  unfold tailWord_5147833
  simp only [CollatzResearch.WordTrace]
  refine ⟨187756894359287695726424153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125171262906191797150949435 187756894359287695726424153)
  ·
    refine ⟨140817670769465771794818115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187756894359287695726424153 140817670769465771794818115)
    ·
      refine ⟨211226506154198657692227173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140817670769465771794818115 211226506154198657692227173)
      ·
        refine ⟨39604969903912248317292595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211226506154198657692227173 39604969903912248317292595)
        ·
          refine ⟨59407454855868372475938893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39604969903912248317292595 59407454855868372475938893)
          ·
            refine ⟨22277795570950639678477085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59407454855868372475938893 22277795570950639678477085)
            ·
              refine ⟨8354173339106489879428907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22277795570950639678477085 8354173339106489879428907)
              ·
                refine ⟨12531260008659734819143361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8354173339106489879428907 12531260008659734819143361)
                ·
                  refine ⟨9398445006494801114357521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12531260008659734819143361 9398445006494801114357521)
                  ·
                    refine ⟨7048833754871100835768141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9398445006494801114357521 7048833754871100835768141)
                    ·
                      refine ⟨2643312658076662813413053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7048833754871100835768141 2643312658076662813413053)
                      ·
                        rfl

theorem cell23_5147833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_5147833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147833 prefixEnd_5147833 := by exact prefixLift 5147833
  have htrace : WordTrace (prefixWord ++ tailWord_5147833) baseStart_5147833 baseEnd_5147833 := by
    simpa [prefixWord, tailWord_5147833, baseEnd_5147833] using wordTrace_append hprefix tailTrace_5147833
  have hstable : (prefixWord ++ tailWord_5147833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147833).length < 2 ^ (prefixWord ++ tailWord_5147833).sum := by decide
  have hdescent : baseEnd_5147833 < baseStart_5147833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147859 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 5]
def baseStart_5147859 : Nat := 118140960795 + 5147859 * 2 ^ 59
def prefixEnd_5147859 : Nat := 4983230072969 + 3 ^ 40 * 5147859 * 2
def baseEnd_5147859 : Nat := 2643326008573679711687933

theorem tailTrace_5147859 : CollatzResearch.WordTrace tailWord_5147859 prefixEnd_5147859 2643326008573679711687933 := by
  unfold tailWord_5147859
  simp only [CollatzResearch.WordTrace]
  refine ⟨187757842657193502166870631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125171895104795668111247087 187757842657193502166870631)
  ·
    refine ⟨281636763985790253250305947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187757842657193502166870631 281636763985790253250305947)
    ·
      refine ⟨422455145978685379875458921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281636763985790253250305947 422455145978685379875458921)
      ·
        refine ⟨316841359484014034906594191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422455145978685379875458921 316841359484014034906594191)
        ·
          refine ⟨475262039226021052359891287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316841359484014034906594191 475262039226021052359891287)
          ·
            refine ⟨712893058839031578539836931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475262039226021052359891287 712893058839031578539836931)
            ·
              refine ⟨1069339588258547367809755397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712893058839031578539836931 1069339588258547367809755397)
              ·
                refine ⟨200501172798477631464329137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1069339588258547367809755397 200501172798477631464329137)
                ·
                  refine ⟨150375879598858223598246853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200501172798477631464329137 150375879598858223598246853)
                  ·
                    refine ⟨28195477424785916924671285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150375879598858223598246853 28195477424785916924671285)
                    ·
                      refine ⟨2643326008573679711687933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28195477424785916924671285 2643326008573679711687933)
                      ·
                        rfl

theorem cell23_5147859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_5147859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147859 prefixEnd_5147859 := by exact prefixLift 5147859
  have htrace : WordTrace (prefixWord ++ tailWord_5147859) baseStart_5147859 baseEnd_5147859 := by
    simpa [prefixWord, tailWord_5147859, baseEnd_5147859] using wordTrace_append hprefix tailTrace_5147859
  have hstable : (prefixWord ++ tailWord_5147859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147859).length < 2 ^ (prefixWord ++ tailWord_5147859).sum := by decide
  have hdescent : baseEnd_5147859 < baseStart_5147859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147863 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_5147863 : Nat := 118140960795 + 5147863 * 2 ^ 59
def prefixEnd_5147863 : Nat := 4983230072969 + 3 ^ 40 * 5147863 * 2
def baseEnd_5147863 : Nat := 2643328062496297696037915

theorem tailTrace_5147863 : CollatzResearch.WordTrace tailWord_5147863 prefixEnd_5147863 2643328062496297696037915 := by
  unfold tailWord_5147863
  simp only [CollatzResearch.WordTrace]
  refine ⟨187757988549179010850016243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125171992366119340566677495 187757988549179010850016243)
  ·
    refine ⟨281636982823768516275024365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187757988549179010850016243 281636982823768516275024365)
    ·
      refine ⟨105613868558913193603134137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281636982823768516275024365 105613868558913193603134137)
      ·
        refine ⟨79210401419184895202350603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105613868558913193603134137 79210401419184895202350603)
        ·
          refine ⟨118815602128777342803525905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79210401419184895202350603 118815602128777342803525905)
          ·
            refine ⟨89111701596583007102644429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118815602128777342803525905 89111701596583007102644429)
            ·
              refine ⟨33416888098718627663491661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89111701596583007102644429 33416888098718627663491661)
              ·
                refine ⟨12531333037019485373809373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33416888098718627663491661 12531333037019485373809373)
                ·
                  refine ⟨4699249888882307015178515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12531333037019485373809373 4699249888882307015178515)
                  ·
                    refine ⟨7048874833323460522767773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699249888882307015178515 7048874833323460522767773)
                    ·
                      refine ⟨2643328062496297696037915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7048874833323460522767773 2643328062496297696037915)
                      ·
                        rfl

theorem cell23_5147863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_5147863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147863 prefixEnd_5147863 := by exact prefixLift 5147863
  have htrace : WordTrace (prefixWord ++ tailWord_5147863) baseStart_5147863 baseEnd_5147863 := by
    simpa [prefixWord, tailWord_5147863, baseEnd_5147863] using wordTrace_append hprefix tailTrace_5147863
  have hstable : (prefixWord ++ tailWord_5147863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147863).length < 2 ^ (prefixWord ++ tailWord_5147863).sum := by decide
  have hdescent : baseEnd_5147863 < baseStart_5147863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147873 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_5147873 : Nat := 118140960795 + 5147873 * 2 ^ 59
def prefixEnd_5147873 : Nat := 4983230072969 + 3 ^ 40 * 5147873 * 2
def baseEnd_5147873 : Nat := 2643333197302842656912869

theorem tailTrace_5147873 : CollatzResearch.WordTrace tailWord_5147873 prefixEnd_5147873 2643333197302842656912869 := by
  unfold tailWord_5147873
  simp only [CollatzResearch.WordTrace]
  refine ⟨187758353279142782557880273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125172235519428521705253515 187758353279142782557880273)
  ·
    refine ⟨140818764959357086918410205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187758353279142782557880273 140818764959357086918410205)
    ·
      refine ⟨52807036859758907594403827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140818764959357086918410205 52807036859758907594403827)
      ·
        refine ⟨79210555289638361391605741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52807036859758907594403827 79210555289638361391605741)
        ·
          refine ⟨29703958233614385521852153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79210555289638361391605741 29703958233614385521852153)
          ·
            refine ⟨22277968675210789141389115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29703958233614385521852153 22277968675210789141389115)
            ·
              refine ⟨33416953012816183712083673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22277968675210789141389115 33416953012816183712083673)
              ·
                refine ⟨25062714759612137784062755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33416953012816183712083673 25062714759612137784062755)
                ·
                  refine ⟨37594072139418206676094133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25062714759612137784062755 37594072139418206676094133)
                  ·
                    refine ⟨3524444263070456875883825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37594072139418206676094133 3524444263070456875883825)
                    ·
                      refine ⟨2643333197302842656912869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524444263070456875883825 2643333197302842656912869)
                      ·
                        rfl

theorem cell23_5147873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_5147873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147873 prefixEnd_5147873 := by exact prefixLift 5147873
  have htrace : WordTrace (prefixWord ++ tailWord_5147873) baseStart_5147873 baseEnd_5147873 := by
    simpa [prefixWord, tailWord_5147873, baseEnd_5147873] using wordTrace_append hprefix tailTrace_5147873
  have hstable : (prefixWord ++ tailWord_5147873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147873).length < 2 ^ (prefixWord ++ tailWord_5147873).sum := by decide
  have hdescent : baseEnd_5147873 < baseStart_5147873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147883 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 1, 5]
def baseStart_5147883 : Nat := 118140960795 + 5147883 * 2 ^ 59
def prefixEnd_5147883 : Nat := 4983230072969 + 3 ^ 40 * 5147883 * 2
def baseEnd_5147883 : Nat := 881112777369795872595941

theorem tailTrace_5147883 : CollatzResearch.WordTrace tailWord_5147883 prefixEnd_5147883 881112777369795872595941 := by
  unfold tailWord_5147883
  simp only [CollatzResearch.WordTrace]
  refine ⟨187758718009106554265744303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125172478672737702843829535 187758718009106554265744303)
  ·
    refine ⟨281638077013659831398616455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187758718009106554265744303 281638077013659831398616455)
    ·
      refine ⟨422457115520489747097924683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281638077013659831398616455 422457115520489747097924683)
      ·
        refine ⟨633685673280734620646887025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422457115520489747097924683 633685673280734620646887025)
        ·
          refine ⟨475264254960550965485165269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633685673280734620646887025 475264254960550965485165269)
          ·
            refine ⟨11139005975637913253558561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 475264254960550965485165269 11139005975637913253558561)
            ·
              refine ⟨8354254481728434940168921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11139005975637913253558561 8354254481728434940168921)
              ·
                refine ⟨6265690861296326205126691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8354254481728434940168921 6265690861296326205126691)
                ·
                  refine ⟨9398536291944489307690037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265690861296326205126691 9398536291944489307690037)
                  ·
                    refine ⟨881112777369795872595941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9398536291944489307690037 881112777369795872595941)
                    ·
                      rfl

theorem cell23_5147883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 5].length) (baseStart_5147883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147883 prefixEnd_5147883 := by exact prefixLift 5147883
  have htrace : WordTrace (prefixWord ++ tailWord_5147883) baseStart_5147883 baseEnd_5147883 := by
    simpa [prefixWord, tailWord_5147883, baseEnd_5147883] using wordTrace_append hprefix tailTrace_5147883
  have hstable : (prefixWord ++ tailWord_5147883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147883).length < 2 ^ (prefixWord ++ tailWord_5147883).sum := by decide
  have hdescent : baseEnd_5147883 < baseStart_5147883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147903 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 4]
def baseStart_5147903 : Nat := 118140960795 + 5147903 * 2 ^ 59
def prefixEnd_5147903 : Nat := 4983230072969 + 3 ^ 40 * 5147903 * 2
def baseEnd_5147903 : Nat := 2643348601722477539537731

theorem tailTrace_5147903 : CollatzResearch.WordTrace tailWord_5147903 prefixEnd_5147903 2643348601722477539537731 := by
  unfold tailWord_5147903
  simp only [CollatzResearch.WordTrace]
  refine ⟨187759447469034097681472363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125172964979356065120981575 187759447469034097681472363)
  ·
    refine ⟨281639171203551146522208545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187759447469034097681472363 281639171203551146522208545)
    ·
      refine ⟨211229378402663359891656409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281639171203551146522208545 211229378402663359891656409)
      ·
        refine ⟨158422033801997519918742307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211229378402663359891656409 158422033801997519918742307)
        ·
          refine ⟨237633050702996279878113461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158422033801997519918742307 237633050702996279878113461)
          ·
            refine ⟨22278098503405901238573137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237633050702996279878113461 22278098503405901238573137)
            ·
              refine ⟨16708573877554425928929853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22278098503405901238573137 16708573877554425928929853)
              ·
                refine ⟨6265715204082909723348695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16708573877554425928929853 6265715204082909723348695)
                ·
                  refine ⟨9398572806124364585023043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265715204082909723348695 9398572806124364585023043)
                  ·
                    refine ⟨14097859209186546877534565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9398572806124364585023043 14097859209186546877534565)
                    ·
                      refine ⟨2643348601722477539537731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14097859209186546877534565 2643348601722477539537731)
                      ·
                        rfl

theorem cell23_5147903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_5147903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147903 prefixEnd_5147903 := by exact prefixLift 5147903
  have htrace : WordTrace (prefixWord ++ tailWord_5147903) baseStart_5147903 baseEnd_5147903 := by
    simpa [prefixWord, tailWord_5147903, baseEnd_5147903] using wordTrace_append hprefix tailTrace_5147903
  have hstable : (prefixWord ++ tailWord_5147903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147903).length < 2 ^ (prefixWord ++ tailWord_5147903).sum := by decide
  have hdescent : baseEnd_5147903 < baseStart_5147903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147913 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 2, 4]
def baseStart_5147913 : Nat := 118140960795 + 5147913 * 2 ^ 59
def prefixEnd_5147913 : Nat := 4983230072969 + 3 ^ 40 * 5147913 * 2
def baseEnd_5147913 : Nat := 881117912176340833470895

theorem tailTrace_5147913 : CollatzResearch.WordTrace tailWord_5147913 prefixEnd_5147913 881117912176340833470895 := by
  unfold tailWord_5147913
  simp only [CollatzResearch.WordTrace]
  refine ⟨187759812198997869389336393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125173208132665246259557595 187759812198997869389336393)
  ·
    refine ⟨140819859149248402042002295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187759812198997869389336393 140819859149248402042002295)
    ·
      refine ⟨211229788723872603063003443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140819859149248402042002295 211229788723872603063003443)
      ·
        refine ⟨316844683085808904594505165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211229788723872603063003443 316844683085808904594505165)
        ·
          refine ⟨118816756157178339222939437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316844683085808904594505165 118816756157178339222939437)
          ·
            refine ⟨44556283558941877208602289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118816756157178339222939437 44556283558941877208602289)
            ·
              refine ⟨33417212669206407906451717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44556283558941877208602289 33417212669206407906451717)
              ·
                refine ⟨6265727375476201482459697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33417212669206407906451717 6265727375476201482459697)
                ·
                  refine ⟨4699295531607151111844773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265727375476201482459697 4699295531607151111844773)
                  ·
                    refine ⟨881117912176340833470895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699295531607151111844773 881117912176340833470895)
                    ·
                      rfl

theorem cell23_5147913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 4].length) (baseStart_5147913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147913 prefixEnd_5147913 := by exact prefixLift 5147913
  have htrace : WordTrace (prefixWord ++ tailWord_5147913) baseStart_5147913 baseEnd_5147913 := by
    simpa [prefixWord, tailWord_5147913, baseEnd_5147913] using wordTrace_append hprefix tailTrace_5147913
  have hstable : (prefixWord ++ tailWord_5147913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147913).length < 2 ^ (prefixWord ++ tailWord_5147913).sum := by decide
  have hdescent : baseEnd_5147913 < baseStart_5147913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147916 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_5147916 : Nat := 118140960795 + 5147916 * 2 ^ 59
def prefixEnd_5147916 : Nat := 4983230072969 + 3 ^ 40 * 5147916 * 2
def baseEnd_5147916 : Nat := 2643355276970985988675171

theorem tailTrace_5147916 : CollatzResearch.WordTrace tailWord_5147916 prefixEnd_5147916 2643355276970985988675171 := by
  unfold tailWord_5147916
  simp only [CollatzResearch.WordTrace]
  refine ⟨93879960808993500450847801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125173281078658000601130401 93879960808993500450847801)
  ·
    refine ⟨70409970606745125338135851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93879960808993500450847801 70409970606745125338135851)
    ·
      refine ⟨105614955910117688007203777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70409970606745125338135851 105614955910117688007203777)
      ·
        refine ⟨79211216932588266005402833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105614955910117688007203777 79211216932588266005402833)
        ·
          refine ⟨59408412699441199504052125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79211216932588266005402833 59408412699441199504052125)
          ·
            refine ⟨22278154762290449814019547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59408412699441199504052125 22278154762290449814019547)
            ·
              refine ⟨33417232143435674721029321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22278154762290449814019547 33417232143435674721029321)
              ·
                refine ⟨25062924107576756040771991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33417232143435674721029321 25062924107576756040771991)
                ·
                  refine ⟨37594386161365134061157987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25062924107576756040771991 37594386161365134061157987)
                  ·
                    refine ⟨56391579242047701091736981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37594386161365134061157987 56391579242047701091736981)
                    ·
                      refine ⟨2643355276970985988675171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56391579242047701091736981 2643355276970985988675171)
                      ·
                        rfl

theorem cell23_5147916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_5147916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147916 prefixEnd_5147916 := by exact prefixLift 5147916
  have htrace : WordTrace (prefixWord ++ tailWord_5147916) baseStart_5147916 baseEnd_5147916 := by
    simpa [prefixWord, tailWord_5147916, baseEnd_5147916] using wordTrace_append hprefix tailTrace_5147916
  have hstable : (prefixWord ++ tailWord_5147916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147916).length < 2 ^ (prefixWord ++ tailWord_5147916).sum := by decide
  have hdescent : baseEnd_5147916 < baseStart_5147916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147930 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_5147930 : Nat := 118140960795 + 5147930 * 2 ^ 59
def prefixEnd_5147930 : Nat := 4983230072969 + 3 ^ 40 * 5147930 * 2
def baseEnd_5147930 : Nat := 881120821900049644633369

theorem tailTrace_5147930 : CollatzResearch.WordTrace tailWord_5147930 prefixEnd_5147930 881120821900049644633369 := by
  unfold tailWord_5147930
  simp only [CollatzResearch.WordTrace]
  refine ⟨46940108059984070323176311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125173621493290854195136829 46940108059984070323176311)
  ·
    refine ⟨70410162089976105484764467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46940108059984070323176311 70410162089976105484764467)
    ·
      refine ⟨105615243134964158227146701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70410162089976105484764467 105615243134964158227146701)
      ·
        refine ⟨39605716175611559335180013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105615243134964158227146701 39605716175611559335180013)
        ·
          refine ⟨14852143565854334750692505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39605716175611559335180013 14852143565854334750692505)
          ·
            refine ⟨11139107674390751063019379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14852143565854334750692505 11139107674390751063019379)
            ·
              refine ⟨16708661511586126594529069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11139107674390751063019379 16708661511586126594529069)
              ·
                refine ⟨6265748066844797472948401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16708661511586126594529069 6265748066844797472948401)
                ·
                  refine ⟨4699311050133598104711301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265748066844797472948401 4699311050133598104711301)
                  ·
                    refine ⟨881120821900049644633369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699311050133598104711301 881120821900049644633369)
                    ·
                      rfl

theorem cell23_5147930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_5147930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147930 prefixEnd_5147930 := by exact prefixLift 5147930
  have htrace : WordTrace (prefixWord ++ tailWord_5147930) baseStart_5147930 baseEnd_5147930 := by
    simpa [prefixWord, tailWord_5147930, baseEnd_5147930] using wordTrace_append hprefix tailTrace_5147930
  have hstable : (prefixWord ++ tailWord_5147930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147930).length < 2 ^ (prefixWord ++ tailWord_5147930).sum := by decide
  have hdescent : baseEnd_5147930 < baseStart_5147930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147933 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5147933 : Nat := 118140960795 + 5147933 * 2 ^ 59
def prefixEnd_5147933 : Nat := 4983230072969 + 3 ^ 40 * 5147933 * 2
def baseEnd_5147933 : Nat := 2643364006142112422162593

theorem tailTrace_5147933 : CollatzResearch.WordTrace tailWord_5147933 prefixEnd_5147933 2643364006142112422162593 := by
  unfold tailWord_5147933
  simp only [CollatzResearch.WordTrace]
  refine ⟨187760541658925412805064453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125173694439283608536709635 187760541658925412805064453)
  ·
    refine ⟨35205101561048514900949585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187760541658925412805064453 35205101561048514900949585)
    ·
      refine ⟨26403826170786386175712189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35205101561048514900949585 26403826170786386175712189)
      ·
        refine ⟨9901434814044894815892071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26403826170786386175712189 9901434814044894815892071)
        ·
          refine ⟨14852152221067342223838107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9901434814044894815892071 14852152221067342223838107)
          ·
            refine ⟨22278228331601013335757161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14852152221067342223838107 22278228331601013335757161)
            ·
              refine ⟨16708671248700760001817871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22278228331601013335757161 16708671248700760001817871)
              ·
                refine ⟨25063006873051140002726807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16708671248700760001817871 25063006873051140002726807)
                ·
                  refine ⟨37594510309576710004090211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25063006873051140002726807 37594510309576710004090211)
                  ·
                    refine ⟨56391765464365065006135317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37594510309576710004090211 56391765464365065006135317)
                    ·
                      refine ⟨2643364006142112422162593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56391765464365065006135317 2643364006142112422162593)
                      ·
                        rfl

theorem cell23_5147933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5147933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147933 prefixEnd_5147933 := by exact prefixLift 5147933
  have htrace : WordTrace (prefixWord ++ tailWord_5147933) baseStart_5147933 baseEnd_5147933 := by
    simpa [prefixWord, tailWord_5147933, baseEnd_5147933] using wordTrace_append hprefix tailTrace_5147933
  have hstable : (prefixWord ++ tailWord_5147933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147933).length < 2 ^ (prefixWord ++ tailWord_5147933).sum := by decide
  have hdescent : baseEnd_5147933 < baseStart_5147933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147934 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5147934 : Nat := 118140960795 + 5147934 * 2 ^ 59
def prefixEnd_5147934 : Nat := 4983230072969 + 3 ^ 40 * 5147934 * 2
def baseEnd_5147934 : Nat := 881121506540922306083363

theorem tailTrace_5147934 : CollatzResearch.WordTrace tailWord_5147934 prefixEnd_5147934 881121506540922306083363 := by
  unfold tailWord_5147934
  simp only [CollatzResearch.WordTrace]
  refine ⟨23470072266490223746981357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125173718754614526650567237 23470072266490223746981357)
  ·
    refine ⟨8801277099933833905118009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23470072266490223746981357 8801277099933833905118009)
    ·
      refine ⟨6600957824950375428838507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8801277099933833905118009 6600957824950375428838507)
      ·
        refine ⟨9901436737425563143257761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6600957824950375428838507 9901436737425563143257761)
        ·
          refine ⟨7426077553069172357443321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9901436737425563143257761 7426077553069172357443321)
          ·
            refine ⟨5569558164801879268082491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7426077553069172357443321 5569558164801879268082491)
            ·
              refine ⟨8354337247202818902123737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569558164801879268082491 8354337247202818902123737)
              ·
                refine ⟨6265752935402114176592803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8354337247202818902123737 6265752935402114176592803)
                ·
                  refine ⟨9398629403103171264889205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265752935402114176592803 9398629403103171264889205)
                  ·
                    refine ⟨881121506540922306083363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9398629403103171264889205 881121506540922306083363)
                    ·
                      rfl

theorem cell23_5147934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5147934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147934 prefixEnd_5147934 := by exact prefixLift 5147934
  have htrace : WordTrace (prefixWord ++ tailWord_5147934) baseStart_5147934 baseEnd_5147934 := by
    simpa [prefixWord, tailWord_5147934, baseEnd_5147934] using wordTrace_append hprefix tailTrace_5147934
  have hstable : (prefixWord ++ tailWord_5147934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147934).length < 2 ^ (prefixWord ++ tailWord_5147934).sum := by decide
  have hdescent : baseEnd_5147934 < baseStart_5147934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147953 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_5147953 : Nat := 118140960795 + 5147953 * 2 ^ 59
def prefixEnd_5147953 : Nat := 4983230072969 + 3 ^ 40 * 5147953 * 2
def baseEnd_5147953 : Nat := 2643374275755202343912501

theorem tailTrace_5147953 : CollatzResearch.WordTrace tailWord_5147953 prefixEnd_5147953 2643374275755202343912501 := by
  unfold tailWord_5147953
  simp only [CollatzResearch.WordTrace]
  refine ⟨187761271118852956220792513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125174180745901970813861675 187761271118852956220792513)
  ·
    refine ⟨140820953339139717165594385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187761271118852956220792513 140820953339139717165594385)
    ·
      refine ⟨105615715004354787874195789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140820953339139717165594385 105615715004354787874195789)
      ·
        refine ⟨39605893126633045452823421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105615715004354787874195789 39605893126633045452823421)
        ·
          refine ⟨14852209922487392044808783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39605893126633045452823421 14852209922487392044808783)
          ·
            refine ⟨22278314883731088067213175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14852209922487392044808783 22278314883731088067213175)
            ·
              refine ⟨33417472325596632100819763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22278314883731088067213175 33417472325596632100819763)
              ·
                refine ⟨50126208488394948151229645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33417472325596632100819763 50126208488394948151229645)
                ·
                  refine ⟨18797328183148105556711117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50126208488394948151229645 18797328183148105556711117)
                  ·
                    refine ⟨7048998068680539583766669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18797328183148105556711117 7048998068680539583766669)
                    ·
                      refine ⟨2643374275755202343912501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7048998068680539583766669 2643374275755202343912501)
                      ·
                        rfl

theorem cell23_5147953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_5147953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147953 prefixEnd_5147953 := by exact prefixLift 5147953
  have htrace : WordTrace (prefixWord ++ tailWord_5147953) baseStart_5147953 baseEnd_5147953 := by
    simpa [prefixWord, tailWord_5147953, baseEnd_5147953] using wordTrace_append hprefix tailTrace_5147953
  have hstable : (prefixWord ++ tailWord_5147953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147953).length < 2 ^ (prefixWord ++ tailWord_5147953).sum := by decide
  have hdescent : baseEnd_5147953 < baseStart_5147953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147957 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_5147957 : Nat := 118140960795 + 5147957 * 2 ^ 59
def prefixEnd_5147957 : Nat := 4983230072969 + 3 ^ 40 * 5147957 * 2
def baseEnd_5147957 : Nat := 2643376329677820328262483

theorem tailTrace_5147957 : CollatzResearch.WordTrace tailWord_5147957 prefixEnd_5147957 2643376329677820328262483 := by
  unfold tailWord_5147957
  simp only [CollatzResearch.WordTrace]
  refine ⟨187761417010838464903938125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125174278007225643269292083 187761417010838464903938125)
  ·
    refine ⟨70410531379064424338976797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187761417010838464903938125 70410531379064424338976797)
    ·
      refine ⟨26403949267149159127116299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70410531379064424338976797 26403949267149159127116299)
      ·
        refine ⟨39605923900723738690674449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26403949267149159127116299 39605923900723738690674449)
        ·
          refine ⟨29704442925542804018005837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39605923900723738690674449 29704442925542804018005837)
          ·
            refine ⟨11139166097078551506752189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29704442925542804018005837 11139166097078551506752189)
            ·
              refine ⟨4177187286404456815032071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11139166097078551506752189 4177187286404456815032071)
              ·
                refine ⟨6265780929606685222548107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177187286404456815032071 6265780929606685222548107)
                ·
                  refine ⟨9398671394410027833822161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265780929606685222548107 9398671394410027833822161)
                  ·
                    refine ⟨7049003545807520875366621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9398671394410027833822161 7049003545807520875366621)
                    ·
                      refine ⟨2643376329677820328262483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049003545807520875366621 2643376329677820328262483)
                      ·
                        rfl

theorem cell23_5147957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_5147957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147957 prefixEnd_5147957 := by exact prefixLift 5147957
  have htrace : WordTrace (prefixWord ++ tailWord_5147957) baseStart_5147957 baseEnd_5147957 := by
    simpa [prefixWord, tailWord_5147957, baseEnd_5147957] using wordTrace_append hprefix tailTrace_5147957
  have hstable : (prefixWord ++ tailWord_5147957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147957).length < 2 ^ (prefixWord ++ tailWord_5147957).sum := by decide
  have hdescent : baseEnd_5147957 < baseStart_5147957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5147980 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 3, 3, 2]
def baseStart_5147980 : Nat := 118140960795 + 5147980 * 2 ^ 59
def prefixEnd_5147980 : Nat := 4983230072969 + 3 ^ 40 * 5147980 * 2
def baseEnd_5147980 : Nat := 2643388139732873738274877

theorem tailTrace_5147980 : CollatzResearch.WordTrace tailWord_5147980 prefixEnd_5147980 2643388139732873738274877 := by
  unfold tailWord_5147980
  simp only [CollatzResearch.WordTrace]
  refine ⟨93881127944877569916012697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125174837259836759888016929 93881127944877569916012697)
  ·
    refine ⟨70410845958658177437009523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93881127944877569916012697 70410845958658177437009523)
    ·
      refine ⟨105616268937987266155514285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70410845958658177437009523 105616268937987266155514285)
      ·
        refine ⟨39606100851745224808317857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105616268937987266155514285 39606100851745224808317857)
        ·
          refine ⟨29704575638808918606238393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39606100851745224808317857 29704575638808918606238393)
          ·
            refine ⟨22278431729106688954678795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29704575638808918606238393 22278431729106688954678795)
            ·
              refine ⟨33417647593660033432018193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22278431729106688954678795 33417647593660033432018193)
              ·
                refine ⟨25063235695245025074013645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33417647593660033432018193 25063235695245025074013645)
                ·
                  refine ⟨9398713385716884402755117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25063235695245025074013645 9398713385716884402755117)
                  ·
                    refine ⟨3524517519643831651033169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9398713385716884402755117 3524517519643831651033169)
                    ·
                      refine ⟨2643388139732873738274877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524517519643831651033169 2643388139732873738274877)
                      ·
                        rfl

theorem cell23_5147980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_5147980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5147980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5147980 prefixEnd_5147980 := by exact prefixLift 5147980
  have htrace : WordTrace (prefixWord ++ tailWord_5147980) baseStart_5147980 baseEnd_5147980 := by
    simpa [prefixWord, tailWord_5147980, baseEnd_5147980] using wordTrace_append hprefix tailTrace_5147980
  have hstable : (prefixWord ++ tailWord_5147980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5147980).length < 2 ^ (prefixWord ++ tailWord_5147980).sum := by decide
  have hdescent : baseEnd_5147980 < baseStart_5147980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5147980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148016 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 9]
def baseStart_5148016 : Nat := 118140960795 + 5148016 * 2 ^ 59
def prefixEnd_5148016 : Nat := 4983230072969 + 3 ^ 40 * 5148016 * 2
def baseEnd_5148016 : Nat := 293711847226270621936079

theorem tailTrace_5148016 : CollatzResearch.WordTrace tailWord_5148016 prefixEnd_5148016 293711847226270621936079 := by
  unfold tailWord_5148016
  simp only [CollatzResearch.WordTrace]
  refine ⟨93881784458812358990167951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125175712611749811986890601 93881784458812358990167951)
  ·
    refine ⟨140822676688218538485251927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93881784458812358990167951 140822676688218538485251927)
    ·
      refine ⟨211234015032327807727877891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140822676688218538485251927 211234015032327807727877891)
      ·
        refine ⟨316851022548491711591816837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211234015032327807727877891 316851022548491711591816837)
        ·
          refine ⟨59409566727842195923465657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 316851022548491711591816837 59409566727842195923465657)
          ·
            refine ⟨44557175045881646942599243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59409566727842195923465657 44557175045881646942599243)
            ·
              refine ⟨66835762568822470413898865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44557175045881646942599243 66835762568822470413898865)
              ·
                refine ⟨50126821926616852810424149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66835762568822470413898865 50126821926616852810424149)
                ·
                  refine ⟨293711847226270621936079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50126821926616852810424149 293711847226270621936079)
                  ·
                    rfl

theorem cell23_5148016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 9].length) (baseStart_5148016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148016 prefixEnd_5148016 := by exact prefixLift 5148016
  have htrace : WordTrace (prefixWord ++ tailWord_5148016) baseStart_5148016 baseEnd_5148016 := by
    simpa [prefixWord, tailWord_5148016, baseEnd_5148016] using wordTrace_append hprefix tailTrace_5148016
  have hstable : (prefixWord ++ tailWord_5148016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148016).length < 2 ^ (prefixWord ++ tailWord_5148016).sum := by decide
  have hdescent : baseEnd_5148016 < baseStart_5148016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148021 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_5148021 : Nat := 118140960795 + 5148021 * 2 ^ 59
def prefixEnd_5148021 : Nat := 4983230072969 + 3 ^ 40 * 5148021 * 2
def baseEnd_5148021 : Nat := 2643409192439708077862189

theorem tailTrace_5148021 : CollatzResearch.WordTrace tailWord_5148021 prefixEnd_5148021 2643409192439708077862189 := by
  unfold tailWord_5148021
  simp only [CollatzResearch.WordTrace]
  refine ⟨187763751282606603834267917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125175834188404402556178611 187763751282606603834267917)
  ·
    refine ⟨70411406730977476437850469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187763751282606603834267917 70411406730977476437850469)
    ·
      refine ⟨13202138762058276832096963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70411406730977476437850469 13202138762058276832096963)
      ·
        refine ⟨19803208143087415248145445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13202138762058276832096963 19803208143087415248145445)
        ·
          refine ⟨3713101526828890359027271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19803208143087415248145445 3713101526828890359027271)
          ·
            refine ⟨5569652290243335538540907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713101526828890359027271 5569652290243335538540907)
            ·
              refine ⟨8354478435365003307811361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569652290243335538540907 8354478435365003307811361)
              ·
                refine ⟨6265858826523752480858521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8354478435365003307811361 6265858826523752480858521)
                ·
                  refine ⟨4699394119892814360643891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265858826523752480858521 4699394119892814360643891)
                  ·
                    refine ⟨7049091179839221540965837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699394119892814360643891 7049091179839221540965837)
                    ·
                      refine ⟨2643409192439708077862189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049091179839221540965837 2643409192439708077862189)
                      ·
                        rfl

theorem cell23_5148021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_5148021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148021 prefixEnd_5148021 := by exact prefixLift 5148021
  have htrace : WordTrace (prefixWord ++ tailWord_5148021) baseStart_5148021 baseEnd_5148021 := by
    simpa [prefixWord, tailWord_5148021, baseEnd_5148021] using wordTrace_append hprefix tailTrace_5148021
  have hstable : (prefixWord ++ tailWord_5148021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148021).length < 2 ^ (prefixWord ++ tailWord_5148021).sum := by decide
  have hdescent : baseEnd_5148021 < baseStart_5148021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148026 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_5148026 : Nat := 118140960795 + 5148026 * 2 ^ 59
def prefixEnd_5148026 : Nat := 4983230072969 + 3 ^ 40 * 5148026 * 2
def baseEnd_5148026 : Nat := 2643411759842980558299665

theorem tailTrace_5148026 : CollatzResearch.WordTrace tailWord_5148026 prefixEnd_5148026 2643411759842980558299665 := by
  unfold tailWord_5148026
  simp only [CollatzResearch.WordTrace]
  refine ⟨46940983411897122422049983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125175955765058993125466621 46940983411897122422049983)
  ·
    refine ⟨70411475117845683633074975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46940983411897122422049983 70411475117845683633074975)
    ·
      refine ⟨105617212676768525449612463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70411475117845683633074975 105617212676768525449612463)
      ·
        refine ⟨158425819015152788174418695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105617212676768525449612463 158425819015152788174418695)
        ·
          refine ⟨237638728522729182261628043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158425819015152788174418695 237638728522729182261628043)
          ·
            refine ⟨356458092784093773392442065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237638728522729182261628043 356458092784093773392442065)
            ·
              refine ⟨267343569588070330044331549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356458092784093773392442065 267343569588070330044331549)
              ·
                refine ⟨100253838595526373766624331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267343569588070330044331549 100253838595526373766624331)
                ·
                  refine ⟨150380757893289560649936497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100253838595526373766624331 150380757893289560649936497)
                  ·
                    refine ⟨112785568419967170487452373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150380757893289560649936497 112785568419967170487452373)
                    ·
                      refine ⟨2643411759842980558299665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112785568419967170487452373 2643411759842980558299665)
                      ·
                        rfl

theorem cell23_5148026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_5148026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148026 prefixEnd_5148026 := by exact prefixLift 5148026
  have htrace : WordTrace (prefixWord ++ tailWord_5148026) baseStart_5148026 baseEnd_5148026 := by
    simpa [prefixWord, tailWord_5148026, baseEnd_5148026] using wordTrace_append hprefix tailTrace_5148026
  have hstable : (prefixWord ++ tailWord_5148026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148026).length < 2 ^ (prefixWord ++ tailWord_5148026).sum := by decide
  have hdescent : baseEnd_5148026 < baseStart_5148026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148043 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 3]
def baseStart_5148043 : Nat := 118140960795 + 5148043 * 2 ^ 59
def prefixEnd_5148043 : Nat := 4983230072969 + 3 ^ 40 * 5148043 * 2
def baseEnd_5148043 : Nat := 2643420489014106991787087

theorem tailTrace_5148043 : CollatzResearch.WordTrace tailWord_5148043 prefixEnd_5148043 2643420489014106991787087 := by
  unfold tailWord_5148043
  simp only [CollatzResearch.WordTrace]
  refine ⟨187764553688526901591568783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125176369125684601061045855 187764553688526901591568783)
  ·
    refine ⟨281646830532790352387353175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187764553688526901591568783 281646830532790352387353175)
    ·
      refine ⟨422470245799185528581029763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281646830532790352387353175 422470245799185528581029763)
      ·
        refine ⟨633705368698778292871544645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422470245799185528581029763 633705368698778292871544645)
        ·
          refine ⟨118819756631020929913414621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 633705368698778292871544645 118819756631020929913414621)
          ·
            refine ⟨44557408736632848717530483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118819756631020929913414621 44557408736632848717530483)
            ·
              refine ⟨66836113104949273076295725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44557408736632848717530483 66836113104949273076295725)
              ·
                refine ⟨25063542414355977403610897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66836113104949273076295725 25063542414355977403610897)
                ·
                  refine ⟨18797656810766983052708173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25063542414355977403610897 18797656810766983052708173)
                  ·
                    refine ⟨7049121304037618644765565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18797656810766983052708173 7049121304037618644765565)
                    ·
                      refine ⟨2643420489014106991787087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049121304037618644765565 2643420489014106991787087)
                      ·
                        rfl

theorem cell23_5148043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 3].length) (baseStart_5148043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148043 prefixEnd_5148043 := by exact prefixLift 5148043
  have htrace : WordTrace (prefixWord ++ tailWord_5148043) baseStart_5148043 baseEnd_5148043 := by
    simpa [prefixWord, tailWord_5148043, baseEnd_5148043] using wordTrace_append hprefix tailTrace_5148043
  have hstable : (prefixWord ++ tailWord_5148043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148043).length < 2 ^ (prefixWord ++ tailWord_5148043).sum := by decide
  have hdescent : baseEnd_5148043 < baseStart_5148043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148044 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 2, 2, 2]
def baseStart_5148044 : Nat := 118140960795 + 5148044 * 2 ^ 59
def prefixEnd_5148044 : Nat := 4983230072969 + 3 ^ 40 * 5148044 * 2
def baseEnd_5148044 : Nat := 2643421002494761487874583

theorem tailTrace_5148044 : CollatzResearch.WordTrace tailWord_5148044 prefixEnd_5148044 2643421002494761487874583 := by
  unfold tailWord_5148044
  simp only [CollatzResearch.WordTrace]
  refine ⟨93882295080761639381177593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125176393441015519174903457 93882295080761639381177593)
  ·
    refine ⟨70411721310571229535883195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93882295080761639381177593 70411721310571229535883195)
    ·
      refine ⟨105617581965856844303824793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70411721310571229535883195 105617581965856844303824793)
      ·
        refine ⟨79213186474392633227868595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105617581965856844303824793 79213186474392633227868595)
        ·
          refine ⟨118819779711588949841802893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79213186474392633227868595 118819779711588949841802893)
          ·
            refine ⟨44557417391845856190676085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118819779711588949841802893 44557417391845856190676085)
            ·
              refine ⟨4177257880485549017875883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44557417391845856190676085 4177257880485549017875883)
              ·
                refine ⟨6265886820728323526813825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177257880485549017875883 6265886820728323526813825)
                ·
                  refine ⟨4699415115546242645110369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265886820728323526813825 4699415115546242645110369)
                  ·
                    refine ⟨3524561336659681983832777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4699415115546242645110369 3524561336659681983832777)
                    ·
                      refine ⟨2643421002494761487874583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524561336659681983832777 2643421002494761487874583)
                      ·
                        rfl

theorem cell23_5148044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_5148044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148044 prefixEnd_5148044 := by exact prefixLift 5148044
  have htrace : WordTrace (prefixWord ++ tailWord_5148044) baseStart_5148044 baseEnd_5148044 := by
    simpa [prefixWord, tailWord_5148044, baseEnd_5148044] using wordTrace_append hprefix tailTrace_5148044
  have hstable : (prefixWord ++ tailWord_5148044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148044).length < 2 ^ (prefixWord ++ tailWord_5148044).sum := by decide
  have hdescent : baseEnd_5148044 < baseStart_5148044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148063 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 1, 7]
def baseStart_5148063 : Nat := 118140960795 + 5148063 * 2 ^ 59
def prefixEnd_5148063 : Nat := 4983230072969 + 3 ^ 40 * 5148063 * 2
def baseEnd_5148063 : Nat := 881143586209065637845665

theorem tailTrace_5148063 : CollatzResearch.WordTrace tailWord_5148063 prefixEnd_5148063 881143586209065637845665 := by
  unfold tailWord_5148063
  simp only [CollatzResearch.WordTrace]
  refine ⟨187765283148454445007296843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125176855432302963338197895 187765283148454445007296843)
  ·
    refine ⟨281647924722681667510945265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187765283148454445007296843 281647924722681667510945265)
    ·
      refine ⟨211235943542011250633208949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281647924722681667510945265 211235943542011250633208949)
      ·
        refine ⟨19803369707063554746863339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211235943542011250633208949 19803369707063554746863339)
        ·
          refine ⟨29705054560595332120295009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19803369707063554746863339 29705054560595332120295009)
          ·
            refine ⟨22278790920446499090221257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29705054560595332120295009 22278790920446499090221257)
            ·
              refine ⟨16709093190334874317665943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22278790920446499090221257 16709093190334874317665943)
              ·
                refine ⟨25063639785502311476498915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16709093190334874317665943 25063639785502311476498915)
                ·
                  refine ⟨37595459678253467214748373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25063639785502311476498915 37595459678253467214748373)
                  ·
                    refine ⟨881143586209065637845665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37595459678253467214748373 881143586209065637845665)
                    ·
                      rfl

theorem cell23_5148063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_5148063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148063 prefixEnd_5148063 := by exact prefixLift 5148063
  have htrace : WordTrace (prefixWord ++ tailWord_5148063) baseStart_5148063 baseEnd_5148063 := by
    simpa [prefixWord, tailWord_5148063, baseEnd_5148063] using wordTrace_append hprefix tailTrace_5148063
  have hstable : (prefixWord ++ tailWord_5148063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148063).length < 2 ^ (prefixWord ++ tailWord_5148063).sum := by decide
  have hdescent : baseEnd_5148063 < baseStart_5148063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148110 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_5148110 : Nat := 118140960795 + 5148110 * 2 ^ 59
def prefixEnd_5148110 : Nat := 4983230072969 + 3 ^ 40 * 5148110 * 2
def baseEnd_5148110 : Nat := 881151630739319409883093

theorem tailTrace_5148110 : CollatzResearch.WordTrace tailWord_5148110 prefixEnd_5148110 881151630739319409883093 := by
  unfold tailWord_5148110
  simp only [CollatzResearch.WordTrace]
  refine ⟨23470874672410521504282223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125177998252856114689505189 23470874672410521504282223)
  ·
    refine ⟨35206312008615782256423335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23470874672410521504282223 35206312008615782256423335)
    ·
      refine ⟨52809468012923673384635003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35206312008615782256423335 52809468012923673384635003)
      ·
        refine ⟨79214202019385510076952505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52809468012923673384635003 79214202019385510076952505)
        ·
          refine ⟨59410651514539132557714379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79214202019385510076952505 59410651514539132557714379)
          ·
            refine ⟨89115977271808698836571569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59410651514539132557714379 89115977271808698836571569)
            ·
              refine ⟨66836982953856524127428677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89115977271808698836571569 66836982953856524127428677)
              ·
                refine ⟨12531934303848098273892877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66836982953856524127428677 12531934303848098273892877)
                ·
                  refine ⟨4699475363943036852709829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12531934303848098273892877 4699475363943036852709829)
                  ·
                    refine ⟨881151630739319409883093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699475363943036852709829 881151630739319409883093)
                    ·
                      rfl

theorem cell23_5148110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_5148110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148110 prefixEnd_5148110 := by exact prefixLift 5148110
  have htrace : WordTrace (prefixWord ++ tailWord_5148110) baseStart_5148110 baseEnd_5148110 := by
    simpa [prefixWord, tailWord_5148110, baseEnd_5148110] using wordTrace_append hprefix tailTrace_5148110
  have hstable : (prefixWord ++ tailWord_5148110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148110).length < 2 ^ (prefixWord ++ tailWord_5148110).sum := by decide
  have hdescent : baseEnd_5148110 < baseStart_5148110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148120 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_5148120 : Nat := 118140960795 + 5148120 * 2 ^ 59
def prefixEnd_5148120 : Nat := 4983230072969 + 3 ^ 40 * 5148120 * 2
def baseEnd_5148120 : Nat := 2643460027024503190524233

theorem tailTrace_5148120 : CollatzResearch.WordTrace tailWord_5148120 prefixEnd_5148120 2643460027024503190524233 := by
  unfold tailWord_5148120
  simp only [CollatzResearch.WordTrace]
  refine ⟨93883681054623971871060907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125178241406165295828081209 93883681054623971871060907)
  ·
    refine ⟨140825521581935957806591361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93883681054623971871060907 140825521581935957806591361)
    ·
      refine ⟨105619141186451968354943521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140825521581935957806591361 105619141186451968354943521)
      ·
        refine ⟨79214355889838976266207641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105619141186451968354943521 79214355889838976266207641)
        ·
          refine ⟨59410766917379232199655731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79214355889838976266207641 59410766917379232199655731)
          ·
            refine ⟨89116150376068848299483597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59410766917379232199655731 89116150376068848299483597)
            ·
              refine ⟨33418556391025818112306349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89116150376068848299483597 33418556391025818112306349)
              ·
                refine ⟨12531958646634681792114881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33418556391025818112306349 12531958646634681792114881)
                ·
                  refine ⟨9398968984976011344086161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12531958646634681792114881 9398968984976011344086161)
                  ·
                    refine ⟨7049226738732008508064621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9398968984976011344086161 7049226738732008508064621)
                    ·
                      refine ⟨2643460027024503190524233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049226738732008508064621 2643460027024503190524233)
                      ·
                        rfl

theorem cell23_5148120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_5148120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148120 prefixEnd_5148120 := by exact prefixLift 5148120
  have htrace : WordTrace (prefixWord ++ tailWord_5148120) baseStart_5148120 baseEnd_5148120 := by
    simpa [prefixWord, tailWord_5148120, baseEnd_5148120] using wordTrace_append hprefix tailTrace_5148120
  have hstable : (prefixWord ++ tailWord_5148120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148120).length < 2 ^ (prefixWord ++ tailWord_5148120).sum := by decide
  have hdescent : baseEnd_5148120 < baseStart_5148120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148127 : List Nat := [1, 1, 2, 3, 3, 1, 2, 5, 1, 4]
def baseStart_5148127 : Nat := 118140960795 + 5148127 * 2 ^ 59
def prefixEnd_5148127 : Nat := 4983230072969 + 3 ^ 40 * 5148127 * 2
def baseEnd_5148127 : Nat := 881154540463028221045567

theorem tailTrace_5148127 : CollatzResearch.WordTrace tailWord_5148127 prefixEnd_5148127 881154540463028221045567 := by
  unfold tailWord_5148127
  simp only [CollatzResearch.WordTrace]
  refine ⟨187767617420222583937626635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125178411613481722625084423 187767617420222583937626635)
  ·
    refine ⟨281651426130333875906439953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187767617420222583937626635 281651426130333875906439953)
    ·
      refine ⟨211238569597750406929829965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281651426130333875906439953 211238569597750406929829965)
      ·
        refine ⟨79214463599156402598686237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211238569597750406929829965 79214463599156402598686237)
        ·
          refine ⟨29705423849683650974507339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79214463599156402598686237 29705423849683650974507339)
          ·
            refine ⟨44558135774525476461761009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29705423849683650974507339 44558135774525476461761009)
            ·
              refine ⟨33418601830894107346320757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44558135774525476461761009 33418601830894107346320757)
              ·
                refine ⟨3132993921646322563717571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33418601830894107346320757 3132993921646322563717571)
                ·
                  refine ⟨4699490882469483845576357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132993921646322563717571 4699490882469483845576357)
                  ·
                    refine ⟨881154540463028221045567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699490882469483845576357 881154540463028221045567)
                    ·
                      rfl

theorem cell23_5148127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 4].length) (baseStart_5148127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148127 prefixEnd_5148127 := by exact prefixLift 5148127
  have htrace : WordTrace (prefixWord ++ tailWord_5148127) baseStart_5148127 baseEnd_5148127 := by
    simpa [prefixWord, tailWord_5148127, baseEnd_5148127] using wordTrace_append hprefix tailTrace_5148127
  have hstable : (prefixWord ++ tailWord_5148127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148127).length < 2 ^ (prefixWord ++ tailWord_5148127).sum := by decide
  have hdescent : baseEnd_5148127 < baseStart_5148127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148144 : List Nat := [2, 1, 1, 1, 3, 4, 4, 2, 1, 4]
def baseStart_5148144 : Nat := 118140960795 + 5148144 * 2 ^ 59
def prefixEnd_5148144 : Nat := 4983230072969 + 3 ^ 40 * 5148144 * 2
def baseEnd_5148144 : Nat := 881157450186737032208041

theorem tailTrace_5148144 : CollatzResearch.WordTrace tailWord_5148144 prefixEnd_5148144 881157450186737032208041 := by
  unfold tailWord_5148144
  simp only [CollatzResearch.WordTrace]
  refine ⟨93884118730580497920497743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125178824974107330560663657 93884118730580497920497743)
  ·
    refine ⟨140826178095870746880746615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93884118730580497920497743 140826178095870746880746615)
    ·
      refine ⟨211239267143806120321119923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140826178095870746880746615 211239267143806120321119923)
      ·
        refine ⟨316858900715709180481679885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211239267143806120321119923 316858900715709180481679885)
        ·
          refine ⟨118822087768390942680629957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316858900715709180481679885 118822087768390942680629957)
          ·
            refine ⟨22279141456573301752618117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118822087768390942680629957 22279141456573301752618117)
            ·
              refine ⟨4177339023107494078615897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22279141456573301752618117 4177339023107494078615897)
              ·
                refine ⟨3133004267330620558961923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4177339023107494078615897 3133004267330620558961923)
                ·
                  refine ⟨4699506400995930838442885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133004267330620558961923 4699506400995930838442885)
                  ·
                    refine ⟨881157450186737032208041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699506400995930838442885 881157450186737032208041)
                    ·
                      rfl

theorem cell23_5148144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 4].length) (baseStart_5148144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148144 prefixEnd_5148144 := by exact prefixLift 5148144
  have htrace : WordTrace (prefixWord ++ tailWord_5148144) baseStart_5148144 baseEnd_5148144 := by
    simpa [prefixWord, tailWord_5148144, baseEnd_5148144] using wordTrace_append hprefix tailTrace_5148144
  have hstable : (prefixWord ++ tailWord_5148144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148144).length < 2 ^ (prefixWord ++ tailWord_5148144).sum := by decide
  have hdescent : baseEnd_5148144 < baseStart_5148144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148167 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_5148167 : Nat := 118140960795 + 5148167 * 2 ^ 59
def prefixEnd_5148167 : Nat := 4983230072969 + 3 ^ 40 * 5148167 * 2
def baseEnd_5148167 : Nat := 2643484160615264506636517

theorem tailTrace_5148167 : CollatzResearch.WordTrace tailWord_5148167 prefixEnd_5148167 2643484160615264506636517 := by
  unfold tailWord_5148167
  simp only [CollatzResearch.WordTrace]
  refine ⟨187769076340077670769082755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125179384226718447179388503 187769076340077670769082755)
  ·
    refine ⟨281653614510116506153624133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187769076340077670769082755 281653614510116506153624133)
    ·
      refine ⟨52810052720646844903804525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281653614510116506153624133 52810052720646844903804525)
      ·
        refine ⟨19803769770242566838926697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52810052720646844903804525 19803769770242566838926697)
        ·
          refine ⟨14852827327681925129195023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19803769770242566838926697 14852827327681925129195023)
          ·
            refine ⟨22279240991522887693792535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14852827327681925129195023 22279240991522887693792535)
            ·
              refine ⟨33418861487284331540688803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22279240991522887693792535 33418861487284331540688803)
              ·
                refine ⟨50128292230926497311033205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33418861487284331540688803 50128292230926497311033205)
                ·
                  refine ⟨4699527396649359122909363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50128292230926497311033205 4699527396649359122909363)
                  ·
                    refine ⟨7049291094974038684364045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699527396649359122909363 7049291094974038684364045)
                    ·
                      refine ⟨2643484160615264506636517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049291094974038684364045 2643484160615264506636517)
                      ·
                        rfl

theorem cell23_5148167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_5148167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148167 prefixEnd_5148167 := by exact prefixLift 5148167
  have htrace : WordTrace (prefixWord ++ tailWord_5148167) baseStart_5148167 baseEnd_5148167 := by
    simpa [prefixWord, tailWord_5148167, baseEnd_5148167] using wordTrace_append hprefix tailTrace_5148167
  have hstable : (prefixWord ++ tailWord_5148167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148167).length < 2 ^ (prefixWord ++ tailWord_5148167).sum := by decide
  have hdescent : baseEnd_5148167 < baseStart_5148167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148170 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_5148170 : Nat := 118140960795 + 5148170 * 2 ^ 59
def prefixEnd_5148170 : Nat := 4983230072969 + 3 ^ 40 * 5148170 * 2
def baseEnd_5148170 : Nat := 881161900352409331633001

theorem tailTrace_5148170 : CollatzResearch.WordTrace tailWord_5148170 prefixEnd_5148170 881161900352409331633001 := by
  unfold tailWord_5148170
  simp only [CollatzResearch.WordTrace]
  refine ⟨46942296439766700570360491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125179457172711201520961309 46942296439766700570360491)
  ·
    refine ⟨70413444659650050855540737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46942296439766700570360491 70413444659650050855540737)
    ·
      refine ⟨52810083494737538141655553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70413444659650050855540737 52810083494737538141655553)
      ·
        refine ⟨39607562621053153606241665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52810083494737538141655553 39607562621053153606241665)
        ·
          refine ⟨29705671965789865204681249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39607562621053153606241665 29705671965789865204681249)
          ·
            refine ⟨22279253974342398903510937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29705671965789865204681249 22279253974342398903510937)
            ·
              refine ⟨16709440480756799177633203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22279253974342398903510937 16709440480756799177633203)
              ·
                refine ⟨25064160721135198766449805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16709440480756799177633203 25064160721135198766449805)
                ·
                  refine ⟨9399060270425699537418677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25064160721135198766449805 9399060270425699537418677)
                  ·
                    refine ⟨881161900352409331633001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9399060270425699537418677 881161900352409331633001)
                    ·
                      rfl

theorem cell23_5148170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_5148170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148170 prefixEnd_5148170 := by exact prefixLift 5148170
  have htrace : WordTrace (prefixWord ++ tailWord_5148170) baseStart_5148170 baseEnd_5148170 := by
    simpa [prefixWord, tailWord_5148170, baseEnd_5148170] using wordTrace_append hprefix tailTrace_5148170
  have hstable : (prefixWord ++ tailWord_5148170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148170).length < 2 ^ (prefixWord ++ tailWord_5148170).sum := by decide
  have hdescent : baseEnd_5148170 < baseStart_5148170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148203 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 4]
def baseStart_5148203 : Nat := 118140960795 + 5148203 * 2 ^ 59
def prefixEnd_5148203 : Nat := 4983230072969 + 3 ^ 40 * 5148203 * 2
def baseEnd_5148203 : Nat := 2643502645918826365786351

theorem tailTrace_5148203 : CollatzResearch.WordTrace tailWord_5148203 prefixEnd_5148203 2643502645918826365786351 := by
  unfold tailWord_5148203
  simp only [CollatzResearch.WordTrace]
  refine ⟨187770389367947248917393263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125180259578631499278262175 187770389367947248917393263)
  ·
    refine ⟨281655584051920873376089895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187770389367947248917393263 281655584051920873376089895)
    ·
      refine ⟨422483376077881310064134843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281655584051920873376089895 422483376077881310064134843)
      ·
        refine ⟨633725064116821965096202265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422483376077881310064134843 633725064116821965096202265)
        ·
          refine ⟨475293798087616473822151699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633725064116821965096202265 475293798087616473822151699)
          ·
            refine ⟨712940697131424710733227549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475293798087616473822151699 712940697131424710733227549)
            ·
              refine ⟨267352761424284266524960331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 712940697131424710733227549 267352761424284266524960331)
              ·
                refine ⟨401029142136426399787440497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267352761424284266524960331 401029142136426399787440497)
                ·
                  refine ⟨300771856602319799840580373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401029142136426399787440497 300771856602319799840580373)
                  ·
                    refine ⟨14098680778233740617527205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 300771856602319799840580373 14098680778233740617527205)
                    ·
                      refine ⟨2643502645918826365786351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14098680778233740617527205 2643502645918826365786351)
                      ·
                        rfl

theorem cell23_5148203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 4].length) (baseStart_5148203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148203 prefixEnd_5148203 := by exact prefixLift 5148203
  have htrace : WordTrace (prefixWord ++ tailWord_5148203) baseStart_5148203 baseEnd_5148203 := by
    simpa [prefixWord, tailWord_5148203, baseEnd_5148203] using wordTrace_append hprefix tailTrace_5148203
  have hstable : (prefixWord ++ tailWord_5148203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148203).length < 2 ^ (prefixWord ++ tailWord_5148203).sum := by decide
  have hdescent : baseEnd_5148203 < baseStart_5148203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148217 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 1, 6]
def baseStart_5148217 : Nat := 118140960795 + 5148217 * 2 ^ 59
def prefixEnd_5148217 : Nat := 4983230072969 + 3 ^ 40 * 5148217 * 2
def baseEnd_5148217 : Nat := 881169944882663103670429

theorem tailTrace_5148217 : CollatzResearch.WordTrace tailWord_5148217 prefixEnd_5148217 881169944882663103670429 := by
  unfold tailWord_5148217
  simp only [CollatzResearch.WordTrace]
  refine ⟨187770899989896529308402905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125180599993264352872268603 187770899989896529308402905)
  ·
    refine ⟨140828174992422396981302179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187770899989896529308402905 140828174992422396981302179)
    ·
      refine ⟨211242262488633595471953269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140828174992422396981302179 211242262488633595471953269)
      ·
        refine ⟨19803962108309399575495619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211242262488633595471953269 19803962108309399575495619)
        ·
          refine ⟨29705943162464099363243429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19803962108309399575495619 29705943162464099363243429)
          ·
            refine ⟨5569864342962018630608143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29705943162464099363243429 5569864342962018630608143)
            ·
              refine ⟨8354796514443027945912215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569864342962018630608143 8354796514443027945912215)
              ·
                refine ⟨12532194771664541918868323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8354796514443027945912215 12532194771664541918868323)
                ·
                  refine ⟨18798292157496812878302485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12532194771664541918868323 18798292157496812878302485)
                  ·
                    refine ⟨881169944882663103670429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18798292157496812878302485 881169944882663103670429)
                    ·
                      rfl

theorem cell23_5148217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_5148217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148217 prefixEnd_5148217 := by exact prefixLift 5148217
  have htrace : WordTrace (prefixWord ++ tailWord_5148217) baseStart_5148217 baseEnd_5148217 := by
    simpa [prefixWord, tailWord_5148217, baseEnd_5148217] using wordTrace_append hprefix tailTrace_5148217
  have hstable : (prefixWord ++ tailWord_5148217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148217).length < 2 ^ (prefixWord ++ tailWord_5148217).sum := by decide
  have hdescent : baseEnd_5148217 < baseStart_5148217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148233 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_5148233 : Nat := 118140960795 + 5148233 * 2 ^ 59
def prefixEnd_5148233 : Nat := 4983230072969 + 3 ^ 40 * 5148233 * 2
def baseEnd_5148233 : Nat := 2643518050338461248411213

theorem tailTrace_5148233 : CollatzResearch.WordTrace tailWord_5148233 prefixEnd_5148233 2643518050338461248411213 := by
  unfold tailWord_5148233
  simp only [CollatzResearch.WordTrace]
  refine ⟨187771483557838564040985353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125180989038559042693990235 187771483557838564040985353)
  ·
    refine ⟨140828612668378923030739015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187771483557838564040985353 140828612668378923030739015)
    ·
      refine ⟨211242919002568384546108523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140828612668378923030739015 211242919002568384546108523)
      ·
        refine ⟨316864378503852576819162785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211242919002568384546108523 316864378503852576819162785)
        ·
          refine ⟨237648283877889432614372089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316864378503852576819162785 237648283877889432614372089)
          ·
            refine ⟨178236212908417074460779067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237648283877889432614372089 178236212908417074460779067)
            ·
              refine ⟨267354319362625611691168601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178236212908417074460779067 267354319362625611691168601)
              ·
                refine ⟨200515739521969208768376451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267354319362625611691168601 200515739521969208768376451)
                ·
                  refine ⟨300773609282953813152564677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200515739521969208768376451 300773609282953813152564677)
                  ·
                    refine ⟨56395051740553839966105877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 300773609282953813152564677 56395051740553839966105877)
                    ·
                      refine ⟨2643518050338461248411213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56395051740553839966105877 2643518050338461248411213)
                      ·
                        rfl

theorem cell23_5148233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_5148233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148233 prefixEnd_5148233 := by exact prefixLift 5148233
  have htrace : WordTrace (prefixWord ++ tailWord_5148233) baseStart_5148233 baseEnd_5148233 := by
    simpa [prefixWord, tailWord_5148233, baseEnd_5148233] using wordTrace_append hprefix tailTrace_5148233
  have hstable : (prefixWord ++ tailWord_5148233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148233).length < 2 ^ (prefixWord ++ tailWord_5148233).sum := by decide
  have hdescent : baseEnd_5148233 < baseStart_5148233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148240 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 3]
def baseStart_5148240 : Nat := 118140960795 + 5148240 * 2 ^ 59
def prefixEnd_5148240 : Nat := 4983230072969 + 3 ^ 40 * 5148240 * 2
def baseEnd_5148240 : Nat := 2643521644703042721023681

theorem tailTrace_5148240 : CollatzResearch.WordTrace tailWord_5148240 prefixEnd_5148240 2643521644703042721023681 := by
  unfold tailWord_5148240
  simp only [CollatzResearch.WordTrace]
  refine ⟨93885869434406602118245087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125181159245875469490993449 93885869434406602118245087)
  ·
    refine ⟨140828804151609903177367631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93885869434406602118245087 140828804151609903177367631)
    ·
      refine ⟨211243206227414854766051447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140828804151609903177367631 211243206227414854766051447)
      ·
        refine ⟨316864809341122282149077171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211243206227414854766051447 316864809341122282149077171)
        ·
          refine ⟨475297214011683423223615757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316864809341122282149077171 475297214011683423223615757)
          ·
            refine ⟨178236455254381283708855909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 475297214011683423223615757 178236455254381283708855909)
            ·
              refine ⟨33419335360196490695410483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178236455254381283708855909 33419335360196490695410483)
              ·
                refine ⟨50129003040294736043115725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33419335360196490695410483 50129003040294736043115725)
                ·
                  refine ⟨18798376140110526016168397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50129003040294736043115725 18798376140110526016168397)
                  ·
                    refine ⟨7049391052541447256063149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18798376140110526016168397 7049391052541447256063149)
                    ·
                      refine ⟨2643521644703042721023681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049391052541447256063149 2643521644703042721023681)
                      ·
                        rfl

theorem cell23_5148240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_5148240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148240 prefixEnd_5148240 := by exact prefixLift 5148240
  have htrace : WordTrace (prefixWord ++ tailWord_5148240) baseStart_5148240 baseEnd_5148240 := by
    simpa [prefixWord, tailWord_5148240, baseEnd_5148240] using wordTrace_append hprefix tailTrace_5148240
  have hstable : (prefixWord ++ tailWord_5148240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148240).length < 2 ^ (prefixWord ++ tailWord_5148240).sum := by decide
  have hdescent : baseEnd_5148240 < baseStart_5148240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148243 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 6, 7]
def baseStart_5148243 : Nat := 118140960795 + 5148243 * 2 ^ 59
def prefixEnd_5148243 : Nat := 4983230072969 + 3 ^ 40 * 5148243 * 2
def baseEnd_5148243 : Nat := 881174395048335403095389

theorem tailTrace_5148243 : CollatzResearch.WordTrace tailWord_5148243 prefixEnd_5148243 881174395048335403095389 := by
  unfold tailWord_5148243
  simp only [CollatzResearch.WordTrace]
  refine ⟨187771848287802335748849383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125181232191868223832566255 187771848287802335748849383)
  ·
    refine ⟨281657772431703503623274075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187771848287802335748849383 281657772431703503623274075)
    ·
      refine ⟨422486658647555255434911113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281657772431703503623274075 422486658647555255434911113)
      ·
        refine ⟨316864993985666441576183335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422486658647555255434911113 316864993985666441576183335)
        ·
          refine ⟨475297490978499662364275003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316864993985666441576183335 475297490978499662364275003)
          ·
            refine ⟨712946236467749493546412505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475297490978499662364275003 712946236467749493546412505)
            ·
              refine ⟨534709677350812120159809379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712946236467749493546412505 534709677350812120159809379)
              ·
                refine ⟨802064516026218180239714069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534709677350812120159809379 802064516026218180239714069)
                ·
                  refine ⟨37596774188728977198736597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 802064516026218180239714069 37596774188728977198736597)
                  ·
                    refine ⟨881174395048335403095389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37596774188728977198736597 881174395048335403095389)
                    ·
                      rfl

theorem cell23_5148243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 7].length) (baseStart_5148243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148243 prefixEnd_5148243 := by exact prefixLift 5148243
  have htrace : WordTrace (prefixWord ++ tailWord_5148243) baseStart_5148243 baseEnd_5148243 := by
    simpa [prefixWord, tailWord_5148243, baseEnd_5148243] using wordTrace_append hprefix tailTrace_5148243
  have hstable : (prefixWord ++ tailWord_5148243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148243).length < 2 ^ (prefixWord ++ tailWord_5148243).sum := by decide
  have hdescent : baseEnd_5148243 < baseStart_5148243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148257 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_5148257 : Nat := 118140960795 + 5148257 * 2 ^ 59
def prefixEnd_5148257 : Nat := 4983230072969 + 3 ^ 40 * 5148257 * 2
def baseEnd_5148257 : Nat := 2643530373874169154511103

theorem tailTrace_5148257 : CollatzResearch.WordTrace tailWord_5148257 prefixEnd_5148257 2643530373874169154511103 := by
  unfold tailWord_5148257
  simp only [CollatzResearch.WordTrace]
  refine ⟨187772358909751616139859025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125181572606501077426572683 187772358909751616139859025)
  ·
    refine ⟨140829269182313712104894269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187772358909751616139859025 140829269182313712104894269)
    ·
      refine ⟨52810975943367642039335351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140829269182313712104894269 52810975943367642039335351)
      ·
        refine ⟨79216463915051463059003027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52810975943367642039335351 79216463915051463059003027)
        ·
          refine ⟨118824695872577194588504541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79216463915051463059003027 118824695872577194588504541)
          ·
            refine ⟨44559260952216447970689203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118824695872577194588504541 44559260952216447970689203)
            ·
              refine ⟨66838891428324671956033805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44559260952216447970689203 66838891428324671956033805)
              ·
                refine ⟨25064584285621751983512677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66838891428324671956033805 25064584285621751983512677)
                ·
                  refine ⟨4699609553554078496908627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25064584285621751983512677 4699609553554078496908627)
                  ·
                    refine ⟨7049414330331117745362941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699609553554078496908627 7049414330331117745362941)
                    ·
                      refine ⟨2643530373874169154511103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049414330331117745362941 2643530373874169154511103)
                      ·
                        rfl

theorem cell23_5148257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_5148257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148257 prefixEnd_5148257 := by exact prefixLift 5148257
  have htrace : WordTrace (prefixWord ++ tailWord_5148257) baseStart_5148257 baseEnd_5148257 := by
    simpa [prefixWord, tailWord_5148257, baseEnd_5148257] using wordTrace_append hprefix tailTrace_5148257
  have hstable : (prefixWord ++ tailWord_5148257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148257).length < 2 ^ (prefixWord ++ tailWord_5148257).sum := by decide
  have hdescent : baseEnd_5148257 < baseStart_5148257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148297 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 3, 4, 2]
def baseStart_5148297 : Nat := 118140960795 + 5148297 * 2 ^ 59
def prefixEnd_5148297 : Nat := 4983230072969 + 3 ^ 40 * 5148297 * 2
def baseEnd_5148297 : Nat := 2643550913100348998010919

theorem tailTrace_5148297 : CollatzResearch.WordTrace tailWord_5148297 prefixEnd_5148297 2643550913100348998010919 := by
  unfold tailWord_5148297
  simp only [CollatzResearch.WordTrace]
  refine ⟨187773817829606702971315145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125182545219737801980876763 187773817829606702971315145)
  ·
    refine ⟨140830363372205027228486359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187773817829606702971315145 140830363372205027228486359)
    ·
      refine ⟨211245545058307540842729539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140830363372205027228486359 211245545058307540842729539)
      ·
        refine ⟨316868317587461311264094309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211245545058307540842729539 316868317587461311264094309)
        ·
          refine ⟨59412809547648995862017683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 316868317587461311264094309 59412809547648995862017683)
          ·
            refine ⟨89119214321473493793026525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59412809547648995862017683 89119214321473493793026525)
            ·
              refine ⟨33419705370552560172384947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89119214321473493793026525 33419705370552560172384947)
              ·
                refine ⟨50129558055828840258577421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33419705370552560172384947 50129558055828840258577421)
                ·
                  refine ⟨18798584270935815096966533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50129558055828840258577421 18798584270935815096966533)
                  ·
                    refine ⟨3524734550800465330681225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18798584270935815096966533 3524734550800465330681225)
                    ·
                      refine ⟨2643550913100348998010919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524734550800465330681225 2643550913100348998010919)
                      ·
                        rfl

theorem cell23_5148297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 4, 2].length) (baseStart_5148297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148297 prefixEnd_5148297 := by exact prefixLift 5148297
  have htrace : WordTrace (prefixWord ++ tailWord_5148297) baseStart_5148297 baseEnd_5148297 := by
    simpa [prefixWord, tailWord_5148297, baseEnd_5148297] using wordTrace_append hprefix tailTrace_5148297
  have hstable : (prefixWord ++ tailWord_5148297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148297).length < 2 ^ (prefixWord ++ tailWord_5148297).sum := by decide
  have hdescent : baseEnd_5148297 < baseStart_5148297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148300 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_5148300 : Nat := 118140960795 + 5148300 * 2 ^ 59
def prefixEnd_5148300 : Nat := 4983230072969 + 3 ^ 40 * 5148300 * 2
def baseEnd_5148300 : Nat := 2643552453542312486273405

theorem tailTrace_5148300 : CollatzResearch.WordTrace tailWord_5148300 prefixEnd_5148300 2643552453542312486273405 := by
  unfold tailWord_5148300
  simp only [CollatzResearch.WordTrace]
  refine ⟨93886963624297917241837177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125182618165730556322449569 93886963624297917241837177)
  ·
    refine ⟨70415222718223437931377883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93886963624297917241837177 70415222718223437931377883)
    ·
      refine ⟨105622834077335156897066825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70415222718223437931377883 105622834077335156897066825)
      ·
        refine ⟨79217125558001367672800119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105622834077335156897066825 79217125558001367672800119)
        ·
          refine ⟨118825688337002051509200179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79217125558001367672800119 118825688337002051509200179)
          ·
            refine ⟨178238532505503077263800269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118825688337002051509200179 178238532505503077263800269)
            ·
              refine ⟨66839449689563653973925101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178238532505503077263800269 66839449689563653973925101)
              ·
                refine ⟨25064793633586370240221913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66839449689563653973925101 25064793633586370240221913)
                ·
                  refine ⟨18798595225189777680166435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25064793633586370240221913 18798595225189777680166435)
                  ·
                    refine ⟨28197892837784666520249653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18798595225189777680166435 28197892837784666520249653)
                    ·
                      refine ⟨2643552453542312486273405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28197892837784666520249653 2643552453542312486273405)
                      ·
                        rfl

theorem cell23_5148300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_5148300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148300 prefixEnd_5148300 := by exact prefixLift 5148300
  have htrace : WordTrace (prefixWord ++ tailWord_5148300) baseStart_5148300 baseEnd_5148300 := by
    simpa [prefixWord, tailWord_5148300, baseEnd_5148300] using wordTrace_append hprefix tailTrace_5148300
  have hstable : (prefixWord ++ tailWord_5148300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148300).length < 2 ^ (prefixWord ++ tailWord_5148300).sum := by decide
  have hdescent : baseEnd_5148300 < baseStart_5148300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148308 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_5148308 : Nat := 118140960795 + 5148308 * 2 ^ 59
def prefixEnd_5148308 : Nat := 4983230072969 + 3 ^ 40 * 5148308 * 2
def baseEnd_5148308 : Nat := 2643556561387548454973369

theorem tailTrace_5148308 : CollatzResearch.WordTrace tailWord_5148308 prefixEnd_5148308 2643556561387548454973369 := by
  unfold tailWord_5148308
  simp only [CollatzResearch.WordTrace]
  refine ⟨93887109516283425924982789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125182812688377901233310385 93887109516283425924982789)
  ·
    refine ⟨17603833034303142360934273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93887109516283425924982789 17603833034303142360934273)
    ·
      refine ⟨13202874775727356770700705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17603833034303142360934273 13202874775727356770700705)
      ·
        refine ⟨9902156081795517578025529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13202874775727356770700705 9902156081795517578025529)
        ·
          refine ⟨7426617061346638183519147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9902156081795517578025529 7426617061346638183519147)
          ·
            refine ⟨11139925592019957275278721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7426617061346638183519147 11139925592019957275278721)
            ·
              refine ⟨8354944194014967956459041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11139925592019957275278721 8354944194014967956459041)
              ·
                refine ⟨6266208145511225967344281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8354944194014967956459041 6266208145511225967344281)
                ·
                  refine ⟨4699656109133419475508211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6266208145511225967344281 4699656109133419475508211)
                  ·
                    refine ⟨7049484163700129213262317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699656109133419475508211 7049484163700129213262317)
                    ·
                      refine ⟨2643556561387548454973369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049484163700129213262317 2643556561387548454973369)
                      ·
                        rfl

theorem cell23_5148308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_5148308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148308 prefixEnd_5148308 := by exact prefixLift 5148308
  have htrace : WordTrace (prefixWord ++ tailWord_5148308) baseStart_5148308 baseEnd_5148308 := by
    simpa [prefixWord, tailWord_5148308, baseEnd_5148308] using wordTrace_append hprefix tailTrace_5148308
  have hstable : (prefixWord ++ tailWord_5148308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148308).length < 2 ^ (prefixWord ++ tailWord_5148308).sum := by decide
  have hdescent : baseEnd_5148308 < baseStart_5148308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148357 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 4, 5, 2]
def baseStart_5148357 : Nat := 118140960795 + 5148357 * 2 ^ 59
def prefixEnd_5148357 : Nat := 4983230072969 + 3 ^ 40 * 5148357 * 2
def baseEnd_5148357 : Nat := 2643581721939618763260643

theorem tailTrace_5148357 : CollatzResearch.WordTrace tailWord_5148357 prefixEnd_5148357 2643581721939618763260643 := by
  unfold tailWord_5148357
  simp only [CollatzResearch.WordTrace]
  refine ⟨187776006209389333218499325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125184004139592888812332883 187776006209389333218499325)
  ·
    refine ⟨70416002328520999956937247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187776006209389333218499325 70416002328520999956937247)
    ·
      refine ⟨105624003492781499935405871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70416002328520999956937247 105624003492781499935405871)
      ·
        refine ⟨158436005239172249903108807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105624003492781499935405871 158436005239172249903108807)
        ·
          refine ⟨237654007858758374854663211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158436005239172249903108807 237654007858758374854663211)
          ·
            refine ⟨356481011788137562281994817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237654007858758374854663211 356481011788137562281994817)
            ·
              refine ⟨267360758841103171711496113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356481011788137562281994817 267360758841103171711496113)
              ·
                refine ⟨200520569130827378783622085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267360758841103171711496113 200520569130827378783622085)
                ·
                  refine ⟨37597606712030133521929141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200520569130827378783622085 37597606712030133521929141)
                  ·
                    refine ⟨3524775629252825017680857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37597606712030133521929141 3524775629252825017680857)
                    ·
                      refine ⟨2643581721939618763260643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524775629252825017680857 2643581721939618763260643)
                      ·
                        rfl

theorem cell23_5148357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_5148357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148357 prefixEnd_5148357 := by exact prefixLift 5148357
  have htrace : WordTrace (prefixWord ++ tailWord_5148357) baseStart_5148357 baseEnd_5148357 := by
    simpa [prefixWord, tailWord_5148357, baseEnd_5148357] using wordTrace_append hprefix tailTrace_5148357
  have hstable : (prefixWord ++ tailWord_5148357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148357).length < 2 ^ (prefixWord ++ tailWord_5148357).sum := by decide
  have hdescent : baseEnd_5148357 < baseStart_5148357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148365 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5148365 : Nat := 118140960795 + 5148365 * 2 ^ 59
def prefixEnd_5148365 : Nat := 4983230072969 + 3 ^ 40 * 5148365 * 2
def baseEnd_5148365 : Nat := 2643585829784854731960607

theorem tailTrace_5148365 : CollatzResearch.WordTrace tailWord_5148365 prefixEnd_5148365 2643585829784854731960607 := by
  unfold tailWord_5148365
  simp only [CollatzResearch.WordTrace]
  refine ⟨187776297993360350584790549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125184198662240233723193699 187776297993360350584790549)
  ·
    refine ⟨8802013968438766433662057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187776297993360350584790549 8802013968438766433662057)
    ·
      refine ⟨6601510476329074825246543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8802013968438766433662057 6601510476329074825246543)
      ·
        refine ⟨9902265714493612237869815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6601510476329074825246543 9902265714493612237869815)
        ·
          refine ⟨14853398571740418356804723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9902265714493612237869815 14853398571740418356804723)
          ·
            refine ⟨22280097857610627535207085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14853398571740418356804723 22280097857610627535207085)
            ·
              refine ⟨8355036696603985325702657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22280097857610627535207085 8355036696603985325702657)
              ·
                refine ⟨6266277522452988994276993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8355036696603985325702657 6266277522452988994276993)
                ·
                  refine ⟨4699708141839741745707745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6266277522452988994276993 4699708141839741745707745)
                  ·
                    refine ⟨3524781106379806309280809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4699708141839741745707745 3524781106379806309280809)
                    ·
                      refine ⟨2643585829784854731960607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524781106379806309280809 2643585829784854731960607)
                      ·
                        rfl

theorem cell23_5148365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5148365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148365 prefixEnd_5148365 := by exact prefixLift 5148365
  have htrace : WordTrace (prefixWord ++ tailWord_5148365) baseStart_5148365 baseEnd_5148365 := by
    simpa [prefixWord, tailWord_5148365, baseEnd_5148365] using wordTrace_append hprefix tailTrace_5148365
  have hstable : (prefixWord ++ tailWord_5148365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148365).length < 2 ^ (prefixWord ++ tailWord_5148365).sum := by decide
  have hdescent : baseEnd_5148365 < baseStart_5148365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148400 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_5148400 : Nat := 118140960795 + 5148400 * 2 ^ 59
def prefixEnd_5148400 : Nat := 4983230072969 + 3 ^ 40 * 5148400 * 2
def baseEnd_5148400 : Nat := 2643603801607762095022945

theorem tailTrace_5148400 : CollatzResearch.WordTrace tailWord_5148400 prefixEnd_5148400 2643603801607762095022945 := by
  unfold tailWord_5148400
  simp only [CollatzResearch.WordTrace]
  refine ⟨93888787274116775781157327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125185049698822367708209769 93888787274116775781157327)
  ·
    refine ⟨140833180911175163671735991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93888787274116775781157327 140833180911175163671735991)
    ·
      refine ⟨211249771366762745507603987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140833180911175163671735991 211249771366762745507603987)
      ·
        refine ⟨316874657050144118261405981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211249771366762745507603987 316874657050144118261405981)
        ·
          refine ⟨118827996393804044348027243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316874657050144118261405981 118827996393804044348027243)
          ·
            refine ⟨178241994590706066522040865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118827996393804044348027243 178241994590706066522040865)
            ·
              refine ⟨133681495943029549891530649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178241994590706066522040865 133681495943029549891530649)
              ·
                refine ⟨100261121957272162418647987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133681495943029549891530649 100261121957272162418647987)
                ·
                  refine ⟨150391682935908243627971981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100261121957272162418647987 150391682935908243627971981)
                  ·
                    refine ⟨56396881100965591360489493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150391682935908243627971981 56396881100965591360489493)
                    ·
                      refine ⟨2643603801607762095022945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56396881100965591360489493 2643603801607762095022945)
                      ·
                        rfl

theorem cell23_5148400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_5148400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148400 prefixEnd_5148400 := by exact prefixLift 5148400
  have htrace : WordTrace (prefixWord ++ tailWord_5148400) baseStart_5148400 baseEnd_5148400 := by
    simpa [prefixWord, tailWord_5148400, baseEnd_5148400] using wordTrace_append hprefix tailTrace_5148400
  have hstable : (prefixWord ++ tailWord_5148400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148400).length < 2 ^ (prefixWord ++ tailWord_5148400).sum := by decide
  have hdescent : baseEnd_5148400 < baseStart_5148400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148407 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_5148407 : Nat := 118140960795 + 5148407 * 2 ^ 59
def prefixEnd_5148407 : Nat := 4983230072969 + 3 ^ 40 * 5148407 * 2
def baseEnd_5148407 : Nat := 2643607395972343567635413

theorem tailTrace_5148407 : CollatzResearch.WordTrace tailWord_5148407 prefixEnd_5148407 2643607395972343567635413 := by
  unfold tailWord_5148407
  simp only [CollatzResearch.WordTrace]
  refine ⟨187777829859208191757819475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125185219906138794505212983 187777829859208191757819475)
  ·
    refine ⟨281666744788812287636729213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187777829859208191757819475 281666744788812287636729213)
    ·
      refine ⟨105625029295804607863773455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281666744788812287636729213 105625029295804607863773455)
      ·
        refine ⟨158437543943706911795660183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105625029295804607863773455 158437543943706911795660183)
        ·
          refine ⟨237656315915560367693490275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158437543943706911795660183 237656315915560367693490275)
          ·
            refine ⟨356484473873340551540235413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237656315915560367693490275 356484473873340551540235413)
            ·
              refine ⟨16710209712812838353448535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 356484473873340551540235413 16710209712812838353448535)
              ·
                refine ⟨25065314569219257530172803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16710209712812838353448535 25065314569219257530172803)
                ·
                  refine ⟨37597971853828886295259205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25065314569219257530172803 37597971853828886295259205)
                  ·
                    refine ⟨7049619722592916180361101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37597971853828886295259205 7049619722592916180361101)
                    ·
                      refine ⟨2643607395972343567635413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049619722592916180361101 2643607395972343567635413)
                      ·
                        rfl

theorem cell23_5148407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_5148407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148407 prefixEnd_5148407 := by exact prefixLift 5148407
  have htrace : WordTrace (prefixWord ++ tailWord_5148407) baseStart_5148407 baseEnd_5148407 := by
    simpa [prefixWord, tailWord_5148407, baseEnd_5148407] using wordTrace_append hprefix tailTrace_5148407
  have hstable : (prefixWord ++ tailWord_5148407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148407).length < 2 ^ (prefixWord ++ tailWord_5148407).sum := by decide
  have hdescent : baseEnd_5148407 < baseStart_5148407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148422 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_5148422 : Nat := 118140960795 + 5148422 * 2 ^ 59
def prefixEnd_5148422 : Nat := 4983230072969 + 3 ^ 40 * 5148422 * 2
def baseEnd_5148422 : Nat := 293735010909129000994205

theorem tailTrace_5148422 : CollatzResearch.WordTrace tailWord_5148422 prefixEnd_5148422 293735010909129000994205 := by
  unfold tailWord_5148422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868074279817307791237985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125185584636102566213077013 5868074279817307791237985)
  ·
    refine ⟨4401055709862980843428489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5868074279817307791237985 4401055709862980843428489)
    ·
      refine ⟨3300791782397235632571367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4401055709862980843428489 3300791782397235632571367)
      ·
        refine ⟨4951187673595853448857051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300791782397235632571367 4951187673595853448857051)
        ·
          refine ⟨7426781510393780173285577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4951187673595853448857051 7426781510393780173285577)
          ·
            refine ⟨5570086132795335129964183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7426781510393780173285577 5570086132795335129964183)
            ·
              refine ⟨8355129199193002694946275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570086132795335129964183 8355129199193002694946275)
              ·
                refine ⟨12532693798789504042419413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8355129199193002694946275 12532693798789504042419413)
                ·
                  refine ⟨293735010909129000994205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12532693798789504042419413 293735010909129000994205)
                  ·
                    rfl

theorem cell23_5148422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_5148422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148422 prefixEnd_5148422 := by exact prefixLift 5148422
  have htrace : WordTrace (prefixWord ++ tailWord_5148422) baseStart_5148422 baseEnd_5148422 := by
    simpa [prefixWord, tailWord_5148422, baseEnd_5148422] using wordTrace_append hprefix tailTrace_5148422
  have hstable : (prefixWord ++ tailWord_5148422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148422).length < 2 ^ (prefixWord ++ tailWord_5148422).sum := by decide
  have hdescent : baseEnd_5148422 < baseStart_5148422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148424 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_5148424 : Nat := 118140960795 + 5148424 * 2 ^ 59
def prefixEnd_5148424 : Nat := 4983230072969 + 3 ^ 40 * 5148424 * 2
def baseEnd_5148424 : Nat := 2643616125143470001122835

theorem tailTrace_5148424 : CollatzResearch.WordTrace tailWord_5148424 prefixEnd_5148424 2643616125143470001122835 := by
  unfold tailWord_5148424
  simp only [CollatzResearch.WordTrace]
  refine ⟨93889224950073301830594163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125185633266764402440792217 93889224950073301830594163)
  ·
    refine ⟨140833837425109952745891245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93889224950073301830594163 140833837425109952745891245)
    ·
      refine ⟨52812689034416232279709217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140833837425109952745891245 52812689034416232279709217)
      ·
        refine ⟨39609516775812174209781913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52812689034416232279709217 39609516775812174209781913)
        ·
          refine ⟨29707137581859130657336435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39609516775812174209781913 29707137581859130657336435)
          ·
            refine ⟨44560706372788695986004653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29707137581859130657336435 44560706372788695986004653)
            ·
              refine ⟨16710264889795760994751745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44560706372788695986004653 16710264889795760994751745)
              ·
                refine ⟨12532698667346820746063809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16710264889795760994751745 12532698667346820746063809)
                ·
                  refine ⟨9399524000510115559547857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12532698667346820746063809 9399524000510115559547857)
                  ·
                    refine ⟨7049643000382586669660893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9399524000510115559547857 7049643000382586669660893)
                    ·
                      refine ⟨2643616125143470001122835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049643000382586669660893 2643616125143470001122835)
                      ·
                        rfl

theorem cell23_5148424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_5148424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148424 prefixEnd_5148424 := by exact prefixLift 5148424
  have htrace : WordTrace (prefixWord ++ tailWord_5148424) baseStart_5148424 baseEnd_5148424 := by
    simpa [prefixWord, tailWord_5148424, baseEnd_5148424] using wordTrace_append hprefix tailTrace_5148424
  have hstable : (prefixWord ++ tailWord_5148424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148424).length < 2 ^ (prefixWord ++ tailWord_5148424).sum := by decide
  have hdescent : baseEnd_5148424 < baseStart_5148424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148488 : List Nat := [2, 1, 3, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_5148488 : Nat := 118140960795 + 5148488 * 2 ^ 59
def prefixEnd_5148488 : Nat := 4983230072969 + 3 ^ 40 * 5148488 * 2
def baseEnd_5148488 : Nat := 2643648987905357750722541

theorem tailTrace_5148488 : CollatzResearch.WordTrace tailWord_5148488 prefixEnd_5148488 2643648987905357750722541 := by
  unfold tailWord_5148488
  simp only [CollatzResearch.WordTrace]
  refine ⟨93890392085957371295759059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125187189447943161727678745 93890392085957371295759059)
  ·
    refine ⟨140835588128936056943638589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93890392085957371295759059 140835588128936056943638589)
    ·
      refine ⟨52813345548351021353864471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140835588128936056943638589 52813345548351021353864471)
      ·
        refine ⟨79220018322526532030796707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52813345548351021353864471 79220018322526532030796707)
        ·
          refine ⟨118830027483789798046195061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79220018322526532030796707 118830027483789798046195061)
          ·
            refine ⟨11140315076605293566830787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118830027483789798046195061 11140315076605293566830787)
            ·
              refine ⟨16710472614907940350246181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11140315076605293566830787 16710472614907940350246181)
              ·
                refine ⟨3133213615295238815671159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16710472614907940350246181 3133213615295238815671159)
                ·
                  refine ⟨4699820422942858223506739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133213615295238815671159 4699820422942858223506739)
                  ·
                    refine ⟨7049730634414287335260109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699820422942858223506739 7049730634414287335260109)
                    ·
                      refine ⟨2643648987905357750722541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049730634414287335260109 2643648987905357750722541)
                      ·
                        rfl

theorem cell23_5148488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_5148488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148488 prefixEnd_5148488 := by exact prefixLift 5148488
  have htrace : WordTrace (prefixWord ++ tailWord_5148488) baseStart_5148488 baseEnd_5148488 := by
    simpa [prefixWord, tailWord_5148488, baseEnd_5148488] using wordTrace_append hprefix tailTrace_5148488
  have hstable : (prefixWord ++ tailWord_5148488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148488).length < 2 ^ (prefixWord ++ tailWord_5148488).sum := by decide
  have hdescent : baseEnd_5148488 < baseStart_5148488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148494 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_5148494 : Nat := 118140960795 + 5148494 * 2 ^ 59
def prefixEnd_5148494 : Nat := 4983230072969 + 3 ^ 40 * 5148494 * 2
def baseEnd_5148494 : Nat := 2643652068789284727247513

theorem tailTrace_5148494 : CollatzResearch.WordTrace tailWord_5148494 prefixEnd_5148494 2643652068789284727247513 := by
  unfold tailWord_5148494
  simp only [CollatzResearch.WordTrace]
  refine ⟨23472625376236625702029567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125187335339928670410824357 23472625376236625702029567)
  ·
    refine ⟨35208938064354938553044351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23472625376236625702029567 35208938064354938553044351)
    ·
      refine ⟨52813407096532407829566527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35208938064354938553044351 52813407096532407829566527)
      ·
        refine ⟨79220110644798611744349791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52813407096532407829566527 79220110644798611744349791)
        ·
          refine ⟨118830165967197917616524687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79220110644798611744349791 118830165967197917616524687)
          ·
            refine ⟨178245248950796876424787031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118830165967197917616524687 178245248950796876424787031)
            ·
              refine ⟨267367873426195314637180547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178245248950796876424787031 267367873426195314637180547)
              ·
                refine ⟨401051810139292971955770821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267367873426195314637180547 401051810139292971955770821)
                ·
                  refine ⟨75197214401117432241707029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 401051810139292971955770821 75197214401117432241707029)
                  ·
                    refine ⟨3524869425052379636330017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75197214401117432241707029 3524869425052379636330017)
                    ·
                      refine ⟨2643652068789284727247513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524869425052379636330017 2643652068789284727247513)
                      ·
                        rfl

theorem cell23_5148494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_5148494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148494 prefixEnd_5148494 := by exact prefixLift 5148494
  have htrace : WordTrace (prefixWord ++ tailWord_5148494) baseStart_5148494 baseEnd_5148494 := by
    simpa [prefixWord, tailWord_5148494, baseEnd_5148494] using wordTrace_append hprefix tailTrace_5148494
  have hstable : (prefixWord ++ tailWord_5148494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148494).length < 2 ^ (prefixWord ++ tailWord_5148494).sum := by decide
  have hdescent : baseEnd_5148494 < baseStart_5148494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148511 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 5, 2, 2]
def baseStart_5148511 : Nat := 118140960795 + 5148511 * 2 ^ 59
def prefixEnd_5148511 : Nat := 4983230072969 + 3 ^ 40 * 5148511 * 2
def baseEnd_5148511 : Nat := 2643660797960411160734935

theorem tailTrace_5148511 : CollatzResearch.WordTrace tailWord_5148511 prefixEnd_5148511 2643660797960411160734935 := by
  unfold tailWord_5148511
  simp only [CollatzResearch.WordTrace]
  refine ⟨187781623050831417519605387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125187748700554278346403591 187781623050831417519605387)
  ·
    refine ⟨281672434576247126279408081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187781623050831417519605387 281672434576247126279408081)
    ·
      refine ⟨211254325932185344709556061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281672434576247126279408081 211254325932185344709556061)
      ·
        refine ⟨79220372224569504266083523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211254325932185344709556061 79220372224569504266083523)
        ·
          refine ⟨118830558336854256399125285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79220372224569504266083523 118830558336854256399125285)
          ·
            refine ⟨22280729688160173074835991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118830558336854256399125285 22280729688160173074835991)
            ·
              refine ⟨33421094532240259612253987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22280729688160173074835991 33421094532240259612253987)
              ·
                refine ⟨50131641798360389418380981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33421094532240259612253987 50131641798360389418380981)
                ·
                  refine ⟨4699841418596286507973217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50131641798360389418380981 4699841418596286507973217)
                  ·
                    refine ⟨3524881063947214880979913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4699841418596286507973217 3524881063947214880979913)
                    ·
                      refine ⟨2643660797960411160734935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524881063947214880979913 2643660797960411160734935)
                      ·
                        rfl

theorem cell23_5148511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_5148511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148511 prefixEnd_5148511 := by exact prefixLift 5148511
  have htrace : WordTrace (prefixWord ++ tailWord_5148511) baseStart_5148511 baseEnd_5148511 := by
    simpa [prefixWord, tailWord_5148511, baseEnd_5148511] using wordTrace_append hprefix tailTrace_5148511
  have hstable : (prefixWord ++ tailWord_5148511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148511).length < 2 ^ (prefixWord ++ tailWord_5148511).sum := by decide
  have hdescent : baseEnd_5148511 < baseStart_5148511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148515 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 2, 3, 2]
def baseStart_5148515 : Nat := 118140960795 + 5148515 * 2 ^ 59
def prefixEnd_5148515 : Nat := 4983230072969 + 3 ^ 40 * 5148515 * 2
def baseEnd_5148515 : Nat := 2643662851883029145084917

theorem tailTrace_5148515 : CollatzResearch.WordTrace tailWord_5148515 prefixEnd_5148515 2643662851883029145084917 := by
  unfold tailWord_5148515
  simp only [CollatzResearch.WordTrace]
  refine ⟨187781768942816926202750999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125187845961877950801833999 187781768942816926202750999)
  ·
    refine ⟨281672653414225389304126499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187781768942816926202750999 281672653414225389304126499)
    ·
      refine ⟨422508980121338083956189749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281672653414225389304126499 422508980121338083956189749)
      ·
        refine ⟨39610216886375445370892789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 422508980121338083956189749 39610216886375445370892789)
        ·
          refine ⟨3713457833097698003521199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39610216886375445370892789 3713457833097698003521199)
          ·
            refine ⟨5570186749646547005281799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713457833097698003521199 5570186749646547005281799)
            ·
              refine ⟨8355280124469820507922699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570186749646547005281799 8355280124469820507922699)
              ·
                refine ⟨12532920186704730761884049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8355280124469820507922699 12532920186704730761884049)
                ·
                  refine ⟨9399690140028548071413037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12532920186704730761884049 9399690140028548071413037)
                  ·
                    refine ⟨3524883802510705526779889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9399690140028548071413037 3524883802510705526779889)
                    ·
                      refine ⟨2643662851883029145084917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524883802510705526779889 2643662851883029145084917)
                      ·
                        rfl

theorem cell23_5148515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_5148515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148515 prefixEnd_5148515 := by exact prefixLift 5148515
  have htrace : WordTrace (prefixWord ++ tailWord_5148515) baseStart_5148515 baseEnd_5148515 := by
    simpa [prefixWord, tailWord_5148515, baseEnd_5148515] using wordTrace_append hprefix tailTrace_5148515
  have hstable : (prefixWord ++ tailWord_5148515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148515).length < 2 ^ (prefixWord ++ tailWord_5148515).sum := by decide
  have hdescent : baseEnd_5148515 < baseStart_5148515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148522 : List Nat := [3, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5148522 : Nat := 118140960795 + 5148522 * 2 ^ 59
def prefixEnd_5148522 : Nat := 4983230072969 + 3 ^ 40 * 5148522 * 2
def baseEnd_5148522 : Nat := 2643666446247610617697385

theorem tailTrace_5148522 : CollatzResearch.WordTrace tailWord_5148522 prefixEnd_5148522 2643666446247610617697385 := by
  unfold tailWord_5148522
  simp only [CollatzResearch.WordTrace]
  refine ⟨46945506063447891599563955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125188016169194377598837213 46945506063447891599563955)
  ·
    refine ⟨70418259095171837399345933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46945506063447891599563955 70418259095171837399345933)
    ·
      refine ⟨26406847160689439024754725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70418259095171837399345933 26406847160689439024754725)
      ·
        refine ⟨4951283842629269817141511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26406847160689439024754725 4951283842629269817141511)
        ·
          refine ⟨7426925763943904725712267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4951283842629269817141511 7426925763943904725712267)
          ·
            refine ⟨11140388645915857088568401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7426925763943904725712267 11140388645915857088568401)
            ·
              refine ⟨8355291484436892816426301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11140388645915857088568401 8355291484436892816426301)
              ·
                refine ⟨3133234306663834806159863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8355291484436892816426301 3133234306663834806159863)
                ·
                  refine ⟨4699851459995752209239795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133234306663834806159863 4699851459995752209239795)
                  ·
                    refine ⟨7049777189993628313859693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699851459995752209239795 7049777189993628313859693)
                    ·
                      refine ⟨2643666446247610617697385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049777189993628313859693 2643666446247610617697385)
                      ·
                        rfl

theorem cell23_5148522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5148522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148522 prefixEnd_5148522 := by exact prefixLift 5148522
  have htrace : WordTrace (prefixWord ++ tailWord_5148522) baseStart_5148522 baseEnd_5148522 := by
    simpa [prefixWord, tailWord_5148522, baseEnd_5148522] using wordTrace_append hprefix tailTrace_5148522
  have hstable : (prefixWord ++ tailWord_5148522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148522).length < 2 ^ (prefixWord ++ tailWord_5148522).sum := by decide
  have hdescent : baseEnd_5148522 < baseStart_5148522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148524 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_5148524 : Nat := 118140960795 + 5148524 * 2 ^ 59
def prefixEnd_5148524 : Nat := 4983230072969 + 3 ^ 40 * 5148524 * 2
def baseEnd_5148524 : Nat := 2643667473208919609872375

theorem tailTrace_5148524 : CollatzResearch.WordTrace tailWord_5148524 prefixEnd_5148524 2643667473208919609872375 := by
  unfold tailWord_5148524
  simp only [CollatzResearch.WordTrace]
  refine ⟨93891048599892160369914313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125188064799856213826552417 93891048599892160369914313)
  ·
    refine ⟨70418286449919120277435735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93891048599892160369914313 70418286449919120277435735)
    ·
      refine ⟨105627429674878680416153603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70418286449919120277435735 105627429674878680416153603)
      ·
        refine ⟨158441144512318020624230405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105627429674878680416153603 158441144512318020624230405)
        ·
          refine ⟨29707714596059628867043201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158441144512318020624230405 29707714596059628867043201)
          ·
            refine ⟨22280785947044721650282401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29707714596059628867043201 22280785947044721650282401)
            ·
              refine ⟨16710589460283541237711801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22280785947044721650282401 16710589460283541237711801)
              ·
                refine ⟨12532942095212655928283851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16710589460283541237711801 12532942095212655928283851)
                ·
                  refine ⟨18799413142818983892425777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12532942095212655928283851 18799413142818983892425777)
                  ·
                    refine ⟨14099559857114237919319333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18799413142818983892425777 14099559857114237919319333)
                    ·
                      refine ⟨2643667473208919609872375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14099559857114237919319333 2643667473208919609872375)
                      ·
                        rfl

theorem cell23_5148524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_5148524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148524 prefixEnd_5148524 := by exact prefixLift 5148524
  have htrace : WordTrace (prefixWord ++ tailWord_5148524) baseStart_5148524 baseEnd_5148524 := by
    simpa [prefixWord, tailWord_5148524, baseEnd_5148524] using wordTrace_append hprefix tailTrace_5148524
  have hstable : (prefixWord ++ tailWord_5148524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148524).length < 2 ^ (prefixWord ++ tailWord_5148524).sum := by decide
  have hdescent : baseEnd_5148524 < baseStart_5148524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148561 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_5148561 : Nat := 118140960795 + 5148561 * 2 ^ 59
def prefixEnd_5148561 : Nat := 4983230072969 + 3 ^ 40 * 5148561 * 2
def baseEnd_5148561 : Nat := 2643686471993135965109705

theorem tailTrace_5148561 : CollatzResearch.WordTrace tailWord_5148561 prefixEnd_5148561 2643686471993135965109705 := by
  unfold tailWord_5148561
  simp only [CollatzResearch.WordTrace]
  refine ⟨187783446700650276058925537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125188964467100184039283691 187783446700650276058925537)
  ·
    refine ⟨140837585025487707044194153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187783446700650276058925537 140837585025487707044194153)
    ·
      refine ⟨105628188769115780283145615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140837585025487707044194153 105628188769115780283145615)
      ·
        refine ⟨158442283153673670424718423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105628188769115780283145615 158442283153673670424718423)
        ·
          refine ⟨237663424730510505637077635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158442283153673670424718423 237663424730510505637077635)
          ·
            refine ⟨356495137095765758455616453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237663424730510505637077635 356495137095765758455616453)
            ·
              refine ⟨66842838205456079710428085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 356495137095765758455616453 66842838205456079710428085)
              ·
                refine ⟨6266516081761507472852633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66842838205456079710428085 6266516081761507472852633)
                ·
                  refine ⟨4699887061321130604639475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6266516081761507472852633 4699887061321130604639475)
                  ·
                    refine ⟨7049830591981695906959213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699887061321130604639475 7049830591981695906959213)
                    ·
                      refine ⟨2643686471993135965109705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7049830591981695906959213 2643686471993135965109705)
                      ·
                        rfl

theorem cell23_5148561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_5148561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148561 prefixEnd_5148561 := by exact prefixLift 5148561
  have htrace : WordTrace (prefixWord ++ tailWord_5148561) baseStart_5148561 baseEnd_5148561 := by
    simpa [prefixWord, tailWord_5148561, baseEnd_5148561] using wordTrace_append hprefix tailTrace_5148561
  have hstable : (prefixWord ++ tailWord_5148561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148561).length < 2 ^ (prefixWord ++ tailWord_5148561).sum := by decide
  have hdescent : baseEnd_5148561 < baseStart_5148561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148568 : List Nat := [2, 1, 2, 6, 1, 2, 2, 7]
def baseStart_5148568 : Nat := 118140960795 + 5148568 * 2 ^ 59
def prefixEnd_5148568 : Nat := 4983230072969 + 3 ^ 40 * 5148568 * 2
def baseEnd_5148568 : Nat := 97914446902137682878599

theorem tailTrace_5148568 : CollatzResearch.WordTrace tailWord_5148568 prefixEnd_5148568 97914446902137682878599 := by
  unfold tailWord_5148568
  simp only [CollatzResearch.WordTrace]
  refine ⟨93891851005812458127215179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125189134674416610836286905 93891851005812458127215179)
  ·
    refine ⟨140837776508718687190822769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93891851005812458127215179 140837776508718687190822769)
    ·
      refine ⟨105628332381539015393117077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140837776508718687190822769 105628332381539015393117077)
      ·
        refine ⟨4951328080384641346552363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105628332381539015393117077 4951328080384641346552363)
        ·
          refine ⟨7426992120576962019828545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4951328080384641346552363 7426992120576962019828545)
          ·
            refine ⟨5570244090432721514871409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7426992120576962019828545 5570244090432721514871409)
            ·
              refine ⟨4177683067824541136153557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570244090432721514871409 4177683067824541136153557)
              ·
                refine ⟨97914446902137682878599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4177683067824541136153557 97914446902137682878599)
                ·
                  rfl

theorem cell23_5148568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 7].length) (baseStart_5148568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148568 prefixEnd_5148568 := by exact prefixLift 5148568
  have htrace : WordTrace (prefixWord ++ tailWord_5148568) baseStart_5148568 baseEnd_5148568 := by
    simpa [prefixWord, tailWord_5148568, baseEnd_5148568] using wordTrace_append hprefix tailTrace_5148568
  have hstable : (prefixWord ++ tailWord_5148568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148568).length < 2 ^ (prefixWord ++ tailWord_5148568).sum := by decide
  have hdescent : baseEnd_5148568 < baseStart_5148568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148596 : List Nat := [2, 5, 2, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_5148596 : Nat := 118140960795 + 5148596 * 2 ^ 59
def prefixEnd_5148596 : Nat := 4983230072969 + 3 ^ 40 * 5148596 * 2
def baseEnd_5148596 : Nat := 2643704443816043328172045

theorem tailTrace_5148596 : CollatzResearch.WordTrace tailWord_5148596 prefixEnd_5148596 2643704443816043328172045 := by
  unfold tailWord_5148596
  simp only [CollatzResearch.WordTrace]
  refine ⟨93892361627761738518224821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125189815503682318024299761 93892361627761738518224821)
  ·
    refine ⟨8802408902602662986083577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93892361627761738518224821 8802408902602662986083577)
    ·
      refine ⟨6601806676951997239562683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8802408902602662986083577 6601806676951997239562683)
      ·
        refine ⟨9902710015427995859344025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6601806676951997239562683 9902710015427995859344025)
        ·
          refine ⟨7427032511570996894508019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9902710015427995859344025 7427032511570996894508019)
          ·
            refine ⟨11140548767356495341762029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7427032511570996894508019 11140548767356495341762029)
            ·
              refine ⟨4177705787758685753160761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11140548767356495341762029 4177705787758685753160761)
              ·
                refine ⟨3133279340819014314870571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4177705787758685753160761 3133279340819014314870571)
                ·
                  refine ⟨4699919011228521472305857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133279340819014314870571 4699919011228521472305857)
                  ·
                    refine ⟨3524939258421391104229393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4699919011228521472305857 3524939258421391104229393)
                    ·
                      refine ⟨2643704443816043328172045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3524939258421391104229393 2643704443816043328172045)
                      ·
                        rfl

theorem cell23_5148596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_5148596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148596 prefixEnd_5148596 := by exact prefixLift 5148596
  have htrace : WordTrace (prefixWord ++ tailWord_5148596) baseStart_5148596 baseEnd_5148596 := by
    simpa [prefixWord, tailWord_5148596, baseEnd_5148596] using wordTrace_append hprefix tailTrace_5148596
  have hstable : (prefixWord ++ tailWord_5148596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148596).length < 2 ^ (prefixWord ++ tailWord_5148596).sum := by decide
  have hdescent : baseEnd_5148596 < baseStart_5148596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148617 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_5148617 : Nat := 118140960795 + 5148617 * 2 ^ 59
def prefixEnd_5148617 : Nat := 4983230072969 + 3 ^ 40 * 5148617 * 2
def baseEnd_5148617 : Nat := 2643715226909787746009447

theorem tailTrace_5148617 : CollatzResearch.WordTrace tailWord_5148617 prefixEnd_5148617 2643715226909787746009447 := by
  unfold tailWord_5148617
  simp only [CollatzResearch.WordTrace]
  refine ⟨187785489188447397622964105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125190326125631598415309403 187785489188447397622964105)
  ·
    refine ⟨140839116891335548217223079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187785489188447397622964105 140839116891335548217223079)
    ·
      refine ⟨211258675337003322325834619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140839116891335548217223079 211258675337003322325834619)
      ·
        refine ⟨316888013005504983488751929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211258675337003322325834619 316888013005504983488751929)
        ·
          refine ⟨237666009754128737616563947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316888013005504983488751929 237666009754128737616563947)
          ·
            refine ⟨356499014631193106424845921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237666009754128737616563947 356499014631193106424845921)
            ·
              refine ⟨267374260973394829818634441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356499014631193106424845921 267374260973394829818634441)
              ·
                refine ⟨200530695730046122363975831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267374260973394829818634441 200530695730046122363975831)
                ·
                  refine ⟨300796043595069183545963747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200530695730046122363975831 300796043595069183545963747)
                  ·
                    refine ⟨451194065392603775318945621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 300796043595069183545963747 451194065392603775318945621)
                    ·
                      refine ⟨2643715226909787746009447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 451194065392603775318945621 2643715226909787746009447)
                      ·
                        rfl

theorem cell23_5148617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_5148617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148617 prefixEnd_5148617 := by exact prefixLift 5148617
  have htrace : WordTrace (prefixWord ++ tailWord_5148617) baseStart_5148617 baseEnd_5148617 := by
    simpa [prefixWord, tailWord_5148617, baseEnd_5148617] using wordTrace_append hprefix tailTrace_5148617
  have hstable : (prefixWord ++ tailWord_5148617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148617).length < 2 ^ (prefixWord ++ tailWord_5148617).sum := by decide
  have hdescent : baseEnd_5148617 < baseStart_5148617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148664 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_5148664 : Nat := 118140960795 + 5148664 * 2 ^ 59
def prefixEnd_5148664 : Nat := 4983230072969 + 3 ^ 40 * 5148664 * 2
def baseEnd_5148664 : Nat := 2643739360500549062121731

theorem tailTrace_5148664 : CollatzResearch.WordTrace tailWord_5148664 prefixEnd_5148664 2643739360500549062121731 := by
  unfold tailWord_5148664
  simp only [CollatzResearch.WordTrace]
  refine ⟨93893601709638562324962523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125191468946184749766616697 93893601709638562324962523)
  ·
    refine ⟨140840402564457843487443785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93893601709638562324962523 140840402564457843487443785)
    ·
      refine ⟨105630301923343382615582839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140840402564457843487443785 105630301923343382615582839)
      ·
        refine ⟨158445452885015073923374259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105630301923343382615582839 158445452885015073923374259)
        ·
          refine ⟨237668179327522610885061389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158445452885015073923374259 237668179327522610885061389)
          ·
            refine ⟨89125567247820979081898021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237668179327522610885061389 89125567247820979081898021)
            ·
              refine ⟨16711043858966433577855879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89125567247820979081898021 16711043858966433577855879)
              ·
                refine ⟨25066565788449650366783819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16711043858966433577855879 25066565788449650366783819)
                ·
                  refine ⟨37599848682674475550175729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25066565788449650366783819 37599848682674475550175729)
                  ·
                    refine ⟨28199886512005856662631797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37599848682674475550175729 28199886512005856662631797)
                    ·
                      refine ⟨2643739360500549062121731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28199886512005856662631797 2643739360500549062121731)
                      ·
                        rfl

theorem cell23_5148664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_5148664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148664 prefixEnd_5148664 := by exact prefixLift 5148664
  have htrace : WordTrace (prefixWord ++ tailWord_5148664) baseStart_5148664 baseEnd_5148664 := by
    simpa [prefixWord, tailWord_5148664, baseEnd_5148664] using wordTrace_append hprefix tailTrace_5148664
  have hstable : (prefixWord ++ tailWord_5148664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148664).length < 2 ^ (prefixWord ++ tailWord_5148664).sum := by decide
  have hdescent : baseEnd_5148664 < baseStart_5148664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148691 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 4]
def baseStart_5148691 : Nat := 118140960795 + 5148691 * 2 ^ 59
def prefixEnd_5148691 : Nat := 4983230072969 + 3 ^ 40 * 5148691 * 2
def baseEnd_5148691 : Nat := 2643753224478220456484107

theorem tailTrace_5148691 : CollatzResearch.WordTrace tailWord_5148691 prefixEnd_5148691 2643753224478220456484107 := by
  unfold tailWord_5148691
  simp only [CollatzResearch.WordTrace]
  refine ⟨187788188190179308261157927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125192125460119538840771951 187788188190179308261157927)
  ·
    refine ⟨281682282285268962391736891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187788188190179308261157927 281682282285268962391736891)
    ·
      refine ⟨422523423427903443587605337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281682282285268962391736891 422523423427903443587605337)
      ·
        refine ⟨316892567570927582690704003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422523423427903443587605337 316892567570927582690704003)
        ·
          refine ⟨475338851356391374036056005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316892567570927582690704003 475338851356391374036056005)
          ·
            refine ⟨89126034629323382631760501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 475338851356391374036056005 89126034629323382631760501)
            ·
              refine ⟨8355565746499067121727547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89126034629323382631760501 8355565746499067121727547)
              ·
                refine ⟨12533348619748600682591321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8355565746499067121727547 12533348619748600682591321)
                ·
                  refine ⟨9400011464811450511943491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12533348619748600682591321 9400011464811450511943491)
                  ·
                    refine ⟨14100017197217175767915237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9400011464811450511943491 14100017197217175767915237)
                    ·
                      refine ⟨2643753224478220456484107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14100017197217175767915237 2643753224478220456484107)
                      ·
                        rfl

theorem cell23_5148691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_5148691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148691 prefixEnd_5148691 := by exact prefixLift 5148691
  have htrace : WordTrace (prefixWord ++ tailWord_5148691) baseStart_5148691 baseEnd_5148691 := by
    simpa [prefixWord, tailWord_5148691, baseEnd_5148691] using wordTrace_append hprefix tailTrace_5148691
  have hstable : (prefixWord ++ tailWord_5148691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148691).length < 2 ^ (prefixWord ++ tailWord_5148691).sum := by decide
  have hdescent : baseEnd_5148691 < baseStart_5148691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148692 : List Nat := [2, 4, 3, 2, 1, 1, 2, 3, 5]
def baseStart_5148692 : Nat := 118140960795 + 5148692 * 2 ^ 59
def prefixEnd_5148692 : Nat := 4983230072969 + 3 ^ 40 * 5148692 * 2
def baseEnd_5148692 : Nat := 293750415328763883619067

theorem tailTrace_5148692 : CollatzResearch.WordTrace tailWord_5148692 prefixEnd_5148692 293750415328763883619067 := by
  unfold tailWord_5148692
  simp only [CollatzResearch.WordTrace]
  refine ⟨93894112331587842715972165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125192149775450456954629553 93894112331587842715972165)
  ·
    refine ⟨17605146062172720509244781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93894112331587842715972165 17605146062172720509244781)
    ·
      refine ⟨6601929773314770190966793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17605146062172720509244781 6601929773314770190966793)
      ·
        refine ⟨4951447329986077643225095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6601929773314770190966793 4951447329986077643225095)
        ·
          refine ⟨7427170994979116464837643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4951447329986077643225095 7427170994979116464837643)
          ·
            refine ⟨11140756492468674697256465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7427170994979116464837643 11140756492468674697256465)
            ·
              refine ⟨8355567369351506022942349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11140756492468674697256465 8355567369351506022942349)
              ·
                refine ⟨3133337763506814758603381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8355567369351506022942349 3133337763506814758603381)
                ·
                  refine ⟨293750415328763883619067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3133337763506814758603381 293750415328763883619067)
                  ·
                    rfl

theorem cell23_5148692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_5148692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148692 prefixEnd_5148692 := by exact prefixLift 5148692
  have htrace : WordTrace (prefixWord ++ tailWord_5148692) baseStart_5148692 baseEnd_5148692 := by
    simpa [prefixWord, tailWord_5148692, baseEnd_5148692] using wordTrace_append hprefix tailTrace_5148692
  have hstable : (prefixWord ++ tailWord_5148692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148692).length < 2 ^ (prefixWord ++ tailWord_5148692).sum := by decide
  have hdescent : baseEnd_5148692 < baseStart_5148692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148718 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_5148718 : Nat := 118140960795 + 5148718 * 2 ^ 59
def prefixEnd_5148718 : Nat := 4983230072969 + 3 ^ 40 * 5148718 * 2
def baseEnd_5148718 : Nat := 881255696151963950282161

theorem tailTrace_5148718 : CollatzResearch.WordTrace tailWord_5148718 prefixEnd_5148718 881255696151963950282161 := by
  unfold tailWord_5148718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23473646620135186484048851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125192781974054327914927205 23473646620135186484048851)
  ·
    refine ⟨35210469930202779726073277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23473646620135186484048851 35210469930202779726073277)
    ·
      refine ⟨13203926223826042397277479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35210469930202779726073277 13203926223826042397277479)
      ·
        refine ⟨19805889335739063595916219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13203926223826042397277479 19805889335739063595916219)
        ·
          refine ⟨29708834003608595393874329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19805889335739063595916219 29708834003608595393874329)
          ·
            refine ⟨22281625502706446545405747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29708834003608595393874329 22281625502706446545405747)
            ·
              refine ⟨33422438254059669818108621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22281625502706446545405747 33422438254059669818108621)
              ·
                refine ⟨12533414345272376181790733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33422438254059669818108621 12533414345272376181790733)
                ·
                  refine ⟨4700030379477141068171525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12533414345272376181790733 4700030379477141068171525)
                  ·
                    refine ⟨881255696151963950282161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4700030379477141068171525 881255696151963950282161)
                    ·
                      rfl

theorem cell23_5148718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_5148718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148718 prefixEnd_5148718 := by exact prefixLift 5148718
  have htrace : WordTrace (prefixWord ++ tailWord_5148718) baseStart_5148718 baseEnd_5148718 := by
    simpa [prefixWord, tailWord_5148718, baseEnd_5148718] using wordTrace_append hprefix tailTrace_5148718
  have hstable : (prefixWord ++ tailWord_5148718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148718).length < 2 ^ (prefixWord ++ tailWord_5148718).sum := by decide
  have hdescent : baseEnd_5148718 < baseStart_5148718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148761 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 1, 5]
def baseStart_5148761 : Nat := 118140960795 + 5148761 * 2 ^ 59
def prefixEnd_5148761 : Nat := 4983230072969 + 3 ^ 40 * 5148761 * 2
def baseEnd_5148761 : Nat := 881263056041345060869595

theorem tailTrace_5148761 : CollatzResearch.WordTrace tailWord_5148761 prefixEnd_5148761 881263056041345060869595 := by
  unfold tailWord_5148761
  simp only [CollatzResearch.WordTrace]
  refine ⟨187790741299925710216206137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125193827533283806810804091 187790741299925710216206137)
  ·
    refine ⟨140843055974944282662154603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187790741299925710216206137 140843055974944282662154603)
    ·
      refine ⟨211264583962416423993231905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140843055974944282662154603 211264583962416423993231905)
      ·
        refine ⟨158448437971812317994923929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211264583962416423993231905 158448437971812317994923929)
        ·
          refine ⟨118836328478859238496192947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158448437971812317994923929 118836328478859238496192947)
          ·
            refine ⟨178254492718288857744289421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118836328478859238496192947 178254492718288857744289421)
            ·
              refine ⟨66845434769358321654108533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178254492718288857744289421 66845434769358321654108533)
              ·
                refine ⟨6266759509627342655072675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66845434769358321654108533 6266759509627342655072675)
                ·
                  refine ⟨9400139264441013982609013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6266759509627342655072675 9400139264441013982609013)
                  ·
                    refine ⟨881263056041345060869595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9400139264441013982609013 881263056041345060869595)
                    ·
                      rfl

theorem cell23_5148761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_5148761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148761 prefixEnd_5148761 := by exact prefixLift 5148761
  have htrace : WordTrace (prefixWord ++ tailWord_5148761) baseStart_5148761 baseEnd_5148761 := by
    simpa [prefixWord, tailWord_5148761, baseEnd_5148761] using wordTrace_append hprefix tailTrace_5148761
  have hstable : (prefixWord ++ tailWord_5148761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148761).length < 2 ^ (prefixWord ++ tailWord_5148761).sum := by decide
  have hdescent : baseEnd_5148761 < baseStart_5148761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148768 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 4, 3, 2]
def baseStart_5148768 : Nat := 118140960795 + 5148768 * 2 ^ 59
def prefixEnd_5148768 : Nat := 4983230072969 + 3 ^ 40 * 5148768 * 2
def baseEnd_5148768 : Nat := 2643792762488616655221253

theorem tailTrace_5148768 : CollatzResearch.WordTrace tailWord_5148768 prefixEnd_5148768 2643792762488616655221253 := by
  unfold tailWord_5148768
  simp only [CollatzResearch.WordTrace]
  refine ⟨93895498305450175205855479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125193997740600233607807305 93895498305450175205855479)
  ·
    refine ⟨140843247458175262808783219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93895498305450175205855479 140843247458175262808783219)
    ·
      refine ⟨211264871187262894213174829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140843247458175262808783219 211264871187262894213174829)
      ·
        refine ⟨79224326695223585329940561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211264871187262894213174829 79224326695223585329940561)
        ·
          refine ⟨59418245021417688997455421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79224326695223585329940561 59418245021417688997455421)
          ·
            refine ⟨22281841883031633374045783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59418245021417688997455421 22281841883031633374045783)
            ·
              refine ⟨33422762824547450061068675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22281841883031633374045783 33422762824547450061068675)
              ·
                refine ⟨50134144236821175091603013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33422762824547450061068675 50134144236821175091603013)
                ·
                  refine ⟨9400152044403970329675565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50134144236821175091603013 9400152044403970329675565)
                  ·
                    refine ⟨3525057016651488873628337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9400152044403970329675565 3525057016651488873628337)
                    ·
                      refine ⟨2643792762488616655221253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525057016651488873628337 2643792762488616655221253)
                      ·
                        rfl

theorem cell23_5148768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_5148768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148768 prefixEnd_5148768 := by exact prefixLift 5148768
  have htrace : WordTrace (prefixWord ++ tailWord_5148768) baseStart_5148768 baseEnd_5148768 := by
    simpa [prefixWord, tailWord_5148768, baseEnd_5148768] using wordTrace_append hprefix tailTrace_5148768
  have hstable : (prefixWord ++ tailWord_5148768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148768).length < 2 ^ (prefixWord ++ tailWord_5148768).sum := by decide
  have hdescent : baseEnd_5148768 < baseStart_5148768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148808 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 1, 6]
def baseStart_5148808 : Nat := 118140960795 + 5148808 * 2 ^ 59
def prefixEnd_5148808 : Nat := 4983230072969 + 3 ^ 40 * 5148808 * 2
def baseEnd_5148808 : Nat := 881271100571598832907023

theorem tailTrace_5148808 : CollatzResearch.WordTrace tailWord_5148808 prefixEnd_5148808 881271100571598832907023 := by
  unfold tailWord_5148808
  simp only [CollatzResearch.WordTrace]
  refine ⟨93896227765377718621583539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125194970353836958162111385 93896227765377718621583539)
  ·
    refine ⟨140844341648066577932375309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93896227765377718621583539 140844341648066577932375309)
    ·
      refine ⟨52816628118024966724640741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140844341648066577932375309 52816628118024966724640741)
      ·
        refine ⟨9903117772129681260870139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52816628118024966724640741 9903117772129681260870139)
        ·
          refine ⟨14854676658194521891305209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9903117772129681260870139 14854676658194521891305209)
          ·
            refine ⟨11141007493645891418478907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14854676658194521891305209 11141007493645891418478907)
            ·
              refine ⟨16711511240468837127718361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11141007493645891418478907 16711511240468837127718361)
              ·
                refine ⟨12533633430351627845788771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16711511240468837127718361 12533633430351627845788771)
                ·
                  refine ⟨18800450145527441768683157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12533633430351627845788771 18800450145527441768683157)
                  ·
                    refine ⟨881271100571598832907023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18800450145527441768683157 881271100571598832907023)
                    ·
                      rfl

theorem cell23_5148808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_5148808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148808 prefixEnd_5148808 := by exact prefixLift 5148808
  have htrace : WordTrace (prefixWord ++ tailWord_5148808) baseStart_5148808 baseEnd_5148808 := by
    simpa [prefixWord, tailWord_5148808, baseEnd_5148808] using wordTrace_append hprefix tailTrace_5148808
  have hstable : (prefixWord ++ tailWord_5148808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148808).length < 2 ^ (prefixWord ++ tailWord_5148808).sum := by decide
  have hdescent : baseEnd_5148808 < baseStart_5148808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148826 : List Nat := [3, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3]
def baseStart_5148826 : Nat := 118140960795 + 5148826 * 2 ^ 59
def prefixEnd_5148826 : Nat := 4983230072969 + 3 ^ 40 * 5148826 * 2
def baseEnd_5148826 : Nat := 2643822544366577428295987

theorem tailTrace_5148826 : CollatzResearch.WordTrace tailWord_5148826 prefixEnd_5148826 2643822544366577428295987 := by
  unfold tailWord_5148826
  simp only [CollatzResearch.WordTrace]
  refine ⟨46948278011172556579330583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125195408029793484211548221 46948278011172556579330583)
  ·
    refine ⟨70422417016758834868995875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46948278011172556579330583 70422417016758834868995875)
    ·
      refine ⟨105633625525138252303493813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70422417016758834868995875 105633625525138252303493813)
      ·
        refine ⟨9903152392981711153452545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105633625525138252303493813 9903152392981711153452545)
        ·
          refine ⟨7427364294736283365089409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9903152392981711153452545 7427364294736283365089409)
          ·
            refine ⟨5570523221052212523817057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7427364294736283365089409 5570523221052212523817057)
            ·
              refine ⟨4177892415789159392862793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570523221052212523817057 4177892415789159392862793)
              ·
                refine ⟨3133419311841869544647095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4177892415789159392862793 3133419311841869544647095)
                ·
                  refine ⟨4700128967762804316970643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133419311841869544647095 4700128967762804316970643)
                  ·
                    refine ⟨7050193451644206475455965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4700128967762804316970643 7050193451644206475455965)
                    ·
                      refine ⟨2643822544366577428295987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7050193451644206475455965 2643822544366577428295987)
                      ·
                        rfl

theorem cell23_5148826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_5148826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148826 prefixEnd_5148826 := by exact prefixLift 5148826
  have htrace : WordTrace (prefixWord ++ tailWord_5148826) baseStart_5148826 baseEnd_5148826 := by
    simpa [prefixWord, tailWord_5148826, baseEnd_5148826] using wordTrace_append hprefix tailTrace_5148826
  have hstable : (prefixWord ++ tailWord_5148826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148826).length < 2 ^ (prefixWord ++ tailWord_5148826).sum := by decide
  have hdescent : baseEnd_5148826 < baseStart_5148826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148845 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_5148845 : Nat := 118140960795 + 5148845 * 2 ^ 59
def prefixEnd_5148845 : Nat := 4983230072969 + 3 ^ 40 * 5148845 * 2
def baseEnd_5148845 : Nat := 2643832300499012853958399

theorem tailTrace_5148845 : CollatzResearch.WordTrace tailWord_5148845 prefixEnd_5148845 2643832300499012853958399 := by
  unfold tailWord_5148845
  simp only [CollatzResearch.WordTrace]
  refine ⟨187793805031621392562263989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125195870021080928374842659 187793805031621392562263989)
  ·
    refine ⟨17605669221714505552712249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187793805031621392562263989 17605669221714505552712249)
    ·
      refine ⟨13204251916285879164534187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17605669221714505552712249 13204251916285879164534187)
      ·
        refine ⟨19806377874428818746801281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13204251916285879164534187 19806377874428818746801281)
        ·
          refine ⟨14854783405821614060100961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19806377874428818746801281 14854783405821614060100961)
          ·
            refine ⟨11141087554366210545075721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14854783405821614060100961 11141087554366210545075721)
            ·
              refine ⟨8355815665774657908806791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11141087554366210545075721 8355815665774657908806791)
              ·
                refine ⟨12533723498661986863210187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8355815665774657908806791 12533723498661986863210187)
                ·
                  refine ⟨18800585247992980294815281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12533723498661986863210187 18800585247992980294815281)
                  ·
                    refine ⟨14100438935994735221111461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18800585247992980294815281 14100438935994735221111461)
                    ·
                      refine ⟨2643832300499012853958399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14100438935994735221111461 2643832300499012853958399)
                      ·
                        rfl

theorem cell23_5148845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_5148845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148845 prefixEnd_5148845 := by exact prefixLift 5148845
  have htrace : WordTrace (prefixWord ++ tailWord_5148845) baseStart_5148845 baseEnd_5148845 := by
    simpa [prefixWord, tailWord_5148845, baseEnd_5148845] using wordTrace_append hprefix tailTrace_5148845
  have hstable : (prefixWord ++ tailWord_5148845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148845).length < 2 ^ (prefixWord ++ tailWord_5148845).sum := by decide
  have hdescent : baseEnd_5148845 < baseStart_5148845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148861 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_5148861 : Nat := 118140960795 + 5148861 * 2 ^ 59
def prefixEnd_5148861 : Nat := 4983230072969 + 3 ^ 40 * 5148861 * 2
def baseEnd_5148861 : Nat := 2643840516189484791358325

theorem tailTrace_5148861 : CollatzResearch.WordTrace tailWord_5148861 prefixEnd_5148861 2643840516189484791358325 := by
  unfold tailWord_5148861
  simp only [CollatzResearch.WordTrace]
  refine ⟨187794388599563427294846437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125196259066375618196564291 187794388599563427294846437)
  ·
    refine ⟨35211447862418142617783707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187794388599563427294846437 35211447862418142617783707)
    ·
      refine ⟨52817171793627213926675561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35211447862418142617783707 52817171793627213926675561)
      ·
        refine ⟨39612878845220410445006671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52817171793627213926675561 39612878845220410445006671)
        ·
          refine ⟨59419318267830615667510007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39612878845220410445006671 59419318267830615667510007)
          ·
            refine ⟨89128977401745923501265011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59419318267830615667510007 89128977401745923501265011)
            ·
              refine ⟨133693466102618885251897517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89128977401745923501265011 133693466102618885251897517)
              ·
                refine ⟨50135049788482081969461569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133693466102618885251897517 50135049788482081969461569)
                ·
                  refine ⟨37601287341361561477096177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50135049788482081969461569 37601287341361561477096177)
                  ·
                    refine ⟨28200965506021171107822133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37601287341361561477096177 28200965506021171107822133)
                    ·
                      refine ⟨2643840516189484791358325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28200965506021171107822133 2643840516189484791358325)
                      ·
                        rfl

theorem cell23_5148861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_5148861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148861 prefixEnd_5148861 := by exact prefixLift 5148861
  have htrace : WordTrace (prefixWord ++ tailWord_5148861) baseStart_5148861 baseEnd_5148861 := by
    simpa [prefixWord, tailWord_5148861, baseEnd_5148861] using wordTrace_append hprefix tailTrace_5148861
  have hstable : (prefixWord ++ tailWord_5148861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148861).length < 2 ^ (prefixWord ++ tailWord_5148861).sum := by decide
  have hdescent : baseEnd_5148861 < baseStart_5148861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148866 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_5148866 : Nat := 118140960795 + 5148866 * 2 ^ 59
def prefixEnd_5148866 : Nat := 4983230072969 + 3 ^ 40 * 5148866 * 2
def baseEnd_5148866 : Nat := 2643843083592757271795803

theorem tailTrace_5148866 : CollatzResearch.WordTrace tailWord_5148866 prefixEnd_5148866 2643843083592757271795803 := by
  unfold tailWord_5148866
  simp only [CollatzResearch.WordTrace]
  refine ⟨46948642741136328287194613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125196380643030208765852301 46948642741136328287194613)
  ·
    refine ⟨4401435256981530776924495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46948642741136328287194613 4401435256981530776924495)
    ·
      refine ⟨6602152885472296165386743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4401435256981530776924495 6602152885472296165386743)
      ·
        refine ⟨9903229328208444248080115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602152885472296165386743 9903229328208444248080115)
        ·
          refine ⟨14854843992312666372120173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9903229328208444248080115 14854843992312666372120173)
          ·
            refine ⟨5570566497117249889545065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14854843992312666372120173 5570566497117249889545065)
            ·
              refine ⟨4177924872837937417158799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570566497117249889545065 4177924872837937417158799)
              ·
                refine ⟨6266887309256906125738199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177924872837937417158799 6266887309256906125738199)
                ·
                  refine ⟨9400330963885359188607299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6266887309256906125738199 9400330963885359188607299)
                  ·
                    refine ⟨14100496445828038782910949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9400330963885359188607299 14100496445828038782910949)
                    ·
                      refine ⟨2643843083592757271795803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14100496445828038782910949 2643843083592757271795803)
                      ·
                        rfl

theorem cell23_5148866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_5148866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148866 prefixEnd_5148866 := by exact prefixLift 5148866
  have htrace : WordTrace (prefixWord ++ tailWord_5148866) baseStart_5148866 baseEnd_5148866 := by
    simpa [prefixWord, tailWord_5148866, baseEnd_5148866] using wordTrace_append hprefix tailTrace_5148866
  have hstable : (prefixWord ++ tailWord_5148866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148866).length < 2 ^ (prefixWord ++ tailWord_5148866).sum := by decide
  have hdescent : baseEnd_5148866 < baseStart_5148866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148875 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 1, 3, 2]
def baseStart_5148875 : Nat := 118140960795 + 5148875 * 2 ^ 59
def prefixEnd_5148875 : Nat := 4983230072969 + 3 ^ 40 * 5148875 * 2
def baseEnd_5148875 : Nat := 2643847704918647736583261

theorem tailTrace_5148875 : CollatzResearch.WordTrace tailWord_5148875 prefixEnd_5148875 2643847704918647736583261 := by
  unfold tailWord_5148875
  simp only [CollatzResearch.WordTrace]
  refine ⟨187794899221512707685856079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125196599481008471790570719 187794899221512707685856079)
  ·
    refine ⟨281692348832269061528784119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187794899221512707685856079 281692348832269061528784119)
    ·
      refine ⟨422538523248403592293176179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281692348832269061528784119 422538523248403592293176179)
      ·
        refine ⟨633807784872605388439764269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422538523248403592293176179 633807784872605388439764269)
        ·
          refine ⟨237677919327227020664911601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 633807784872605388439764269 237677919327227020664911601)
          ·
            refine ⟨178258439495420265498683701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237677919327227020664911601 178258439495420265498683701)
            ·
              refine ⟨16711728702695649890501597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178258439495420265498683701 16711728702695649890501597)
              ·
                refine ⟨6266898263510868708938099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16711728702695649890501597 6266898263510868708938099)
                ·
                  refine ⟨9400347395266303063407149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6266898263510868708938099 9400347395266303063407149)
                  ·
                    refine ⟨3525130273224863648777681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9400347395266303063407149 3525130273224863648777681)
                    ·
                      refine ⟨2643847704918647736583261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3525130273224863648777681 2643847704918647736583261)
                      ·
                        rfl

theorem cell23_5148875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 3, 2].length) (baseStart_5148875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148875 prefixEnd_5148875 := by exact prefixLift 5148875
  have htrace : WordTrace (prefixWord ++ tailWord_5148875) baseStart_5148875 baseEnd_5148875 := by
    simpa [prefixWord, tailWord_5148875, baseEnd_5148875] using wordTrace_append hprefix tailTrace_5148875
  have hstable : (prefixWord ++ tailWord_5148875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148875).length < 2 ^ (prefixWord ++ tailWord_5148875).sum := by decide
  have hdescent : baseEnd_5148875 < baseStart_5148875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5148881 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 2, 6]
def baseStart_5148881 : Nat := 118140960795 + 5148881 * 2 ^ 59
def prefixEnd_5148881 : Nat := 4983230072969 + 3 ^ 40 * 5148881 * 2
def baseEnd_5148881 : Nat := 881283595267524904369411

theorem tailTrace_5148881 : CollatzResearch.WordTrace tailWord_5148881 prefixEnd_5148881 881283595267524904369411 := by
  unfold tailWord_5148881
  simp only [CollatzResearch.WordTrace]
  refine ⟨187795118059490970710574497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125196745372993980473716331 187795118059490970710574497)
  ·
    refine ⟨140846338544618228032930873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187795118059490970710574497 140846338544618228032930873)
    ·
      refine ⟨105634753908463671024698155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140846338544618228032930873 105634753908463671024698155)
      ·
        refine ⟨158452130862695506537047233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105634753908463671024698155 158452130862695506537047233)
        ·
          refine ⟨118839098147021629902785425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158452130862695506537047233 118839098147021629902785425)
          ·
            refine ⟨89129323610266222427089069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118839098147021629902785425 89129323610266222427089069)
            ·
              refine ⟨33423496353849833410158401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89129323610266222427089069 33423496353849833410158401)
              ·
                refine ⟨25067622265387375057618801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33423496353849833410158401 25067622265387375057618801)
                ·
                  refine ⟨18800716699040531293214101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25067622265387375057618801 18800716699040531293214101)
                  ·
                    refine ⟨881283595267524904369411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18800716699040531293214101 881283595267524904369411)
                    ·
                      rfl

theorem cell23_5148881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_5148881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5148881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5148881 prefixEnd_5148881 := by exact prefixLift 5148881
  have htrace : WordTrace (prefixWord ++ tailWord_5148881) baseStart_5148881 baseEnd_5148881 := by
    simpa [prefixWord, tailWord_5148881, baseEnd_5148881] using wordTrace_append hprefix tailTrace_5148881
  have hstable : (prefixWord ++ tailWord_5148881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5148881).length < 2 ^ (prefixWord ++ tailWord_5148881).sum := by decide
  have hdescent : baseEnd_5148881 < baseStart_5148881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5148881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
