import V185TrunkScan23Chunk0306

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1815891 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 5]
def baseStart_1815891 : Nat := 118140960795 + 1815891 * 2 ^ 59
def prefixEnd_1815891 : Nat := 4983230072969 + 3 ^ 40 * 1815891 * 2
def baseEnd_1815891 : Nat := 932424899173660051811375

theorem tailTrace_1815891 : CollatzResearch.WordTrace tailWord_1815891 prefixEnd_1815891 932424899173660051811375 := by
  unfold tailWord_1815891
  simp only [CollatzResearch.WordTrace]
  refine ⟨66230985864344511337239527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44153990576229674224826351 66230985864344511337239527)
  ·
    refine ⟨99346478796516767005859291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66230985864344511337239527 99346478796516767005859291)
    ·
      refine ⟨149019718194775150508788937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99346478796516767005859291 149019718194775150508788937)
      ·
        refine ⟨111764788646081362881591703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149019718194775150508788937 111764788646081362881591703)
        ·
          refine ⟨167647182969122044322387555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111764788646081362881591703 167647182969122044322387555)
          ·
            refine ⟨251470774453683066483581333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167647182969122044322387555 251470774453683066483581333)
            ·
              refine ⟨11787692552516393741417875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 251470774453683066483581333 11787692552516393741417875)
              ·
                refine ⟨17681538828774590612126813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11787692552516393741417875 17681538828774590612126813)
                ·
                  refine ⟨6630577060790471479547555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17681538828774590612126813 6630577060790471479547555)
                  ·
                    refine ⟨9945865591185707219321333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6630577060790471479547555 9945865591185707219321333)
                    ·
                      refine ⟨932424899173660051811375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9945865591185707219321333 932424899173660051811375)
                      ·
                        rfl

theorem cell23_1815891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_1815891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815891 prefixEnd_1815891 := by exact prefixLift 1815891
  have htrace : WordTrace (prefixWord ++ tailWord_1815891) baseStart_1815891 baseEnd_1815891 := by
    simpa [prefixWord, tailWord_1815891, baseEnd_1815891] using wordTrace_append hprefix tailTrace_1815891
  have hstable : (prefixWord ++ tailWord_1815891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815891).length < 2 ^ (prefixWord ++ tailWord_1815891).sum := by decide
  have hdescent : baseEnd_1815891 < baseStart_1815891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815939 : List Nat := [1, 1, 1, 3, 5, 1, 2, 4, 1, 2, 2]
def baseStart_1815939 : Nat := 118140960795 + 1815939 * 2 ^ 59
def prefixEnd_1815939 : Nat := 4983230072969 + 3 ^ 40 * 1815939 * 2
def baseEnd_1815939 : Nat := 932449546245075864011155

theorem tailTrace_1815939 : CollatzResearch.WordTrace tailWord_1815939 prefixEnd_1815939 932449546245075864011155 := by
  unfold tailWord_1815939
  simp only [CollatzResearch.WordTrace]
  refine ⟨66232736568170615534986871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44155157712113743689991247 66232736568170615534986871)
  ·
    refine ⟨99349104852255923302480307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66232736568170615534986871 99349104852255923302480307)
    ·
      refine ⟨149023657278383884953720461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99349104852255923302480307 149023657278383884953720461)
      ·
        refine ⟨55883871479393956857645173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149023657278383884953720461 55883871479393956857645173)
        ·
          refine ⟨5239112951193183455404235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55883871479393956857645173 5239112951193183455404235)
          ·
            refine ⟨7858669426789775183106353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239112951193183455404235 7858669426789775183106353)
            ·
              refine ⟨5894002070092331387329765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7858669426789775183106353 5894002070092331387329765)
              ·
                refine ⟨1105125388142312135124331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5894002070092331387329765 1105125388142312135124331)
                ·
                  refine ⟨1657688082213468202686497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105125388142312135124331 1657688082213468202686497)
                  ·
                    refine ⟨1243266061660101152014873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1657688082213468202686497 1243266061660101152014873)
                    ·
                      refine ⟨932449546245075864011155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1243266061660101152014873 932449546245075864011155)
                      ·
                        rfl

theorem cell23_1815939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_1815939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815939 prefixEnd_1815939 := by exact prefixLift 1815939
  have htrace : WordTrace (prefixWord ++ tailWord_1815939) baseStart_1815939 baseEnd_1815939 := by
    simpa [prefixWord, tailWord_1815939, baseEnd_1815939] using wordTrace_append hprefix tailTrace_1815939
  have hstable : (prefixWord ++ tailWord_1815939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815939).length < 2 ^ (prefixWord ++ tailWord_1815939).sum := by decide
  have hdescent : baseEnd_1815939 < baseStart_1815939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815941 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_1815941 : Nat := 118140960795 + 1815941 * 2 ^ 59
def prefixEnd_1815941 : Nat := 4983230072969 + 3 ^ 40 * 1815941 * 2
def baseEnd_1815941 : Nat := 310816857735461618728715

theorem tailTrace_1815941 : CollatzResearch.WordTrace tailWord_1815941 prefixEnd_1815941 310816857735461618728715 := by
  unfold tailWord_1815941
  simp only [CollatzResearch.WordTrace]
  refine ⟨66232809514163369876559677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44155206342775579917706451 66232809514163369876559677)
  ·
    refine ⟨24837303567811263703709879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66232809514163369876559677 24837303567811263703709879)
    ·
      refine ⟨37255955351716895555564819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24837303567811263703709879 37255955351716895555564819)
      ·
        refine ⟨55883933027575343333347229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37255955351716895555564819 55883933027575343333347229)
        ·
          refine ⟨20956474885340753750005211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55883933027575343333347229 20956474885340753750005211)
          ·
            refine ⟨31434712328011130625007817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20956474885340753750005211 31434712328011130625007817)
            ·
              refine ⟨23576034246008347968755863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31434712328011130625007817 23576034246008347968755863)
              ·
                refine ⟨35364051369012521953133795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23576034246008347968755863 35364051369012521953133795)
                ·
                  refine ⟨53046077053518782929700693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35364051369012521953133795 53046077053518782929700693)
                  ·
                    refine ⟨310816857735461618728715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 53046077053518782929700693 310816857735461618728715)
                    ·
                      rfl

theorem cell23_1815941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_1815941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815941 prefixEnd_1815941 := by exact prefixLift 1815941
  have htrace : WordTrace (prefixWord ++ tailWord_1815941) baseStart_1815941 baseEnd_1815941 := by
    simpa [prefixWord, tailWord_1815941, baseEnd_1815941] using wordTrace_append hprefix tailTrace_1815941
  have hstable : (prefixWord ++ tailWord_1815941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815941).length < 2 ^ (prefixWord ++ tailWord_1815941).sum := by decide
  have hdescent : baseEnd_1815941 < baseStart_1815941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815998 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1815998 : Nat := 118140960795 + 1815998 * 2 ^ 59
def prefixEnd_1815998 : Nat := 4983230072969 + 3 ^ 40 * 1815998 * 2
def baseEnd_1815998 : Nat := 932479841603691133173383

theorem tailTrace_1815998 : CollatzResearch.WordTrace tailWord_1815998 prefixEnd_1815998 932479841603691133173383 := by
  unfold tailWord_1815998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8279361059369608576423081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44156592316637912407589765 8279361059369608576423081)
  ·
    refine ⟨6209520794527206432317311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8279361059369608576423081 6209520794527206432317311)
    ·
      refine ⟨9314281191790809648475967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209520794527206432317311 9314281191790809648475967)
      ·
        refine ⟨13971421787686214472713951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314281191790809648475967 13971421787686214472713951)
        ·
          refine ⟨20957132681529321709070927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13971421787686214472713951 20957132681529321709070927)
          ·
            refine ⟨31435699022293982563606391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20957132681529321709070927 31435699022293982563606391)
            ·
              refine ⟨47153548533440973845409587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31435699022293982563606391 47153548533440973845409587)
              ·
                refine ⟨70730322800161460768114381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47153548533440973845409587 70730322800161460768114381)
                ·
                  refine ⟨26523871050060547788042893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70730322800161460768114381 26523871050060547788042893)
                  ·
                    refine ⟨9946451643772705420516085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26523871050060547788042893 9946451643772705420516085)
                    ·
                      refine ⟨932479841603691133173383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9946451643772705420516085 932479841603691133173383)
                      ·
                        rfl

theorem cell23_1815998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1815998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815998 prefixEnd_1815998 := by exact prefixLift 1815998
  have htrace : WordTrace (prefixWord ++ tailWord_1815998) baseStart_1815998 baseEnd_1815998 := by
    simpa [prefixWord, tailWord_1815998, baseEnd_1815998] using wordTrace_append hprefix tailTrace_1815998
  have hstable : (prefixWord ++ tailWord_1815998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815998).length < 2 ^ (prefixWord ++ tailWord_1815998).sum := by decide
  have hdescent : baseEnd_1815998 < baseStart_1815998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816008 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1816008 : Nat := 118140960795 + 1816008 * 2 ^ 59
def prefixEnd_1816008 : Nat := 4983230072969 + 3 ^ 40 * 1816008 * 2
def baseEnd_1816008 : Nat := 932484976410236094048337

theorem tailTrace_1816008 : CollatzResearch.WordTrace tailWord_1816008 prefixEnd_1816008 932484976410236094048337 := by
  unfold tailWord_1816008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33117626602460320159624339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44156835469947093546165785 33117626602460320159624339)
  ·
    refine ⟨49676439903690480239436509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33117626602460320159624339 49676439903690480239436509)
    ·
      refine ⟨18628664963883930089788691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49676439903690480239436509 18628664963883930089788691)
      ·
        refine ⟨27942997445825895134683037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18628664963883930089788691 27942997445825895134683037)
        ·
          refine ⟨10478624042184710675506139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27942997445825895134683037 10478624042184710675506139)
          ·
            refine ⟨15717936063277066013259209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10478624042184710675506139 15717936063277066013259209)
            ·
              refine ⟨11788452047457799509944407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15717936063277066013259209 11788452047457799509944407)
              ·
                refine ⟨17682678071186699264916611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11788452047457799509944407 17682678071186699264916611)
                ·
                  refine ⟨26524017106780048897374917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17682678071186699264916611 26524017106780048897374917)
                  ·
                    refine ⟨4973253207521259168257797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26524017106780048897374917 4973253207521259168257797)
                    ·
                      refine ⟨932484976410236094048337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4973253207521259168257797 932484976410236094048337)
                      ·
                        rfl

theorem cell23_1816008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1816008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816008 prefixEnd_1816008 := by exact prefixLift 1816008
  have htrace : WordTrace (prefixWord ++ tailWord_1816008) baseStart_1816008 baseEnd_1816008 := by
    simpa [prefixWord, tailWord_1816008, baseEnd_1816008] using wordTrace_append hprefix tailTrace_1816008
  have hstable : (prefixWord ++ tailWord_1816008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816008).length < 2 ^ (prefixWord ++ tailWord_1816008).sum := by decide
  have hdescent : baseEnd_1816008 < baseStart_1816008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816058 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_1816058 : Nat := 118140960795 + 1816058 * 2 ^ 59
def prefixEnd_1816058 : Nat := 4983230072969 + 3 ^ 40 * 1816058 * 2
def baseEnd_1816058 : Nat := 932510650442960898423107

theorem tailTrace_1816058 : CollatzResearch.WordTrace tailWord_1816058 prefixEnd_1816058 932510650442960898423107 := by
  unfold tailWord_1816058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16559269213684874714642207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44158051236492999239045885 16559269213684874714642207)
  ·
    refine ⟨24838903820527312071963311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16559269213684874714642207 24838903820527312071963311)
    ·
      refine ⟨37258355730790968107944967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24838903820527312071963311 37258355730790968107944967)
      ·
        refine ⟨55887533596186452161917451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37258355730790968107944967 55887533596186452161917451)
        ·
          refine ⟨83831300394279678242876177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55887533596186452161917451 83831300394279678242876177)
          ·
            refine ⟨62873475295709758682157133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83831300394279678242876177 62873475295709758682157133)
            ·
              refine ⟨23577553235891159505808925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62873475295709758682157133 23577553235891159505808925)
              ·
                refine ⟨8841582463459184814678347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23577553235891159505808925 8841582463459184814678347)
                ·
                  refine ⟨13262373695188777222017521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8841582463459184814678347 13262373695188777222017521)
                  ·
                    refine ⟨9946780271391582916513141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13262373695188777222017521 9946780271391582916513141)
                    ·
                      refine ⟨932510650442960898423107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9946780271391582916513141 932510650442960898423107)
                      ·
                        rfl

theorem cell23_1816058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_1816058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816058 prefixEnd_1816058 := by exact prefixLift 1816058
  have htrace : WordTrace (prefixWord ++ tailWord_1816058) baseStart_1816058 baseEnd_1816058 := by
    simpa [prefixWord, tailWord_1816058, baseEnd_1816058] using wordTrace_append hprefix tailTrace_1816058
  have hstable : (prefixWord ++ tailWord_1816058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816058).length < 2 ^ (prefixWord ++ tailWord_1816058).sum := by decide
  have hdescent : baseEnd_1816058 < baseStart_1816058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816085 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_1816085 : Nat := 118140960795 + 1816085 * 2 ^ 59
def prefixEnd_1816085 : Nat := 4983230072969 + 3 ^ 40 * 1816085 * 2
def baseEnd_1816085 : Nat := 932524514420632292785483

theorem tailTrace_1816085 : CollatzResearch.WordTrace tailWord_1816085 prefixEnd_1816085 932524514420632292785483 := by
  unfold tailWord_1816085
  simp only [CollatzResearch.WordTrace]
  refine ⟨66238061625641682469801709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44158707750427788313201139 66238061625641682469801709)
  ·
    refine ⟨24839273109615630926175641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66238061625641682469801709 24839273109615630926175641)
    ·
      refine ⟨18629454832211723194631731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24839273109615630926175641 18629454832211723194631731)
      ·
        refine ⟨27944182248317584791947597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18629454832211723194631731 27944182248317584791947597)
        ·
          refine ⟨10479068343119094296980349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27944182248317584791947597 10479068343119094296980349)
          ·
            refine ⟨3929650628669660361367631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10479068343119094296980349 3929650628669660361367631)
            ·
              refine ⟨5894475943004490542051447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929650628669660361367631 5894475943004490542051447)
              ·
                refine ⟨8841713914506735813077171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5894475943004490542051447 8841713914506735813077171)
                ·
                  refine ⟨13262570871760103719615757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8841713914506735813077171 13262570871760103719615757)
                  ·
                    refine ⟨4973464076910038894855909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13262570871760103719615757 4973464076910038894855909)
                    ·
                      refine ⟨932524514420632292785483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4973464076910038894855909 932524514420632292785483)
                      ·
                        rfl

theorem cell23_1816085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_1816085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816085 prefixEnd_1816085 := by exact prefixLift 1816085
  have htrace : WordTrace (prefixWord ++ tailWord_1816085) baseStart_1816085 baseEnd_1816085 := by
    simpa [prefixWord, tailWord_1816085, baseEnd_1816085] using wordTrace_append hprefix tailTrace_1816085
  have hstable : (prefixWord ++ tailWord_1816085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816085).length < 2 ^ (prefixWord ++ tailWord_1816085).sum := by decide
  have hdescent : baseEnd_1816085 < baseStart_1816085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816128 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1816128 : Nat := 118140960795 + 1816128 * 2 ^ 59
def prefixEnd_1816128 : Nat := 4983230072969 + 3 ^ 40 * 1816128 * 2
def baseEnd_1816128 : Nat := 932546594088775624547785

theorem tailTrace_1816128 : CollatzResearch.WordTrace tailWord_1816128 prefixEnd_1816128 932546594088775624547785 := by
  unfold tailWord_1816128
  simp only [CollatzResearch.WordTrace]
  refine ⟨33119814982242950406808519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44159753309657267209078025 33119814982242950406808519)
  ·
    refine ⟨49679722473364425610212779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33119814982242950406808519 49679722473364425610212779)
    ·
      refine ⟨74519583710046638415319169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49679722473364425610212779 74519583710046638415319169)
      ·
        refine ⟨55889687782534978811489377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74519583710046638415319169 55889687782534978811489377)
        ·
          refine ⟨41917265836901234108617033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55889687782534978811489377 41917265836901234108617033)
          ·
            refine ⟨31437949377675925581462775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41917265836901234108617033 31437949377675925581462775)
            ·
              refine ⟨47156924066513888372194163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31437949377675925581462775 47156924066513888372194163)
              ·
                refine ⟨70735386099770832558291245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47156924066513888372194163 70735386099770832558291245)
                ·
                  refine ⟨26525769787414062209359217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70735386099770832558291245 26525769787414062209359217)
                  ·
                    refine ⟨19894327340560546657019413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26525769787414062209359217 19894327340560546657019413)
                    ·
                      refine ⟨932546594088775624547785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19894327340560546657019413 932546594088775624547785)
                      ·
                        rfl

theorem cell23_1816128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1816128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816128 prefixEnd_1816128 := by exact prefixLift 1816128
  have htrace : WordTrace (prefixWord ++ tailWord_1816128) baseStart_1816128 baseEnd_1816128 := by
    simpa [prefixWord, tailWord_1816128, baseEnd_1816128] using wordTrace_append hprefix tailTrace_1816128
  have hstable : (prefixWord ++ tailWord_1816128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816128).length < 2 ^ (prefixWord ++ tailWord_1816128).sum := by decide
  have hdescent : baseEnd_1816128 < baseStart_1816128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816146 : List Nat := [3, 2, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_1816146 : Nat := 118140960795 + 1816146 * 2 ^ 59
def prefixEnd_1816146 : Nat := 4983230072969 + 3 ^ 40 * 1816146 * 2
def baseEnd_1816146 : Nat := 310851945580185518040901

theorem tailTrace_1816146 : CollatzResearch.WordTrace tailWord_1816146 prefixEnd_1816146 310851945580185518040901 := by
  unfold tailWord_1816146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16560071619605172471943073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44160190985613793258514861 16560071619605172471943073)
  ·
    refine ⟨12420053714703879353957305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16560071619605172471943073 12420053714703879353957305)
    ·
      refine ⟨9315040286027909515467979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12420053714703879353957305 9315040286027909515467979)
      ·
        refine ⟨13972560429041864273201969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9315040286027909515467979 13972560429041864273201969)
        ·
          refine ⟨10479420321781398204901477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13972560429041864273201969 10479420321781398204901477)
          ·
            refine ⟨1964891310334012163419027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10479420321781398204901477 1964891310334012163419027)
            ·
              refine ⟨2947336965501018245128541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964891310334012163419027 2947336965501018245128541)
              ·
                refine ⟨1105251362062881841923203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2947336965501018245128541 1105251362062881841923203)
                ·
                  refine ⟨1657877043094322762884805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105251362062881841923203 1657877043094322762884805)
                  ·
                    refine ⟨310851945580185518040901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1657877043094322762884805 310851945580185518040901)
                    ·
                      rfl

theorem cell23_1816146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_1816146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816146 prefixEnd_1816146 := by exact prefixLift 1816146
  have htrace : WordTrace (prefixWord ++ tailWord_1816146) baseStart_1816146 baseEnd_1816146 := by
    simpa [prefixWord, tailWord_1816146, baseEnd_1816146] using wordTrace_append hprefix tailTrace_1816146
  have hstable : (prefixWord ++ tailWord_1816146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816146).length < 2 ^ (prefixWord ++ tailWord_1816146).sum := by decide
  have hdescent : baseEnd_1816146 < baseStart_1816146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816169 : List Nat := [1, 2, 1, 1, 1, 4, 2, 6, 1, 1, 3]
def baseStart_1816169 : Nat := 118140960795 + 1816169 * 2 ^ 59
def prefixEnd_1816169 : Nat := 4983230072969 + 3 ^ 40 * 1816169 * 2
def baseEnd_1816169 : Nat := 932567646795609964135097

theorem tailTrace_1816169 : CollatzResearch.WordTrace tailWord_1816169 prefixEnd_1816169 932567646795609964135097 := by
  unfold tailWord_1816169
  simp only [CollatzResearch.WordTrace]
  refine ⟨66241125357337364815859561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44160750238224909877239707 66241125357337364815859561)
  ·
    refine ⟨49680844018003023611894671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66241125357337364815859561 49680844018003023611894671)
    ·
      refine ⟨74521266027004535417842007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49680844018003023611894671 74521266027004535417842007)
      ·
        refine ⟨111781899040506803126763011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74521266027004535417842007 111781899040506803126763011)
        ·
          refine ⟨167672848560760204690144517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111781899040506803126763011 167672848560760204690144517)
          ·
            refine ⟨31438659105142538379402097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167672848560760204690144517 31438659105142538379402097)
            ·
              refine ⟨23578994328856903784551573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31438659105142538379402097 23578994328856903784551573)
              ·
                refine ⟨1105265359165167364900855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23578994328856903784551573 1105265359165167364900855)
                ·
                  refine ⟨1657898038747751047351283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105265359165167364900855 1657898038747751047351283)
                  ·
                    refine ⟨2486847058121626571026925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1657898038747751047351283 2486847058121626571026925)
                    ·
                      refine ⟨932567646795609964135097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2486847058121626571026925 932567646795609964135097)
                      ·
                        rfl

theorem cell23_1816169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 1, 3].length) (baseStart_1816169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816169 prefixEnd_1816169 := by exact prefixLift 1816169
  have htrace : WordTrace (prefixWord ++ tailWord_1816169) baseStart_1816169 baseEnd_1816169 := by
    simpa [prefixWord, tailWord_1816169, baseEnd_1816169] using wordTrace_append hprefix tailTrace_1816169
  have hstable : (prefixWord ++ tailWord_1816169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816169).length < 2 ^ (prefixWord ++ tailWord_1816169).sum := by decide
  have hdescent : baseEnd_1816169 < baseStart_1816169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816175 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_1816175 : Nat := 118140960795 + 1816175 * 2 ^ 59
def prefixEnd_1816175 : Nat := 4983230072969 + 3 ^ 40 * 1816175 * 2
def baseEnd_1816175 : Nat := 932570727679536940660069

theorem tailTrace_1816175 : CollatzResearch.WordTrace tailWord_1816175 prefixEnd_1816175 932570727679536940660069 := by
  unfold tailWord_1816175
  simp only [CollatzResearch.WordTrace]
  refine ⟨66241344195315627840577979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44160896130210418560385319 66241344195315627840577979)
  ·
    refine ⟨99362016292973441760866969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66241344195315627840577979 99362016292973441760866969)
    ·
      refine ⟨74521512219730081320650227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99362016292973441760866969 74521512219730081320650227)
      ·
        refine ⟨111782268329595121980975341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74521512219730081320650227 111782268329595121980975341)
        ·
          refine ⟨41918350623598170742865753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111782268329595121980975341 41918350623598170742865753)
          ·
            refine ⟨31438762967698628057149315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41918350623598170742865753 31438762967698628057149315)
            ·
              refine ⟨47158144451547942085723973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31438762967698628057149315 47158144451547942085723973)
              ·
                refine ⟨8842152084665239141073245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47158144451547942085723973 8842152084665239141073245)
                ·
                  refine ⟨3315807031749464677902467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8842152084665239141073245 3315807031749464677902467)
                  ·
                    refine ⟨4973710547624197016853701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3315807031749464677902467 4973710547624197016853701)
                    ·
                      refine ⟨932570727679536940660069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4973710547624197016853701 932570727679536940660069)
                      ·
                        rfl

theorem cell23_1816175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_1816175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816175 prefixEnd_1816175 := by exact prefixLift 1816175
  have htrace : WordTrace (prefixWord ++ tailWord_1816175) baseStart_1816175 baseEnd_1816175 := by
    simpa [prefixWord, tailWord_1816175, baseEnd_1816175] using wordTrace_append hprefix tailTrace_1816175
  have hstable : (prefixWord ++ tailWord_1816175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816175).length < 2 ^ (prefixWord ++ tailWord_1816175).sum := by decide
  have hdescent : baseEnd_1816175 < baseStart_1816175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816185 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 1, 6]
def baseStart_1816185 : Nat := 118140960795 + 1816185 * 2 ^ 59
def prefixEnd_1816185 : Nat := 4983230072969 + 3 ^ 40 * 1816185 * 2
def baseEnd_1816185 : Nat := 310858620828693967178341

theorem tailTrace_1816185 : CollatzResearch.WordTrace tailWord_1816185 prefixEnd_1816185 310858620828693967178341 := by
  unfold tailWord_1816185
  simp only [CollatzResearch.WordTrace]
  refine ⟨66241708925279399548442009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44161139283519599698961339 66241708925279399548442009)
  ·
    refine ⟨49681281693959549661331507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66241708925279399548442009 49681281693959549661331507)
    ·
      refine ⟨74521922540939324491997261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49681281693959549661331507 74521922540939324491997261)
      ·
        refine ⟨27945720952852246684498973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74521922540939324491997261 27945720952852246684498973)
        ·
          refine ⟨10479645357319592506687115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27945720952852246684498973 10479645357319592506687115)
          ·
            refine ⟨15719468035979388760030673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10479645357319592506687115 15719468035979388760030673)
            ·
              refine ⟨11789601026984541570023005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15719468035979388760030673 11789601026984541570023005)
              ·
                refine ⟨4421100385119203088758627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11789601026984541570023005 4421100385119203088758627)
                ·
                  refine ⟨6631650577678804633137941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421100385119203088758627 6631650577678804633137941)
                  ·
                    refine ⟨310858620828693967178341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6631650577678804633137941 310858620828693967178341)
                    ·
                      rfl

theorem cell23_1816185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_1816185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816185 prefixEnd_1816185 := by exact prefixLift 1816185
  have htrace : WordTrace (prefixWord ++ tailWord_1816185) baseStart_1816185 baseEnd_1816185 := by
    simpa [prefixWord, tailWord_1816185, baseEnd_1816185] using wordTrace_append hprefix tailTrace_1816185
  have hstable : (prefixWord ++ tailWord_1816185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816185).length < 2 ^ (prefixWord ++ tailWord_1816185).sum := by decide
  have hdescent : baseEnd_1816185 < baseStart_1816185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816189 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_1816189 : Nat := 118140960795 + 1816189 * 2 ^ 59
def prefixEnd_1816189 : Nat := 4983230072969 + 3 ^ 40 * 1816189 * 2
def baseEnd_1816189 : Nat := 310859305469566628628335

theorem tailTrace_1816189 : CollatzResearch.WordTrace tailWord_1816189 prefixEnd_1816189 310859305469566628628335 := by
  unfold tailWord_1816189
  simp only [CollatzResearch.WordTrace]
  refine ⟨66241854817264908231587621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44161236544843272154391747 66241854817264908231587621)
  ·
    refine ⟨12420347778237170293422679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66241854817264908231587621 12420347778237170293422679)
    ·
      refine ⟨18630521667355755440134019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12420347778237170293422679 18630521667355755440134019)
      ·
        refine ⟨27945782501033633160201029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18630521667355755440134019 27945782501033633160201029)
        ·
          refine ⟨5239834218943806217537693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27945782501033633160201029 5239834218943806217537693)
          ·
            refine ⟨1964937832103927331576635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5239834218943806217537693 1964937832103927331576635)
            ·
              refine ⟨2947406748155890997364953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964937832103927331576635 2947406748155890997364953)
              ·
                refine ⟨2210555061116918248023715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947406748155890997364953 2210555061116918248023715)
                ·
                  refine ⟨3315832591675377372035573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210555061116918248023715 3315832591675377372035573)
                  ·
                    refine ⟨310859305469566628628335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3315832591675377372035573 310859305469566628628335)
                    ·
                      rfl

theorem cell23_1816189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_1816189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816189 prefixEnd_1816189 := by exact prefixLift 1816189
  have htrace : WordTrace (prefixWord ++ tailWord_1816189) baseStart_1816189 baseEnd_1816189 := by
    simpa [prefixWord, tailWord_1816189, baseEnd_1816189] using wordTrace_append hprefix tailTrace_1816189
  have hstable : (prefixWord ++ tailWord_1816189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816189).length < 2 ^ (prefixWord ++ tailWord_1816189).sum := by decide
  have hdescent : baseEnd_1816189 < baseStart_1816189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816196 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_1816196 : Nat := 118140960795 + 1816196 * 2 ^ 59
def prefixEnd_1816196 : Nat := 4983230072969 + 3 ^ 40 * 1816196 * 2
def baseEnd_1816196 : Nat := 932581510773281358497473

theorem tailTrace_1816196 : CollatzResearch.WordTrace tailWord_1816196 prefixEnd_1816196 932581510773281358497473 := by
  unfold tailWord_1816196
  simp only [CollatzResearch.WordTrace]
  refine ⟨33121055064119774213546221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44161406752159698951394961 33121055064119774213546221)
  ·
    refine ⟨12420395649044915330079833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33121055064119774213546221 12420395649044915330079833)
    ·
      refine ⟨9315296736783686497559875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12420395649044915330079833 9315296736783686497559875)
      ·
        refine ⟨13972945105175529746339813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9315296736783686497559875 13972945105175529746339813)
        ·
          refine ⟨2619927207220411827438715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13972945105175529746339813 2619927207220411827438715)
          ·
            refine ⟨3929890810830617741158073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619927207220411827438715 3929890810830617741158073)
            ·
              refine ⟨2947418108122963305868555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3929890810830617741158073 2947418108122963305868555)
              ·
                refine ⟨4421127162184444958802833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947418108122963305868555 4421127162184444958802833)
                ·
                  refine ⟨3315845371638333719102125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4421127162184444958802833 3315845371638333719102125)
                  ·
                    refine ⟨1243442014364375144663297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315845371638333719102125 1243442014364375144663297)
                    ·
                      refine ⟨932581510773281358497473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1243442014364375144663297 932581510773281358497473)
                      ·
                        rfl

theorem cell23_1816196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_1816196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816196 prefixEnd_1816196 := by exact prefixLift 1816196
  have htrace : WordTrace (prefixWord ++ tailWord_1816196) baseStart_1816196 baseEnd_1816196 := by
    simpa [prefixWord, tailWord_1816196, baseEnd_1816196] using wordTrace_append hprefix tailTrace_1816196
  have hstable : (prefixWord ++ tailWord_1816196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816196).length < 2 ^ (prefixWord ++ tailWord_1816196).sum := by decide
  have hdescent : baseEnd_1816196 < baseStart_1816196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816202 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1816202 : Nat := 118140960795 + 1816202 * 2 ^ 59
def prefixEnd_1816202 : Nat := 4983230072969 + 3 ^ 40 * 1816202 * 2
def baseEnd_1816202 : Nat := 310861530552402778340815

theorem tailTrace_1816202 : CollatzResearch.WordTrace tailWord_1816202 prefixEnd_1816202 310861530552402778340815 := by
  unfold tailWord_1816202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16560582241554452862952715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44161552644145207634540573 16560582241554452862952715)
  ·
    refine ⟨24840873362331679294429073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16560582241554452862952715 24840873362331679294429073)
    ·
      refine ⟨18630655021748759470821805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24840873362331679294429073 18630655021748759470821805)
      ·
        refine ⟨6986495633155784801558177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18630655021748759470821805 6986495633155784801558177)
        ·
          refine ⟨5239871724866838601168633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6986495633155784801558177 5239871724866838601168633)
          ·
            refine ⟨3929903793650128950876475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5239871724866838601168633 3929903793650128950876475)
            ·
              refine ⟨5894855690475193426314713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929903793650128950876475 5894855690475193426314713)
              ·
                refine ⟨4421141767856395069736035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5894855690475193426314713 4421141767856395069736035)
                ·
                  refine ⟨6631712651784592604604053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421141767856395069736035 6631712651784592604604053)
                  ·
                    refine ⟨310861530552402778340815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6631712651784592604604053 310861530552402778340815)
                    ·
                      rfl

theorem cell23_1816202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1816202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816202 prefixEnd_1816202 := by exact prefixLift 1816202
  have htrace : WordTrace (prefixWord ++ tailWord_1816202) baseStart_1816202 baseEnd_1816202 := by
    simpa [prefixWord, tailWord_1816202, baseEnd_1816202] using wordTrace_append hprefix tailTrace_1816202
  have hstable : (prefixWord ++ tailWord_1816202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816202).length < 2 ^ (prefixWord ++ tailWord_1816202).sum := by decide
  have hdescent : baseEnd_1816202 < baseStart_1816202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816220 : List Nat := [2, 2, 3, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_1816220 : Nat := 118140960795 + 1816220 * 2 ^ 59
def prefixEnd_1816220 : Nat := 4983230072969 + 3 ^ 40 * 1816220 * 2
def baseEnd_1816220 : Nat := 932593834308989264597363

theorem tailTrace_1816220 : CollatzResearch.WordTrace tailWord_1816220 prefixEnd_1816220 932593834308989264597363 := by
  unfold tailWord_1816220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33121492740076300262983057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44161990320101733683977409 33121492740076300262983057)
  ·
    refine ⟨24841119555057225197237293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33121492740076300262983057 24841119555057225197237293)
    ·
      refine ⟨9315419833146459448963985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24841119555057225197237293 9315419833146459448963985)
      ·
        refine ⟨6986564874859844586722989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9315419833146459448963985 6986564874859844586722989)
        ·
          refine ⟨2619961828072441720021121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6986564874859844586722989 2619961828072441720021121)
          ·
            refine ⟨1964971371054331290015841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2619961828072441720021121 1964971371054331290015841)
            ·
              refine ⟨1473728528290748467511881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964971371054331290015841 1473728528290748467511881)
              ·
                refine ⟨1105296396218061350633911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473728528290748467511881 1105296396218061350633911)
                ·
                  refine ⟨1657944594327092025950867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105296396218061350633911 1657944594327092025950867)
                  ·
                    refine ⟨2486916891490638038926301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1657944594327092025950867 2486916891490638038926301)
                    ·
                      refine ⟨932593834308989264597363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2486916891490638038926301 932593834308989264597363)
                      ·
                        rfl

theorem cell23_1816220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_1816220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816220 prefixEnd_1816220 := by exact prefixLift 1816220
  have htrace : WordTrace (prefixWord ++ tailWord_1816220) baseStart_1816220 baseEnd_1816220 := by
    simpa [prefixWord, tailWord_1816220, baseEnd_1816220] using wordTrace_append hprefix tailTrace_1816220
  have hstable : (prefixWord ++ tailWord_1816220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816220).length < 2 ^ (prefixWord ++ tailWord_1816220).sum := by decide
  have hdescent : baseEnd_1816220 < baseStart_1816220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816242 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1816242 : Nat := 118140960795 + 1816242 * 2 ^ 59
def prefixEnd_1816242 : Nat := 4983230072969 + 3 ^ 40 * 1816242 * 2
def baseEnd_1816242 : Nat := 932605130883388178522261

theorem tailTrace_1816242 : CollatzResearch.WordTrace tailWord_1816242 prefixEnd_1816242 932605130883388178522261 := by
  unfold tailWord_1816242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16560946971518224570816745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44162525257381932188844653 16560946971518224570816745)
  ·
    refine ⟨12420710228638668428112559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16560946971518224570816745 12420710228638668428112559)
    ·
      refine ⟨18631065342958002642168839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12420710228638668428112559 18631065342958002642168839)
      ·
        refine ⟨27946598014437003963253259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18631065342958002642168839 27946598014437003963253259)
        ·
          refine ⟨41919897021655505944879889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27946598014437003963253259 41919897021655505944879889)
          ·
            refine ⟨31439922766241629458659917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41919897021655505944879889 31439922766241629458659917)
            ·
              refine ⟨11789971037340611046997469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31439922766241629458659917 11789971037340611046997469)
              ·
                refine ⟨4421239139002729142624051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11789971037340611046997469 4421239139002729142624051)
                ·
                  refine ⟨6631858708504093713936077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421239139002729142624051 6631858708504093713936077)
                  ·
                    refine ⟨2486947015689035142726029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6631858708504093713936077 2486947015689035142726029)
                    ·
                      refine ⟨932605130883388178522261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2486947015689035142726029 932605130883388178522261)
                      ·
                        rfl

theorem cell23_1816242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1816242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816242 prefixEnd_1816242 := by exact prefixLift 1816242
  have htrace : WordTrace (prefixWord ++ tailWord_1816242) baseStart_1816242 baseEnd_1816242 := by
    simpa [prefixWord, tailWord_1816242, baseEnd_1816242] using wordTrace_append hprefix tailTrace_1816242
  have hstable : (prefixWord ++ tailWord_1816242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816242).length < 2 ^ (prefixWord ++ tailWord_1816242).sum := by decide
  have hdescent : baseEnd_1816242 < baseStart_1816242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816246 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1816246 : Nat := 118140960795 + 1816246 * 2 ^ 59
def prefixEnd_1816246 : Nat := 4983230072969 + 3 ^ 40 * 1816246 * 2
def baseEnd_1816246 : Nat := 932607184806006162872243

theorem tailTrace_1816246 : CollatzResearch.WordTrace tailWord_1816246 prefixEnd_1816246 932607184806006162872243 := by
  unfold tailWord_1816246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140245861128650435400787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44162622518705604644275061 4140245861128650435400787)
  ·
    refine ⟨6210368791692975653101181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4140245861128650435400787 6210368791692975653101181)
    ·
      refine ⟨2328888296884865869912943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6210368791692975653101181 2328888296884865869912943)
      ·
        refine ⟨3493332445327298804869415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328888296884865869912943 3493332445327298804869415)
        ·
          refine ⟨5239998667990948207304123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493332445327298804869415 5239998667990948207304123)
          ·
            refine ⟨7859998001986422310956185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239998667990948207304123 7859998001986422310956185)
            ·
              refine ⟨5894998501489816733217139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7859998001986422310956185 5894998501489816733217139)
              ·
                refine ⟨8842497752234725099825709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5894998501489816733217139 8842497752234725099825709)
                ·
                  refine ⟨3315936657088021912434641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8842497752234725099825709 3315936657088021912434641)
                  ·
                    refine ⟨2486952492816016434325981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3315936657088021912434641 2486952492816016434325981)
                    ·
                      refine ⟨932607184806006162872243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2486952492816016434325981 932607184806006162872243)
                      ·
                        rfl

theorem cell23_1816246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1816246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816246 prefixEnd_1816246 := by exact prefixLift 1816246
  have htrace : WordTrace (prefixWord ++ tailWord_1816246) baseStart_1816246 baseEnd_1816246 := by
    simpa [prefixWord, tailWord_1816246, baseEnd_1816246] using wordTrace_append hprefix tailTrace_1816246
  have hstable : (prefixWord ++ tailWord_1816246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816246).length < 2 ^ (prefixWord ++ tailWord_1816246).sum := by decide
  have hdescent : baseEnd_1816246 < baseStart_1816246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816255 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_1816255 : Nat := 118140960795 + 1816255 * 2 ^ 59
def prefixEnd_1816255 : Nat := 4983230072969 + 3 ^ 40 * 1816255 * 2
def baseEnd_1816255 : Nat := 932611806131896627659701

theorem tailTrace_1816255 : CollatzResearch.WordTrace tailWord_1816255 prefixEnd_1816255 932611806131896627659701 := by
  unfold tailWord_1816255
  simp only [CollatzResearch.WordTrace]
  refine ⟨66244262035025801503490219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44162841356683867668993479 66244262035025801503490219)
  ·
    refine ⟨99366393052538702255235329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66244262035025801503490219 99366393052538702255235329)
    ·
      refine ⟨74524794789404026691426497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99366393052538702255235329 74524794789404026691426497)
      ·
        refine ⟨55893596092053020018569873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74524794789404026691426497 55893596092053020018569873)
        ·
          refine ⟨41920197069039765013927405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55893596092053020018569873 41920197069039765013927405)
          ·
            refine ⟨15720073900889911880222777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41920197069039765013927405 15720073900889911880222777)
            ·
              refine ⟨11790055425667433910167083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15720073900889911880222777 11790055425667433910167083)
              ·
                refine ⟨17685083138501150865250625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11790055425667433910167083 17685083138501150865250625)
                ·
                  refine ⟨13263812353875863148937969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17685083138501150865250625 13263812353875863148937969)
                  ·
                    refine ⟨9947859265406897361703477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13263812353875863148937969 9947859265406897361703477)
                    ·
                      refine ⟨932611806131896627659701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9947859265406897361703477 932611806131896627659701)
                      ·
                        rfl

theorem cell23_1816255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_1816255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816255 prefixEnd_1816255 := by exact prefixLift 1816255
  have htrace : WordTrace (prefixWord ++ tailWord_1816255) baseStart_1816255 baseEnd_1816255 := by
    simpa [prefixWord, tailWord_1816255, baseEnd_1816255] using wordTrace_append hprefix tailTrace_1816255
  have hstable : (prefixWord ++ tailWord_1816255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816255).length < 2 ^ (prefixWord ++ tailWord_1816255).sum := by decide
  have hdescent : baseEnd_1816255 < baseStart_1816255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816276 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1816276 : Nat := 118140960795 + 1816276 * 2 ^ 59
def prefixEnd_1816276 : Nat := 4983230072969 + 3 ^ 40 * 1816276 * 2
def baseEnd_1816276 : Nat := 932622589225641045497105

theorem tailTrace_1816276 : CollatzResearch.WordTrace tailWord_1816276 prefixEnd_1816276 932622589225641045497105 := by
  unfold tailWord_1816276
  simp only [CollatzResearch.WordTrace]
  refine ⟨33122513983974861045002341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44163351978633148060003121 33122513983974861045002341)
  ·
    refine ⟨6210471371995286445937939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33122513983974861045002341 6210471371995286445937939)
    ·
      refine ⟨9315707057992929668906909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6210471371995286445937939 9315707057992929668906909)
      ·
        refine ⟨3493390146747348625840091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9315707057992929668906909 3493390146747348625840091)
        ·
          refine ⟨5240085220121022938760137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493390146747348625840091 5240085220121022938760137)
          ·
            refine ⟨3930063915090767204070103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5240085220121022938760137 3930063915090767204070103)
            ·
              refine ⟨5895095872636150806105155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930063915090767204070103 5895095872636150806105155)
              ·
                refine ⟨8842643808954226209157733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895095872636150806105155 8842643808954226209157733)
                ·
                  refine ⟨1657995714178917414217075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8842643808954226209157733 1657995714178917414217075)
                  ·
                    refine ⟨2486993571268376121325613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1657995714178917414217075 2486993571268376121325613)
                    ·
                      refine ⟨932622589225641045497105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2486993571268376121325613 932622589225641045497105)
                      ·
                        rfl

theorem cell23_1816276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1816276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816276 prefixEnd_1816276 := by exact prefixLift 1816276
  have htrace : WordTrace (prefixWord ++ tailWord_1816276) baseStart_1816276 baseEnd_1816276 := by
    simpa [prefixWord, tailWord_1816276, baseEnd_1816276] using wordTrace_append hprefix tailTrace_1816276
  have hstable : (prefixWord ++ tailWord_1816276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816276).length < 2 ^ (prefixWord ++ tailWord_1816276).sum := by decide
  have hdescent : baseEnd_1816276 < baseStart_1816276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816299 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 1, 4, 2]
def baseStart_1816299 : Nat := 118140960795 + 1816299 * 2 ^ 59
def prefixEnd_1816299 : Nat := 4983230072969 + 3 ^ 40 * 1816299 * 2
def baseEnd_1816299 : Nat := 932634399280694455509499

theorem tailTrace_1816299 : CollatzResearch.WordTrace tailWord_1816299 prefixEnd_1816299 932634399280694455509499 := by
  unfold tailWord_1816299
  simp only [CollatzResearch.WordTrace]
  refine ⟨66245866846866397018091951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44163911231244264678727967 66245866846866397018091951)
  ·
    refine ⟨99368800270299595527137927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66245866846866397018091951 99368800270299595527137927)
    ·
      refine ⟨149053200405449393290706891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99368800270299595527137927 149053200405449393290706891)
      ·
        refine ⟨223579800608174089936060337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149053200405449393290706891 223579800608174089936060337)
        ·
          refine ⟨167684850456130567452045253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223579800608174089936060337 167684850456130567452045253)
          ·
            refine ⟨31440909460524481397258485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167684850456130567452045253 31440909460524481397258485)
            ·
              refine ⟨2947585261924170130992983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31440909460524481397258485 2947585261924170130992983)
              ·
                refine ⟨4421377892886255196489475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947585261924170130992983 4421377892886255196489475)
                ·
                  refine ⟨6632066839329382794734213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421377892886255196489475 6632066839329382794734213)
                  ·
                    refine ⟨1243512532374259274012665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632066839329382794734213 1243512532374259274012665)
                    ·
                      refine ⟨932634399280694455509499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1243512532374259274012665 932634399280694455509499)
                      ·
                        rfl

theorem cell23_1816299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 4, 2].length) (baseStart_1816299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816299 prefixEnd_1816299 := by exact prefixLift 1816299
  have htrace : WordTrace (prefixWord ++ tailWord_1816299) baseStart_1816299 baseEnd_1816299 := by
    simpa [prefixWord, tailWord_1816299, baseEnd_1816299] using wordTrace_append hprefix tailTrace_1816299
  have hstable : (prefixWord ++ tailWord_1816299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816299).length < 2 ^ (prefixWord ++ tailWord_1816299).sum := by decide
  have hdescent : baseEnd_1816299 < baseStart_1816299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816302 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1816302 : Nat := 118140960795 + 1816302 * 2 ^ 59
def prefixEnd_1816302 : Nat := 4983230072969 + 3 ^ 40 * 1816302 * 2
def baseEnd_1816302 : Nat := 932635939722657943771985

theorem tailTrace_1816302 : CollatzResearch.WordTrace tailWord_1816302 prefixEnd_1816302 932635939722657943771985 := by
  unfold tailWord_1816302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280747033231941066306395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44163984177237019020300773 8280747033231941066306395)
  ·
    refine ⟨12421120549847911599459593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8280747033231941066306395 12421120549847911599459593)
    ·
      refine ⟨9315840412385933699594695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12421120549847911599459593 9315840412385933699594695)
      ·
        refine ⟨13973760618578900549392043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9315840412385933699594695 13973760618578900549392043)
        ·
          refine ⟨20960640927868350824088065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13973760618578900549392043 20960640927868350824088065)
          ·
            refine ⟨15720480695901263118066049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20960640927868350824088065 15720480695901263118066049)
            ·
              refine ⟨11790360521925947338549537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15720480695901263118066049 11790360521925947338549537)
              ·
                refine ⟨8842770391444460503912153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11790360521925947338549537 8842770391444460503912153)
                ·
                  refine ⟨6632077793583345377934115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8842770391444460503912153 6632077793583345377934115)
                  ·
                    refine ⟨9948116690375018066901173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632077793583345377934115 9948116690375018066901173)
                    ·
                      refine ⟨932635939722657943771985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9948116690375018066901173 932635939722657943771985)
                      ·
                        rfl

theorem cell23_1816302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1816302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816302 prefixEnd_1816302 := by exact prefixLift 1816302
  have htrace : WordTrace (prefixWord ++ tailWord_1816302) baseStart_1816302 baseEnd_1816302 := by
    simpa [prefixWord, tailWord_1816302, baseEnd_1816302] using wordTrace_append hprefix tailTrace_1816302
  have hstable : (prefixWord ++ tailWord_1816302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816302).length < 2 ^ (prefixWord ++ tailWord_1816302).sum := by decide
  have hdescent : baseEnd_1816302 < baseStart_1816302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816325 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_1816325 : Nat := 118140960795 + 1816325 * 2 ^ 59
def prefixEnd_1816325 : Nat := 4983230072969 + 3 ^ 40 * 1816325 * 2
def baseEnd_1816325 : Nat := 932647749777711353784379

theorem tailTrace_1816325 : CollatzResearch.WordTrace tailWord_1816325 prefixEnd_1816325 932647749777711353784379 := by
  unfold tailWord_1816325
  simp only [CollatzResearch.WordTrace]
  refine ⟨66246815144772203458538429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44164543429848135639025619 66246815144772203458538429)
  ·
    refine ⟨24842555679289576296951911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66246815144772203458538429 24842555679289576296951911)
    ·
      refine ⟨37263833518934364445427867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24842555679289576296951911 37263833518934364445427867)
      ·
        refine ⟨55895750278401546668141801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37263833518934364445427867 55895750278401546668141801)
        ·
          refine ⟨41921812708801160001106351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55895750278401546668141801 41921812708801160001106351)
          ·
            refine ⟨62882719063201740001659527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41921812708801160001106351 62882719063201740001659527)
            ·
              refine ⟨94324078594802610002489291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62882719063201740001659527 94324078594802610002489291)
              ·
                refine ⟨141486117892203915003733937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94324078594802610002489291 141486117892203915003733937)
                ·
                  refine ⟨106114588419152936252800453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141486117892203915003733937 106114588419152936252800453)
                  ·
                    refine ⟨19896485328591175547400085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106114588419152936252800453 19896485328591175547400085)
                    ·
                      refine ⟨932647749777711353784379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19896485328591175547400085 932647749777711353784379)
                      ·
                        rfl

theorem cell23_1816325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_1816325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816325 prefixEnd_1816325 := by exact prefixLift 1816325
  have htrace : WordTrace (prefixWord ++ tailWord_1816325) baseStart_1816325 baseEnd_1816325 := by
    simpa [prefixWord, tailWord_1816325, baseEnd_1816325] using wordTrace_append hprefix tailTrace_1816325
  have hstable : (prefixWord ++ tailWord_1816325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816325).length < 2 ^ (prefixWord ++ tailWord_1816325).sum := by decide
  have hdescent : baseEnd_1816325 < baseStart_1816325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816332 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1816332 : Nat := 118140960795 + 1816332 * 2 ^ 59
def prefixEnd_1816332 : Nat := 4983230072969 + 3 ^ 40 * 1816332 * 2
def baseEnd_1816332 : Nat := 932651344142292826396847

theorem tailTrace_1816332 : CollatzResearch.WordTrace tailWord_1816332 prefixEnd_1816332 932651344142292826396847 := by
  unfold tailWord_1816332
  simp only [CollatzResearch.WordTrace]
  refine ⟨33123535227873421827021625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44164713637164562436028833 33123535227873421827021625)
  ·
    refine ⟨24842651420905066370266219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33123535227873421827021625 24842651420905066370266219)
    ·
      refine ⟨37263977131357599555399329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24842651420905066370266219 37263977131357599555399329)
      ·
        refine ⟨27947982848518199666549497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37263977131357599555399329 27947982848518199666549497)
        ·
          refine ⟨20960987136388649749912123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27947982848518199666549497 20960987136388649749912123)
          ·
            refine ⟨31441480704582974624868185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20960987136388649749912123 31441480704582974624868185)
            ·
              refine ⟨23581110528437230968651139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31441480704582974624868185 23581110528437230968651139)
              ·
                refine ⟨35371665792655846452976709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23581110528437230968651139 35371665792655846452976709)
                ·
                  refine ⟨6632187336122971209933133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35371665792655846452976709 6632187336122971209933133)
                  ·
                    refine ⟨2487070251046114203724925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6632187336122971209933133 2487070251046114203724925)
                    ·
                      refine ⟨932651344142292826396847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2487070251046114203724925 932651344142292826396847)
                      ·
                        rfl

theorem cell23_1816332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1816332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816332 prefixEnd_1816332 := by exact prefixLift 1816332
  have htrace : WordTrace (prefixWord ++ tailWord_1816332) baseStart_1816332 baseEnd_1816332 := by
    simpa [prefixWord, tailWord_1816332, baseEnd_1816332] using wordTrace_append hprefix tailTrace_1816332
  have hstable : (prefixWord ++ tailWord_1816332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816332).length < 2 ^ (prefixWord ++ tailWord_1816332).sum := by decide
  have hdescent : baseEnd_1816332 < baseStart_1816332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816335 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 3, 7]
def baseStart_1816335 : Nat := 118140960795 + 1816335 * 2 ^ 59
def prefixEnd_1816335 : Nat := 4983230072969 + 3 ^ 40 * 1816335 * 2
def baseEnd_1816335 : Nat := 310884294861418771553111

theorem tailTrace_1816335 : CollatzResearch.WordTrace tailWord_1816335 prefixEnd_1816335 310884294861418771553111 := by
  unfold tailWord_1816335
  simp only [CollatzResearch.WordTrace]
  refine ⟨66247179874735975166402459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44164786583157316777601639 66247179874735975166402459)
  ·
    refine ⟨99370769812103962749603689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66247179874735975166402459 99370769812103962749603689)
    ·
      refine ⟨74528077359077972062202767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99370769812103962749603689 74528077359077972062202767)
      ·
        refine ⟨111792116038616958093304151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74528077359077972062202767 111792116038616958093304151)
        ·
          refine ⟨167688174057925437139956227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111792116038616958093304151 167688174057925437139956227)
          ·
            refine ⟨251532261086888155709934341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167688174057925437139956227 251532261086888155709934341)
            ·
              refine ⟨47162298953791529195612689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251532261086888155709934341 47162298953791529195612689)
              ·
                refine ⟨35371724215343646896709517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47162298953791529195612689 35371724215343646896709517)
                ·
                  refine ⟨13264396580753867586266069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35371724215343646896709517 13264396580753867586266069)
                  ·
                    refine ⟨310884294861418771553111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13264396580753867586266069 310884294861418771553111)
                    ·
                      rfl

theorem cell23_1816335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_1816335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816335 prefixEnd_1816335 := by exact prefixLift 1816335
  have htrace : WordTrace (prefixWord ++ tailWord_1816335) baseStart_1816335 baseEnd_1816335 := by
    simpa [prefixWord, tailWord_1816335, baseEnd_1816335] using wordTrace_append hprefix tailTrace_1816335
  have hstable : (prefixWord ++ tailWord_1816335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816335).length < 2 ^ (prefixWord ++ tailWord_1816335).sum := by decide
  have hdescent : baseEnd_1816335 < baseStart_1816335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816352 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 4, 5]
def baseStart_1816352 : Nat := 118140960795 + 1816352 * 2 ^ 59
def prefixEnd_1816352 : Nat := 4983230072969 + 3 ^ 40 * 1816352 * 2
def baseEnd_1816352 : Nat := 310887204585127582715585

theorem tailTrace_1816352 : CollatzResearch.WordTrace tailWord_1816352 prefixEnd_1816352 310887204585127582715585 := by
  unfold tailWord_1816352
  simp only [CollatzResearch.WordTrace]
  refine ⟨33123899957837193534885655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44165199943782924713180873 33123899957837193534885655)
  ·
    refine ⟨49685849936755790302328483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33123899957837193534885655 49685849936755790302328483)
    ·
      refine ⟨74528774905133685453492725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49685849936755790302328483 74528774905133685453492725)
      ·
        refine ⟨6987072647356283011264943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74528774905133685453492725 6987072647356283011264943)
        ·
          refine ⟨10480608971034424516897415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987072647356283011264943 10480608971034424516897415)
          ·
            refine ⟨15720913456551636775346123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480608971034424516897415 15720913456551636775346123)
            ·
              refine ⟨23581370184827455163019185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15720913456551636775346123 23581370184827455163019185)
              ·
                refine ⟨17686027638620591372264389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23581370184827455163019185 17686027638620591372264389)
                ·
                  refine ⟨3316130182241360882299573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17686027638620591372264389 3316130182241360882299573)
                  ·
                    refine ⟨310887204585127582715585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3316130182241360882299573 310887204585127582715585)
                    ·
                      rfl

theorem cell23_1816352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_1816352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816352 prefixEnd_1816352 := by exact prefixLift 1816352
  have htrace : WordTrace (prefixWord ++ tailWord_1816352) baseStart_1816352 baseEnd_1816352 := by
    simpa [prefixWord, tailWord_1816352, baseEnd_1816352] using wordTrace_append hprefix tailTrace_1816352
  have hstable : (prefixWord ++ tailWord_1816352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816352).length < 2 ^ (prefixWord ++ tailWord_1816352).sum := by decide
  have hdescent : baseEnd_1816352 < baseStart_1816352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816369 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 2, 5]
def baseStart_1816369 : Nat := 118140960795 + 1816369 * 2 ^ 59
def prefixEnd_1816369 : Nat := 4983230072969 + 3 ^ 40 * 1816369 * 2
def baseEnd_1816369 : Nat := 310890114308836393878059

theorem tailTrace_1816369 : CollatzResearch.WordTrace tailWord_1816369 prefixEnd_1816369 310890114308836393878059 := by
  unfold tailWord_1816369
  simp only [CollatzResearch.WordTrace]
  refine ⟨66248419956612798973140161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44165613304408532648760107 66248419956612798973140161)
  ·
    refine ⟨49686314967459599229855121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66248419956612798973140161 49686314967459599229855121)
    ·
      refine ⟨37264736225594699422391341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49686314967459599229855121 37264736225594699422391341)
      ·
        refine ⟨13974276084598012283396753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37264736225594699422391341 13974276084598012283396753)
        ·
          refine ⟨10480707063448509212547565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13974276084598012283396753 10480707063448509212547565)
          ·
            refine ⟨3930265148793190954705337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10480707063448509212547565 3930265148793190954705337)
            ·
              refine ⟨2947698861594893216029003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3930265148793190954705337 2947698861594893216029003)
              ·
                refine ⟨4421548292392339824043505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947698861594893216029003 4421548292392339824043505)
                ·
                  refine ⟨3316161219294254868032629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4421548292392339824043505 3316161219294254868032629)
                  ·
                    refine ⟨310890114308836393878059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3316161219294254868032629 310890114308836393878059)
                    ·
                      rfl

theorem cell23_1816369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_1816369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816369 prefixEnd_1816369 := by exact prefixLift 1816369
  have htrace : WordTrace (prefixWord ++ tailWord_1816369) baseStart_1816369 baseEnd_1816369 := by
    simpa [prefixWord, tailWord_1816369, baseEnd_1816369] using wordTrace_append hprefix tailTrace_1816369
  have hstable : (prefixWord ++ tailWord_1816369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816369).length < 2 ^ (prefixWord ++ tailWord_1816369).sum := by decide
  have hdescent : baseEnd_1816369 < baseStart_1816369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816389 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 2, 4, 2]
def baseStart_1816389 : Nat := 118140960795 + 1816389 * 2 ^ 59
def prefixEnd_1816389 : Nat := 4983230072969 + 3 ^ 40 * 1816389 * 2
def baseEnd_1816389 : Nat := 932680612539599103384085

theorem tailTrace_1816389 : CollatzResearch.WordTrace tailWord_1816389 prefixEnd_1816389 932680612539599103384085 := by
  unfold tailWord_1816389
  simp only [CollatzResearch.WordTrace]
  refine ⟨66249149416540342388868221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44166099611026894925912147 66249149416540342388868221)
  ·
    refine ⟨24843431031202628395825583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66249149416540342388868221 24843431031202628395825583)
    ·
      refine ⟨37265146546803942593738375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24843431031202628395825583 37265146546803942593738375)
      ·
        refine ⟨55897719820205913890607563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37265146546803942593738375 55897719820205913890607563)
        ·
          refine ⟨83846579730308870835911345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55897719820205913890607563 83846579730308870835911345)
          ·
            refine ⟨62884934797731653126933509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83846579730308870835911345 62884934797731653126933509)
            ·
              refine ⟨11790925274574684961300033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62884934797731653126933509 11790925274574684961300033)
              ·
                refine ⟨8843193955931013720975025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11790925274574684961300033 8843193955931013720975025)
                ·
                  refine ⟨6632395466948260290731269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8843193955931013720975025 6632395466948260290731269)
                  ·
                    refine ⟨1243574150052798804512113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632395466948260290731269 1243574150052798804512113)
                    ·
                      refine ⟨932680612539599103384085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1243574150052798804512113 932680612539599103384085)
                      ·
                        rfl

theorem cell23_1816389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_1816389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816389 prefixEnd_1816389 := by exact prefixLift 1816389
  have htrace : WordTrace (prefixWord ++ tailWord_1816389) baseStart_1816389 baseEnd_1816389 := by
    simpa [prefixWord, tailWord_1816389, baseEnd_1816389] using wordTrace_append hprefix tailTrace_1816389
  have hstable : (prefixWord ++ tailWord_1816389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816389).length < 2 ^ (prefixWord ++ tailWord_1816389).sum := by decide
  have hdescent : baseEnd_1816389 < baseStart_1816389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816390 : List Nat := [6, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1816390 : Nat := 118140960795 + 1816390 * 2 ^ 59
def prefixEnd_1816390 : Nat := 4983230072969 + 3 ^ 40 * 1816390 * 2
def baseEnd_1816390 : Nat := 103631236224472622163509

theorem tailTrace_1816390 : CollatzResearch.WordTrace tailWord_1816390 prefixEnd_1816390 103631236224472622163509 := by
  unfold tailWord_1816390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070287059048022486239207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44166123926357813039769749 2070287059048022486239207)
  ·
    refine ⟨3105430588572033729358811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2070287059048022486239207 3105430588572033729358811)
    ·
      refine ⟨4658145882858050594038217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105430588572033729358811 4658145882858050594038217)
      ·
        refine ⟨3493609412143537945528663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4658145882858050594038217 3493609412143537945528663)
        ·
          refine ⟨5240414118215306918292995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493609412143537945528663 5240414118215306918292995)
          ·
            refine ⟨7860621177322960377439493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240414118215306918292995 7860621177322960377439493)
            ·
              refine ⟨1473866470748055070769905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7860621177322960377439493 1473866470748055070769905)
              ·
                refine ⟨1105399853061041303077429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473866470748055070769905 1105399853061041303077429)
                ·
                  refine ⟨103631236224472622163509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1105399853061041303077429 103631236224472622163509)
                  ·
                    rfl

theorem cell23_1816390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1816390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816390 prefixEnd_1816390 := by exact prefixLift 1816390
  have htrace : WordTrace (prefixWord ++ tailWord_1816390) baseStart_1816390 baseEnd_1816390 := by
    simpa [prefixWord, tailWord_1816390, baseEnd_1816390] using wordTrace_append hprefix tailTrace_1816390
  have hstable : (prefixWord ++ tailWord_1816390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816390).length < 2 ^ (prefixWord ++ tailWord_1816390).sum := by decide
  have hdescent : baseEnd_1816390 < baseStart_1816390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816446 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_1816446 : Nat := 118140960795 + 1816446 * 2 ^ 59
def prefixEnd_1816446 : Nat := 4983230072969 + 3 ^ 40 * 1816446 * 2
def baseEnd_1816446 : Nat := 103634431215211708930147

theorem tailTrace_1816446 : CollatzResearch.WordTrace tailWord_1816446 prefixEnd_1816446 103634431215211708930147 := by
  unfold tailWord_1816446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281403547166730140461649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44167485584889227415795461 8281403547166730140461649)
  ·
    refine ⟨6211052660375047605346237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8281403547166730140461649 6211052660375047605346237)
    ·
      refine ⟨2329144747640642852004839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6211052660375047605346237 2329144747640642852004839)
      ·
        refine ⟨3493717121460964278007259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2329144747640642852004839 3493717121460964278007259)
        ·
          refine ⟨5240575682191446417010889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493717121460964278007259 5240575682191446417010889)
          ·
            refine ⟨3930431761643584812758167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5240575682191446417010889 3930431761643584812758167)
            ·
              refine ⟨5895647642465377219137251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930431761643584812758167 5895647642465377219137251)
              ·
                refine ⟨8843471463698065828705877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895647642465377219137251 8843471463698065828705877)
                ·
                  refine ⟨103634431215211708930147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8843471463698065828705877 103634431215211708930147)
                  ·
                    rfl

theorem cell23_1816446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_1816446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816446 prefixEnd_1816446 := by exact prefixLift 1816446
  have htrace : WordTrace (prefixWord ++ tailWord_1816446) baseStart_1816446 baseEnd_1816446 := by
    simpa [prefixWord, tailWord_1816446, baseEnd_1816446] using wordTrace_append hprefix tailTrace_1816446
  have hstable : (prefixWord ++ tailWord_1816446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816446).length < 2 ^ (prefixWord ++ tailWord_1816446).sum := by decide
  have hdescent : baseEnd_1816446 < baseStart_1816446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816476 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1816476 : Nat := 118140960795 + 1816476 * 2 ^ 59
def prefixEnd_1816476 : Nat := 4983230072969 + 3 ^ 40 * 1816476 * 2
def baseEnd_1816476 : Nat := 310908428452180087665395

theorem tailTrace_1816476 : CollatzResearch.WordTrace tailWord_1816476 prefixEnd_1816476 310908428452180087665395 := by
  unfold tailWord_1816476
  simp only [CollatzResearch.WordTrace]
  refine ⟨33126161283612578123642641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44168215044816770831523521 33126161283612578123642641)
  ·
    refine ⟨24844620962709433592731981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33126161283612578123642641 24844620962709433592731981)
    ·
      refine ⟨9316732861016037597274493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24844620962709433592731981 9316732861016037597274493)
      ·
        refine ⟨3493774822881014098977935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9316732861016037597274493 3493774822881014098977935)
        ·
          refine ⟨5240662234321521148466903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493774822881014098977935 5240662234321521148466903)
          ·
            refine ⟨7860993351482281722700355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240662234321521148466903 7860993351482281722700355)
            ·
              refine ⟨11791490027223422584050533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7860993351482281722700355 11791490027223422584050533)
              ·
                refine ⟨2210904380104391734509475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11791490027223422584050533 2210904380104391734509475)
                ·
                  refine ⟨3316356570156587601764213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210904380104391734509475 3316356570156587601764213)
                  ·
                    refine ⟨310908428452180087665395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3316356570156587601764213 310908428452180087665395)
                    ·
                      rfl

theorem cell23_1816476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1816476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816476 prefixEnd_1816476 := by exact prefixLift 1816476
  have htrace : WordTrace (prefixWord ++ tailWord_1816476) baseStart_1816476 baseEnd_1816476 := by
    simpa [prefixWord, tailWord_1816476, baseEnd_1816476] using wordTrace_append hprefix tailTrace_1816476
  have hstable : (prefixWord ++ tailWord_1816476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816476).length < 2 ^ (prefixWord ++ tailWord_1816476).sum := by decide
  have hdescent : baseEnd_1816476 < baseStart_1816476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816492 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_1816492 : Nat := 118140960795 + 1816492 * 2 ^ 59
def prefixEnd_1816492 : Nat := 4983230072969 + 3 ^ 40 * 1816492 * 2
def baseEnd_1816492 : Nat := 932733501047012200396111

theorem tailTrace_1816492 : CollatzResearch.WordTrace tailWord_1816492 prefixEnd_1816492 932733501047012200396111 := by
  unfold tailWord_1816492
  simp only [CollatzResearch.WordTrace]
  refine ⟨33126453067583595489933865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44168604090111460653245153 33126453067583595489933865)
  ·
    refine ⟨24844839800687696617450399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33126453067583595489933865 24844839800687696617450399)
    ·
      refine ⟨37267259701031544926175599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24844839800687696617450399 37267259701031544926175599)
      ·
        refine ⟨55900889551547317389263399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37267259701031544926175599 55900889551547317389263399)
        ·
          refine ⟨83851334327320976083895099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55900889551547317389263399 83851334327320976083895099)
          ·
            refine ⟨125777001490981464125842649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83851334327320976083895099 125777001490981464125842649)
            ·
              refine ⟨94332751118236098094381987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125777001490981464125842649 94332751118236098094381987)
              ·
                refine ⟨141499126677354147141572981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94332751118236098094381987 141499126677354147141572981)
                ·
                  refine ⟨13265543126001951294522467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141499126677354147141572981 13265543126001951294522467)
                  ·
                    refine ⟨19898314689002926941783701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13265543126001951294522467 19898314689002926941783701)
                    ·
                      refine ⟨932733501047012200396111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19898314689002926941783701 932733501047012200396111)
                      ·
                        rfl

theorem cell23_1816492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_1816492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816492 prefixEnd_1816492 := by exact prefixLift 1816492
  have htrace : WordTrace (prefixWord ++ tailWord_1816492) baseStart_1816492 baseEnd_1816492 := by
    simpa [prefixWord, tailWord_1816492, baseEnd_1816492] using wordTrace_append hprefix tailTrace_1816492
  have hstable : (prefixWord ++ tailWord_1816492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816492).length < 2 ^ (prefixWord ++ tailWord_1816492).sum := by decide
  have hdescent : baseEnd_1816492 < baseStart_1816492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816499 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 5]
def baseStart_1816499 : Nat := 118140960795 + 1816499 * 2 ^ 59
def prefixEnd_1816499 : Nat := 4983230072969 + 3 ^ 40 * 1816499 * 2
def baseEnd_1816499 : Nat := 932737095411593673008579

theorem tailTrace_1816499 : CollatzResearch.WordTrace tailWord_1816499 prefixEnd_1816499 932737095411593673008579 := by
  unfold tailWord_1816499
  simp only [CollatzResearch.WordTrace]
  refine ⟨66253161446141831175372551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44168774297427887450248367 66253161446141831175372551)
  ·
    refine ⟨99379742169212746763058827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66253161446141831175372551 99379742169212746763058827)
    ·
      refine ⟨149069613253819120144588241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99379742169212746763058827 149069613253819120144588241)
      ·
        refine ⟨111802209940364340108441181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149069613253819120144588241 111802209940364340108441181)
        ·
          refine ⟨41925828727636627540665443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111802209940364340108441181 41925828727636627540665443)
          ·
            refine ⟨62888743091454941310998165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41925828727636627540665443 62888743091454941310998165)
            ·
              refine ⟨2947909832411950373953039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62888743091454941310998165 2947909832411950373953039)
              ·
                refine ⟨4421864748617925560929559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947909832411950373953039 4421864748617925560929559)
                ·
                  refine ⟨6632797122926888341394339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421864748617925560929559 6632797122926888341394339)
                  ·
                    refine ⟨9949195684390332512091509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632797122926888341394339 9949195684390332512091509)
                    ·
                      refine ⟨932737095411593673008579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9949195684390332512091509 932737095411593673008579)
                      ·
                        rfl

theorem cell23_1816499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_1816499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816499 prefixEnd_1816499 := by exact prefixLift 1816499
  have htrace : WordTrace (prefixWord ++ tailWord_1816499) baseStart_1816499 baseEnd_1816499 := by
    simpa [prefixWord, tailWord_1816499, baseEnd_1816499] using wordTrace_append hprefix tailTrace_1816499
  have hstable : (prefixWord ++ tailWord_1816499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816499).length < 2 ^ (prefixWord ++ tailWord_1816499).sum := by decide
  have hdescent : baseEnd_1816499 < baseStart_1816499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816509 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1816509 : Nat := 118140960795 + 1816509 * 2 ^ 59
def prefixEnd_1816509 : Nat := 4983230072969 + 3 ^ 40 * 1816509 * 2
def baseEnd_1816509 : Nat := 932742230218138633883533

theorem tailTrace_1816509 : CollatzResearch.WordTrace tailWord_1816509 prefixEnd_1816509 932742230218138633883533 := by
  unfold tailWord_1816509
  simp only [CollatzResearch.WordTrace]
  refine ⟨66253526176105602883236581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44169017450737068588824387 66253526176105602883236581)
  ·
    refine ⟨12422536158019800540606859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66253526176105602883236581 12422536158019800540606859)
    ·
      refine ⟨18633804237029700810910289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12422536158019800540606859 18633804237029700810910289)
      ·
        refine ⟨13975353177772275608182717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18633804237029700810910289 13975353177772275608182717)
        ·
          refine ⟨5240757441664603353068519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13975353177772275608182717 5240757441664603353068519)
          ·
            refine ⟨7861136162496905029602779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240757441664603353068519 7861136162496905029602779)
            ·
              refine ⟨11791704243745357544404169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861136162496905029602779 11791704243745357544404169)
              ·
                refine ⟨8843778182809018158303127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11791704243745357544404169 8843778182809018158303127)
                ·
                  refine ⟨13265667274213527237454691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843778182809018158303127 13265667274213527237454691)
                  ·
                    refine ⟨19898500911320290856182037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13265667274213527237454691 19898500911320290856182037)
                    ·
                      refine ⟨932742230218138633883533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19898500911320290856182037 932742230218138633883533)
                      ·
                        rfl

theorem cell23_1816509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1816509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816509 prefixEnd_1816509 := by exact prefixLift 1816509
  have htrace : WordTrace (prefixWord ++ tailWord_1816509) baseStart_1816509 baseEnd_1816509 := by
    simpa [prefixWord, tailWord_1816509, baseEnd_1816509] using wordTrace_append hprefix tailTrace_1816509
  have hstable : (prefixWord ++ tailWord_1816509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816509).length < 2 ^ (prefixWord ++ tailWord_1816509).sum := by decide
  have hdescent : baseEnd_1816509 < baseStart_1816509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816530 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1816530 : Nat := 118140960795 + 1816530 * 2 ^ 59
def prefixEnd_1816530 : Nat := 4983230072969 + 3 ^ 40 * 1816530 * 2
def baseEnd_1816530 : Nat := 932753013311883051720937

theorem tailTrace_1816530 : CollatzResearch.WordTrace tailWord_1816530 prefixEnd_1816530 932753013311883051720937 := by
  unfold tailWord_1816530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16563573027257380867437761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44169528072686348979834029 16563573027257380867437761)
  ·
    refine ⟨12422679770443035650578321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16563573027257380867437761 12422679770443035650578321)
    ·
      refine ⟨9317009827832276737933741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12422679770443035650578321 9317009827832276737933741)
      ·
        refine ⟨3493878685437103776725153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9317009827832276737933741 3493878685437103776725153)
        ·
          refine ⟨2620409014077827832543865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3493878685437103776725153 2620409014077827832543865)
          ·
            refine ⟨1965306760558370874407899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620409014077827832543865 1965306760558370874407899)
            ·
              refine ⟨2947960140837556311611849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965306760558370874407899 2947960140837556311611849)
              ·
                refine ⟨2210970105628167233708887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947960140837556311611849 2210970105628167233708887)
                ·
                  refine ⟨3316455158442250850563331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210970105628167233708887 3316455158442250850563331)
                  ·
                    refine ⟨4974682737663376275844997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3316455158442250850563331 4974682737663376275844997)
                    ·
                      refine ⟨932753013311883051720937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4974682737663376275844997 932753013311883051720937)
                      ·
                        rfl

theorem cell23_1816530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1816530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816530 prefixEnd_1816530 := by exact prefixLift 1816530
  have htrace : WordTrace (prefixWord ++ tailWord_1816530) baseStart_1816530 baseEnd_1816530 := by
    simpa [prefixWord, tailWord_1816530, baseEnd_1816530] using wordTrace_append hprefix tailTrace_1816530
  have hstable : (prefixWord ++ tailWord_1816530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816530).length < 2 ^ (prefixWord ++ tailWord_1816530).sum := by decide
  have hdescent : baseEnd_1816530 < baseStart_1816530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816533 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1816533 : Nat := 118140960795 + 1816533 * 2 ^ 59
def prefixEnd_1816533 : Nat := 4983230072969 + 3 ^ 40 * 1816533 * 2
def baseEnd_1816533 : Nat := 932754553753846539983423

theorem tailTrace_1816533 : CollatzResearch.WordTrace tailWord_1816533 prefixEnd_1816533 932754553753846539983423 := by
  unfold tailWord_1816533
  simp only [CollatzResearch.WordTrace]
  refine ⟨66254401528018654982110253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44169601018679103321406835 66254401528018654982110253)
  ·
    refine ⟨24845400573006995618291345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66254401528018654982110253 24845400573006995618291345)
    ·
      refine ⟨18634050429755246713718509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24845400573006995618291345 18634050429755246713718509)
      ·
        refine ⟨6987768911158217517644441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18634050429755246713718509 6987768911158217517644441)
        ·
          refine ⟨5240826683368663138233331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6987768911158217517644441 5240826683368663138233331)
          ·
            refine ⟨7861240025052994707349997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240826683368663138233331 7861240025052994707349997)
            ·
              refine ⟨2947965009394873015256249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7861240025052994707349997 2947965009394873015256249)
              ·
                refine ⟨2210973757046154761442187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947965009394873015256249 2210973757046154761442187)
                ·
                  refine ⟨3316460635569232142163281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210973757046154761442187 3316460635569232142163281)
                  ·
                    refine ⟨2487345476676924106622461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3316460635569232142163281 2487345476676924106622461)
                    ·
                      refine ⟨932754553753846539983423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2487345476676924106622461 932754553753846539983423)
                      ·
                        rfl

theorem cell23_1816533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1816533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816533 prefixEnd_1816533 := by exact prefixLift 1816533
  have htrace : WordTrace (prefixWord ++ tailWord_1816533) baseStart_1816533 baseEnd_1816533 := by
    simpa [prefixWord, tailWord_1816533, baseEnd_1816533] using wordTrace_append hprefix tailTrace_1816533
  have hstable : (prefixWord ++ tailWord_1816533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816533).length < 2 ^ (prefixWord ++ tailWord_1816533).sum := by decide
  have hdescent : baseEnd_1816533 < baseStart_1816533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816540 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1816540 : Nat := 118140960795 + 1816540 * 2 ^ 59
def prefixEnd_1816540 : Nat := 4983230072969 + 3 ^ 40 * 1816540 * 2
def baseEnd_1816540 : Nat := 310919382706142670865297

theorem tailTrace_1816540 : CollatzResearch.WordTrace tailWord_1816540 prefixEnd_1816540 310919382706142670865297 := by
  unfold tailWord_1816540
  simp only [CollatzResearch.WordTrace]
  refine ⟨33127328419496647588807537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44169771225995530118410049 33127328419496647588807537)
  ·
    refine ⟨24845496314622485691605653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33127328419496647588807537 24845496314622485691605653)
    ·
      refine ⟨1164632639747929016794015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24845496314622485691605653 1164632639747929016794015)
      ·
        refine ⟨1746948959621893525191023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164632639747929016794015 1746948959621893525191023)
        ·
          refine ⟨2620423439432840287786535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1746948959621893525191023 2620423439432840287786535)
          ·
            refine ⟨3930635159149260431679803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620423439432840287786535 3930635159149260431679803)
            ·
              refine ⟨5895952738723890647519705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930635159149260431679803 5895952738723890647519705)
              ·
                refine ⟨4421964554042917985639779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5895952738723890647519705 4421964554042917985639779)
                ·
                  refine ⟨6632946831064376978459669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421964554042917985639779 6632946831064376978459669)
                  ·
                    refine ⟨310919382706142670865297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6632946831064376978459669 310919382706142670865297)
                    ·
                      rfl

theorem cell23_1816540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1816540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816540 prefixEnd_1816540 := by exact prefixLift 1816540
  have htrace : WordTrace (prefixWord ++ tailWord_1816540) baseStart_1816540 baseEnd_1816540 := by
    simpa [prefixWord, tailWord_1816540, baseEnd_1816540] using wordTrace_append hprefix tailTrace_1816540
  have hstable : (prefixWord ++ tailWord_1816540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816540).length < 2 ^ (prefixWord ++ tailWord_1816540).sum := by decide
  have hdescent : baseEnd_1816540 < baseStart_1816540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816569 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1816569 : Nat := 118140960795 + 1816569 * 2 ^ 59
def prefixEnd_1816569 : Nat := 4983230072969 + 3 ^ 40 * 1816569 * 2
def baseEnd_1816569 : Nat := 932773039057408399133257

theorem tailTrace_1816569 : CollatzResearch.WordTrace tailWord_1816569 prefixEnd_1816569 932773039057408399133257 := by
  unfold tailWord_1816569
  simp only [CollatzResearch.WordTrace]
  refine ⟨66255714555888233130420761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44170476370592155420280507 66255714555888233130420761)
  ·
    refine ⟨49691785916916174847815571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66255714555888233130420761 49691785916916174847815571)
    ·
      refine ⟨74537678875374262271723357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49691785916916174847815571 74537678875374262271723357)
      ·
        refine ⟨27951629578265348351896259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74537678875374262271723357 27951629578265348351896259)
        ·
          refine ⟨41927444367398022527844389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27951629578265348351896259 41927444367398022527844389)
          ·
            refine ⟨7861395818887129223970823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41927444367398022527844389 7861395818887129223970823)
            ·
              refine ⟨11792093728330693835956235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861395818887129223970823 11792093728330693835956235)
              ·
                refine ⟨17688140592496040753934353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11792093728330693835956235 17688140592496040753934353)
                ·
                  refine ⟨13266105444372030565450765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17688140592496040753934353 13266105444372030565450765)
                  ·
                    refine ⟨4974789541639511462044037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13266105444372030565450765 4974789541639511462044037)
                    ·
                      refine ⟨932773039057408399133257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4974789541639511462044037 932773039057408399133257)
                      ·
                        rfl

theorem cell23_1816569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1816569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816569 prefixEnd_1816569 := by exact prefixLift 1816569
  have htrace : WordTrace (prefixWord ++ tailWord_1816569) baseStart_1816569 baseEnd_1816569 := by
    simpa [prefixWord, tailWord_1816569, baseEnd_1816569] using wordTrace_append hprefix tailTrace_1816569
  have hstable : (prefixWord ++ tailWord_1816569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816569).length < 2 ^ (prefixWord ++ tailWord_1816569).sum := by decide
  have hdescent : baseEnd_1816569 < baseStart_1816569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816580 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1816580 : Nat := 118140960795 + 1816580 * 2 ^ 59
def prefixEnd_1816580 : Nat := 4983230072969 + 3 ^ 40 * 1816580 * 2
def baseEnd_1816580 : Nat := 932778687344607856095707

theorem tailTrace_1816580 : CollatzResearch.WordTrace tailWord_1816580 prefixEnd_1816580 932778687344607856095707 := by
  unfold tailWord_1816580
  simp only [CollatzResearch.WordTrace]
  refine ⟨33128057879424191004535597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44170743839232254672714129 33128057879424191004535597)
  ·
    refine ⟨12423021704784071626700849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33128057879424191004535597 12423021704784071626700849)
    ·
      refine ⟨9317266278588053720025637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12423021704784071626700849 9317266278588053720025637)
      ·
        refine ⟨1746987427235260072504807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9317266278588053720025637 1746987427235260072504807)
        ·
          refine ⟨2620481140852890108757211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1746987427235260072504807 2620481140852890108757211)
          ·
            refine ⟨3930721711279335163135817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620481140852890108757211 3930721711279335163135817)
            ·
              refine ⟨2948041283459501372351863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3930721711279335163135817 2948041283459501372351863)
              ·
                refine ⟨4422061925189252058527795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948041283459501372351863 4422061925189252058527795)
                ·
                  refine ⟨6633092887783878087791693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422061925189252058527795 6633092887783878087791693)
                  ·
                    refine ⟨2487409832918954282921885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6633092887783878087791693 2487409832918954282921885)
                    ·
                      refine ⟨932778687344607856095707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2487409832918954282921885 932778687344607856095707)
                      ·
                        rfl

theorem cell23_1816580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1816580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816580 prefixEnd_1816580 := by exact prefixLift 1816580
  have htrace : WordTrace (prefixWord ++ tailWord_1816580) baseStart_1816580 baseEnd_1816580 := by
    simpa [prefixWord, tailWord_1816580, baseEnd_1816580] using wordTrace_append hprefix tailTrace_1816580
  have hstable : (prefixWord ++ tailWord_1816580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816580).length < 2 ^ (prefixWord ++ tailWord_1816580).sum := by decide
  have hdescent : baseEnd_1816580 < baseStart_1816580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816626 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 7]
def baseStart_1816626 : Nat := 118140960795 + 1816626 * 2 ^ 59
def prefixEnd_1816626 : Nat := 4983230072969 + 3 ^ 40 * 1816626 * 2
def baseEnd_1816626 : Nat := 103644700828301630680055

theorem tailTrace_1816626 : CollatzResearch.WordTrace tailWord_1816626 prefixEnd_1816626 103644700828301630680055 := by
  unfold tailWord_1816626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16564448379170432966311433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44171862344454487910163821 16564448379170432966311433)
  ·
    refine ⟨12423336284377824724733575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16564448379170432966311433 12423336284377824724733575)
    ·
      refine ⟨18635004426566737087100363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423336284377824724733575 18635004426566737087100363)
      ·
        refine ⟨27952506639850105630650545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18635004426566737087100363 27952506639850105630650545)
        ·
          refine ⟨20964379979887579222987909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27952506639850105630650545 20964379979887579222987909)
          ·
            refine ⟨3930821246228921104310233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20964379979887579222987909 3930821246228921104310233)
            ·
              refine ⟨2948115934671690828232675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3930821246228921104310233 2948115934671690828232675)
              ·
                refine ⟨4422173902007536242349013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948115934671690828232675 4422173902007536242349013)
                ·
                  refine ⟨103644700828301630680055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4422173902007536242349013 103644700828301630680055)
                  ·
                    rfl

theorem cell23_1816626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_1816626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816626 prefixEnd_1816626 := by exact prefixLift 1816626
  have htrace : WordTrace (prefixWord ++ tailWord_1816626) baseStart_1816626 baseEnd_1816626 := by
    simpa [prefixWord, tailWord_1816626, baseEnd_1816626] using wordTrace_append hprefix tailTrace_1816626
  have hstable : (prefixWord ++ tailWord_1816626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816626).length < 2 ^ (prefixWord ++ tailWord_1816626).sum := by decide
  have hdescent : baseEnd_1816626 < baseStart_1816626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816636 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_1816636 : Nat := 118140960795 + 1816636 * 2 ^ 59
def prefixEnd_1816636 : Nat := 4983230072969 + 3 ^ 40 * 1816636 * 2
def baseEnd_1816636 : Nat := 932807442261259636995449

theorem tailTrace_1816636 : CollatzResearch.WordTrace tailWord_1816636 prefixEnd_1816636 932807442261259636995449 := by
  unfold tailWord_1816636
  simp only [CollatzResearch.WordTrace]
  refine ⟨33129079123322751786554881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44172105497763669048739841 33129079123322751786554881)
  ·
    refine ⟨24846809342492063839916161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33129079123322751786554881 24846809342492063839916161)
    ·
      refine ⟨18635107006869047879937121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24846809342492063839916161 18635107006869047879937121)
      ·
        refine ⟨13976330255151785909952841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18635107006869047879937121 13976330255151785909952841)
        ·
          refine ⟨10482247691363839432464631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13976330255151785909952841 10482247691363839432464631)
          ·
            refine ⟨15723371537045759148696947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482247691363839432464631 15723371537045759148696947)
            ·
              refine ⟨23585057305568638723045421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15723371537045759148696947 23585057305568638723045421)
              ·
                refine ⟨8844396489588239521142033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23585057305568638723045421 8844396489588239521142033)
                ·
                  refine ⟨6633297367191179640856525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8844396489588239521142033 6633297367191179640856525)
                  ·
                    refine ⟨2487486512696692365321197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6633297367191179640856525 2487486512696692365321197)
                    ·
                      refine ⟨932807442261259636995449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2487486512696692365321197 932807442261259636995449)
                      ·
                        rfl

theorem cell23_1816636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_1816636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816636 prefixEnd_1816636 := by exact prefixLift 1816636
  have htrace : WordTrace (prefixWord ++ tailWord_1816636) baseStart_1816636 baseEnd_1816636 := by
    simpa [prefixWord, tailWord_1816636, baseEnd_1816636] using wordTrace_append hprefix tailTrace_1816636
  have hstable : (prefixWord ++ tailWord_1816636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816636).length < 2 ^ (prefixWord ++ tailWord_1816636).sum := by decide
  have hdescent : baseEnd_1816636 < baseStart_1816636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816637 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_1816637 : Nat := 118140960795 + 1816637 * 2 ^ 59
def prefixEnd_1816637 : Nat := 4983230072969 + 3 ^ 40 * 1816637 * 2
def baseEnd_1816637 : Nat := 932807955741914133082945

theorem tailTrace_1816637 : CollatzResearch.WordTrace tailWord_1816637 prefixEnd_1816637 932807955741914133082945 := by
  unfold tailWord_1816637
  simp only [CollatzResearch.WordTrace]
  refine ⟨66258194719641880743896165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44172129813094587162597443 66258194719641880743896165)
  ·
    refine ⟨12423411509932852639480531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66258194719641880743896165 12423411509932852639480531)
    ·
      refine ⟨18635117264899278959220797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423411509932852639480531 18635117264899278959220797)
      ·
        refine ⟨6988168974337229609707799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18635117264899278959220797 6988168974337229609707799)
        ·
          refine ⟨10482253461505844414561699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988168974337229609707799 10482253461505844414561699)
          ·
            refine ⟨15723380192258766621842549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482253461505844414561699 15723380192258766621842549)
            ·
              refine ⟨1474066893024259370797739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15723380192258766621842549 1474066893024259370797739)
              ·
                refine ⟨2211100339536389056196609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474066893024259370797739 2211100339536389056196609)
                ·
                  refine ⟨1658325254652291792147457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2211100339536389056196609 1658325254652291792147457)
                  ·
                    refine ⟨1243743940989218844110593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1658325254652291792147457 1243743940989218844110593)
                    ·
                      refine ⟨932807955741914133082945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1243743940989218844110593 932807955741914133082945)
                      ·
                        rfl

theorem cell23_1816637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_1816637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816637 prefixEnd_1816637 := by exact prefixLift 1816637
  have htrace : WordTrace (prefixWord ++ tailWord_1816637) baseStart_1816637 baseEnd_1816637 := by
    simpa [prefixWord, tailWord_1816637, baseEnd_1816637] using wordTrace_append hprefix tailTrace_1816637
  have hstable : (prefixWord ++ tailWord_1816637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816637).length < 2 ^ (prefixWord ++ tailWord_1816637).sum := by decide
  have hdescent : baseEnd_1816637 < baseStart_1816637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816639 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 1, 7]
def baseStart_1816639 : Nat := 118140960795 + 1816639 * 2 ^ 59
def prefixEnd_1816639 : Nat := 4983230072969 + 3 ^ 40 * 1816639 * 2
def baseEnd_1816639 : Nat := 310936327567741041752645

theorem tailTrace_1816639 : CollatzResearch.WordTrace tailWord_1816639 prefixEnd_1816639 310936327567741041752645 := by
  unfold tailWord_1816639
  simp only [CollatzResearch.WordTrace]
  refine ⟨66258267665634635085468971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44172178443756423390312647 66258267665634635085468971)
  ·
    refine ⟨99387401498451952628203457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66258267665634635085468971 99387401498451952628203457)
    ·
      refine ⟨74540551123838964471152593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99387401498451952628203457 74540551123838964471152593)
      ·
        refine ⟨55905413342879223353364445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74540551123838964471152593 55905413342879223353364445)
        ·
          refine ⟨20964530003579708757511667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55905413342879223353364445 20964530003579708757511667)
          ·
            refine ⟨31446795005369563136267501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20964530003579708757511667 31446795005369563136267501)
            ·
              refine ⟨11792548127013586176100313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31446795005369563136267501 11792548127013586176100313)
              ·
                refine ⟨8844411095260189632075235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11792548127013586176100313 8844411095260189632075235)
                ·
                  refine ⟨13266616642890284448112853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8844411095260189632075235 13266616642890284448112853)
                  ·
                    refine ⟨310936327567741041752645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13266616642890284448112853 310936327567741041752645)
                    ·
                      rfl

theorem cell23_1816639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_1816639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816639 prefixEnd_1816639 := by exact prefixLift 1816639
  have htrace : WordTrace (prefixWord ++ tailWord_1816639) baseStart_1816639 baseEnd_1816639 := by
    simpa [prefixWord, tailWord_1816639, baseEnd_1816639] using wordTrace_append hprefix tailTrace_1816639
  have hstable : (prefixWord ++ tailWord_1816639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816639).length < 2 ^ (prefixWord ++ tailWord_1816639).sum := by decide
  have hdescent : baseEnd_1816639 < baseStart_1816639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816659 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 4]
def baseStart_1816659 : Nat := 118140960795 + 1816659 * 2 ^ 59
def prefixEnd_1816659 : Nat := 4983230072969 + 3 ^ 40 * 1816659 * 2
def baseEnd_1816659 : Nat := 932819252316313047007843

theorem tailTrace_1816659 : CollatzResearch.WordTrace tailWord_1816659 prefixEnd_1816659 932819252316313047007843 := by
  unfold tailWord_1816659
  simp only [CollatzResearch.WordTrace]
  refine ⟨66258997125562178501197031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44172664750374785667464687 66258997125562178501197031)
  ·
    refine ⟨99388495688343267751795547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66258997125562178501197031 99388495688343267751795547)
    ·
      refine ⟨149082743532514901627693321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99388495688343267751795547 149082743532514901627693321)
      ·
        refine ⟨111812057649386176220769991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149082743532514901627693321 111812057649386176220769991)
        ·
          refine ⟨167718086474079264331154987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111812057649386176220769991 167718086474079264331154987)
          ·
            refine ⟨251577129711118896496732481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167718086474079264331154987 251577129711118896496732481)
            ·
              refine ⟨188682847283339172372549361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251577129711118896496732481 188682847283339172372549361)
              ·
                refine ⟨141512135462504379279412021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188682847283339172372549361 141512135462504379279412021)
                ·
                  refine ⟨13266762699609785557444877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141512135462504379279412021 13266762699609785557444877)
                  ·
                    refine ⟨4975036012353669584041829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13266762699609785557444877 4975036012353669584041829)
                    ·
                      refine ⟨932819252316313047007843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4975036012353669584041829 932819252316313047007843)
                      ·
                        rfl

theorem cell23_1816659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_1816659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816659 prefixEnd_1816659 := by exact prefixLift 1816659
  have htrace : WordTrace (prefixWord ++ tailWord_1816659) baseStart_1816659 baseEnd_1816659 := by
    simpa [prefixWord, tailWord_1816659, baseEnd_1816659] using wordTrace_append hprefix tailTrace_1816659
  have hstable : (prefixWord ++ tailWord_1816659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816659).length < 2 ^ (prefixWord ++ tailWord_1816659).sum := by decide
  have hdescent : baseEnd_1816659 < baseStart_1816659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816676 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_1816676 : Nat := 118140960795 + 1816676 * 2 ^ 59
def prefixEnd_1816676 : Nat := 4983230072969 + 3 ^ 40 * 1816676 * 2
def baseEnd_1816676 : Nat := 932827981487439480495265

theorem tailTrace_1816676 : CollatzResearch.WordTrace tailWord_1816676 prefixEnd_1816676 932827981487439480495265 := by
  unfold tailWord_1816676
  simp only [CollatzResearch.WordTrace]
  refine ⟨33129808583250295202282941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44173078111000393603043921 33129808583250295202282941)
  ·
    refine ⟨12423678218718860700856103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33129808583250295202282941 12423678218718860700856103)
    ·
      refine ⟨18635517328078291051284155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423678218718860700856103 18635517328078291051284155)
      ·
        refine ⟨27953275992117436576926233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18635517328078291051284155 27953275992117436576926233)
        ·
          refine ⟨20964956994088077432694675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27953275992117436576926233 20964956994088077432694675)
          ·
            refine ⟨31447435491132116149042013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20964956994088077432694675 31447435491132116149042013)
            ·
              refine ⟨11792788309174543555890755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31447435491132116149042013 11792788309174543555890755)
              ·
                refine ⟨17689182463761815333836133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11792788309174543555890755 17689182463761815333836133)
                ·
                  refine ⟨3316721711955340375094275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17689182463761815333836133 3316721711955340375094275)
                  ·
                    refine ⟨4975082567933010562641413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3316721711955340375094275 4975082567933010562641413)
                    ·
                      refine ⟨932827981487439480495265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4975082567933010562641413 932827981487439480495265)
                      ·
                        rfl

theorem cell23_1816676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_1816676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816676 prefixEnd_1816676 := by exact prefixLift 1816676
  have htrace : WordTrace (prefixWord ++ tailWord_1816676) baseStart_1816676 baseEnd_1816676 := by
    simpa [prefixWord, tailWord_1816676, baseEnd_1816676] using wordTrace_append hprefix tailTrace_1816676
  have hstable : (prefixWord ++ tailWord_1816676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816676).length < 2 ^ (prefixWord ++ tailWord_1816676).sum := by decide
  have hdescent : baseEnd_1816676 < baseStart_1816676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816696 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_1816696 : Nat := 118140960795 + 1816696 * 2 ^ 59
def prefixEnd_1816696 : Nat := 4983230072969 + 3 ^ 40 * 1816696 * 2
def baseEnd_1816696 : Nat := 932838251100529402245173

theorem tailTrace_1816696 : CollatzResearch.WordTrace tailWord_1816696 prefixEnd_1816696 932838251100529402245173 := by
  unfold tailWord_1816696
  simp only [CollatzResearch.WordTrace]
  refine ⟨33130173313214066910146971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44173564417618755880195961 33130173313214066910146971)
  ·
    refine ⟨49695259969821100365220457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33130173313214066910146971 49695259969821100365220457)
    ·
      refine ⟨37271444977365825273915343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49695259969821100365220457 37271444977365825273915343)
      ·
        refine ⟨55907167466048737910873015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37271444977365825273915343 55907167466048737910873015)
        ·
          refine ⟨83860751199073106866309523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55907167466048737910873015 83860751199073106866309523)
          ·
            refine ⟨125791126798609660299464285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83860751199073106866309523 125791126798609660299464285)
            ·
              refine ⟨47171672549478622612299107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125791126798609660299464285 47171672549478622612299107)
              ·
                refine ⟨70757508824217933918448661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47171672549478622612299107 70757508824217933918448661)
                ·
                  refine ⟨3316758226135215652427281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70757508824217933918448661 3316758226135215652427281)
                  ·
                    refine ⟨2487568669601411739320461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3316758226135215652427281 2487568669601411739320461)
                    ·
                      refine ⟨932838251100529402245173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2487568669601411739320461 932838251100529402245173)
                      ·
                        rfl

theorem cell23_1816696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_1816696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816696 prefixEnd_1816696 := by exact prefixLift 1816696
  have htrace : WordTrace (prefixWord ++ tailWord_1816696) baseStart_1816696 baseEnd_1816696 := by
    simpa [prefixWord, tailWord_1816696, baseEnd_1816696] using wordTrace_append hprefix tailTrace_1816696
  have hstable : (prefixWord ++ tailWord_1816696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816696).length < 2 ^ (prefixWord ++ tailWord_1816696).sum := by decide
  have hdescent : baseEnd_1816696 < baseStart_1816696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816713 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 3]
def baseStart_1816713 : Nat := 118140960795 + 1816713 * 2 ^ 59
def prefixEnd_1816713 : Nat := 4983230072969 + 3 ^ 40 * 1816713 * 2
def baseEnd_1816713 : Nat := 932846980271655835732595

theorem tailTrace_1816713 : CollatzResearch.WordTrace tailWord_1816713 prefixEnd_1816713 932846980271655835732595 := by
  unfold tailWord_1816713
  simp only [CollatzResearch.WordTrace]
  refine ⟨66260966667366545723662793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44173977778244363815775195 66260966667366545723662793)
  ·
    refine ⟨49695725000524909292747095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66260966667366545723662793 49695725000524909292747095)
    ·
      refine ⟨74543587500787363939120643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49695725000524909292747095 74543587500787363939120643)
      ·
        refine ⟨111815381251181045908680965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74543587500787363939120643 111815381251181045908680965)
        ·
          refine ⟨20965383984596446107877681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111815381251181045908680965 20965383984596446107877681)
          ·
            refine ⟨15724037988447334580908261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20965383984596446107877681 15724037988447334580908261)
            ·
              refine ⟨2948257122833875233920299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15724037988447334580908261 2948257122833875233920299)
              ·
                refine ⟨4422385684250812850880449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948257122833875233920299 4422385684250812850880449)
                ·
                  refine ⟨3316789263188109638160337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4422385684250812850880449 3316789263188109638160337)
                  ·
                    refine ⟨2487591947391082228620253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3316789263188109638160337 2487591947391082228620253)
                    ·
                      refine ⟨932846980271655835732595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2487591947391082228620253 932846980271655835732595)
                      ·
                        rfl

theorem cell23_1816713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_1816713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816713 prefixEnd_1816713 := by exact prefixLift 1816713
  have htrace : WordTrace (prefixWord ++ tailWord_1816713) baseStart_1816713 baseEnd_1816713 := by
    simpa [prefixWord, tailWord_1816713, baseEnd_1816713] using wordTrace_append hprefix tailTrace_1816713
  have hstable : (prefixWord ++ tailWord_1816713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816713).length < 2 ^ (prefixWord ++ tailWord_1816713).sum := by decide
  have hdescent : baseEnd_1816713 < baseStart_1816713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816733 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 6]
def baseStart_1816733 : Nat := 118140960795 + 1816733 * 2 ^ 59
def prefixEnd_1816733 : Nat := 4983230072969 + 3 ^ 40 * 1816733 * 2
def baseEnd_1816733 : Nat := 103650805542749528609167

theorem tailTrace_1816733 : CollatzResearch.WordTrace tailWord_1816733 prefixEnd_1816733 103650805542749528609167 := by
  unfold tailWord_1816733
  simp only [CollatzResearch.WordTrace]
  refine ⟨66261696127294089139390853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44174464084862726092927235 66261696127294089139390853)
  ·
    refine ⟨12424068023867641713635785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66261696127294089139390853 12424068023867641713635785)
    ·
      refine ⟨9318051017900731285226839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12424068023867641713635785 9318051017900731285226839)
      ·
        refine ⟨13977076526851096927840259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318051017900731285226839 13977076526851096927840259)
        ·
          refine ⟨20965614790276645391760389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13977076526851096927840259 20965614790276645391760389)
          ·
            refine ⟨3931052773176871010955073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20965614790276645391760389 3931052773176871010955073)
            ·
              refine ⟨2948289579882653258216305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3931052773176871010955073 2948289579882653258216305)
              ·
                refine ⟨2211217184911989943662229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2948289579882653258216305 2211217184911989943662229)
                ·
                  refine ⟨103650805542749528609167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2211217184911989943662229 103650805542749528609167)
                  ·
                    rfl

theorem cell23_1816733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_1816733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816733 prefixEnd_1816733 := by exact prefixLift 1816733
  have htrace : WordTrace (prefixWord ++ tailWord_1816733) baseStart_1816733 baseEnd_1816733 := by
    simpa [prefixWord, tailWord_1816733, baseEnd_1816733] using wordTrace_append hprefix tailTrace_1816733
  have hstable : (prefixWord ++ tailWord_1816733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816733).length < 2 ^ (prefixWord ++ tailWord_1816733).sum := by decide
  have hdescent : baseEnd_1816733 < baseStart_1816733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816737 : List Nat := [1, 2, 3, 3, 1, 2, 4, 2, 1, 4]
def baseStart_1816737 : Nat := 118140960795 + 1816737 * 2 ^ 59
def prefixEnd_1816737 : Nat := 4983230072969 + 3 ^ 40 * 1816737 * 2
def baseEnd_1816737 : Nat := 310953101269121247277495

theorem tailTrace_1816737 : CollatzResearch.WordTrace tailWord_1816737 prefixEnd_1816737 310953101269121247277495 := by
  unfold tailWord_1816737
  simp only [CollatzResearch.WordTrace]
  refine ⟨66261842019279597822536465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44174561346186398548357643 66261842019279597822536465)
  ·
    refine ⟨49696381514459698366902349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66261842019279597822536465 49696381514459698366902349)
    ·
      refine ⟨18636143067922386887588381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49696381514459698366902349 18636143067922386887588381)
      ·
        refine ⟨6988553650470895082845643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18636143067922386887588381 6988553650470895082845643)
        ·
          refine ⟨10482830475706342624268465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988553650470895082845643 10482830475706342624268465)
          ·
            refine ⟨7862122856779756968201349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10482830475706342624268465 7862122856779756968201349)
            ·
              refine ⟨1474148035646204431537753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7862122856779756968201349 1474148035646204431537753)
              ·
                refine ⟨1105611026734653323653315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474148035646204431537753 1105611026734653323653315)
                ·
                  refine ⟨1658416540101979985479973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105611026734653323653315 1658416540101979985479973)
                  ·
                    refine ⟨310953101269121247277495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1658416540101979985479973 310953101269121247277495)
                    ·
                      rfl

theorem cell23_1816737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_1816737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816737 prefixEnd_1816737 := by exact prefixLift 1816737
  have htrace : WordTrace (prefixWord ++ tailWord_1816737) baseStart_1816737 baseEnd_1816737 := by
    simpa [prefixWord, tailWord_1816737, baseEnd_1816737] using wordTrace_append hprefix tailTrace_1816737
  have hstable : (prefixWord ++ tailWord_1816737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816737).length < 2 ^ (prefixWord ++ tailWord_1816737).sum := by decide
  have hdescent : baseEnd_1816737 < baseStart_1816737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816783 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 4]
def baseStart_1816783 : Nat := 118140960795 + 1816783 * 2 ^ 59
def prefixEnd_1816783 : Nat := 4983230072969 + 3 ^ 40 * 1816783 * 2
def baseEnd_1816783 : Nat := 932882923917470561857273

theorem tailTrace_1816783 : CollatzResearch.WordTrace tailWord_1816783 prefixEnd_1816783 932882923917470561857273 := by
  unfold tailWord_1816783
  simp only [CollatzResearch.WordTrace]
  refine ⟨66263519777112947678711003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44175679851408631785807335 66263519777112947678711003)
  ·
    refine ⟨99395279665669421518066505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66263519777112947678711003 99395279665669421518066505)
    ·
      refine ⟨74546459749252066138549879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99395279665669421518066505 74546459749252066138549879)
      ·
        refine ⟨111819689623878099207824819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74546459749252066138549879 111819689623878099207824819)
        ·
          refine ⟨167729534435817148811737229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111819689623878099207824819 167729534435817148811737229)
          ·
            refine ⟨62898575413431430804401461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167729534435817148811737229 62898575413431430804401461)
            ·
              refine ⟨5896741445009196637912637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62898575413431430804401461 5896741445009196637912637)
              ·
                refine ⟨2211278041878448739217239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5896741445009196637912637 2211278041878448739217239)
                ·
                  refine ⟨3316917062817673108825859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211278041878448739217239 3316917062817673108825859)
                  ·
                    refine ⟨4975375594226509663238789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3316917062817673108825859 4975375594226509663238789)
                    ·
                      refine ⟨932882923917470561857273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4975375594226509663238789 932882923917470561857273)
                      ·
                        rfl

theorem cell23_1816783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 4].length) (baseStart_1816783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816783 prefixEnd_1816783 := by exact prefixLift 1816783
  have htrace : WordTrace (prefixWord ++ tailWord_1816783) baseStart_1816783 baseEnd_1816783 := by
    simpa [prefixWord, tailWord_1816783, baseEnd_1816783] using wordTrace_append hprefix tailTrace_1816783
  have hstable : (prefixWord ++ tailWord_1816783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816783).length < 2 ^ (prefixWord ++ tailWord_1816783).sum := by decide
  have hdescent : baseEnd_1816783 < baseStart_1816783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816833 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_1816833 : Nat := 118140960795 + 1816833 * 2 ^ 59
def prefixEnd_1816833 : Nat := 4983230072969 + 3 ^ 40 * 1816833 * 2
def baseEnd_1816833 : Nat := 932908597950195366232043

theorem tailTrace_1816833 : CollatzResearch.WordTrace tailWord_1816833 prefixEnd_1816833 932908597950195366232043 := by
  unfold tailWord_1816833
  simp only [CollatzResearch.WordTrace]
  refine ⟨66265343426931806218031153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44176895617954537478687435 66265343426931806218031153)
  ·
    refine ⟨49699007570198854663523365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66265343426931806218031153 49699007570198854663523365)
    ·
      refine ⟨9318563919412285249410631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49699007570198854663523365 9318563919412285249410631)
      ·
        refine ⟨13977845879118427874115947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318563919412285249410631 13977845879118427874115947)
        ·
          refine ⟨20966768818677641811173921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13977845879118427874115947 20966768818677641811173921)
          ·
            refine ⟨15725076614008231358380441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20966768818677641811173921 15725076614008231358380441)
            ·
              refine ⟨11793807460506173518785331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15725076614008231358380441 11793807460506173518785331)
              ·
                refine ⟨17690711190759260278177997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11793807460506173518785331 17690711190759260278177997)
                ·
                  refine ⟨6634016696534722604316749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17690711190759260278177997 6634016696534722604316749)
                  ·
                    refine ⟨2487756261200520976618781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6634016696534722604316749 2487756261200520976618781)
                    ·
                      refine ⟨932908597950195366232043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2487756261200520976618781 932908597950195366232043)
                      ·
                        rfl

theorem cell23_1816833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_1816833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816833 prefixEnd_1816833 := by exact prefixLift 1816833
  have htrace : WordTrace (prefixWord ++ tailWord_1816833) baseStart_1816833 baseEnd_1816833 := by
    simpa [prefixWord, tailWord_1816833, baseEnd_1816833] using wordTrace_append hprefix tailTrace_1816833
  have hstable : (prefixWord ++ tailWord_1816833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816833).length < 2 ^ (prefixWord ++ tailWord_1816833).sum := by decide
  have hdescent : baseEnd_1816833 < baseStart_1816833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816860 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_1816860 : Nat := 118140960795 + 1816860 * 2 ^ 59
def prefixEnd_1816860 : Nat := 4983230072969 + 3 ^ 40 * 1816860 * 2
def baseEnd_1816860 : Nat := 932922461927866760594419

theorem tailTrace_1816860 : CollatzResearch.WordTrace tailWord_1816860 prefixEnd_1816860 932922461927866760594419 := by
  unfold tailWord_1816860
  simp only [CollatzResearch.WordTrace]
  refine ⟨33133164098916994914632017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44177552131889326552842689 33133164098916994914632017)
  ·
    refine ⟨24849873074187746185974013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33133164098916994914632017 24849873074187746185974013)
    ·
      refine ⟨9318702402820404819740255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24849873074187746185974013 9318702402820404819740255)
      ·
        refine ⟨13978053604230607229610383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318702402820404819740255 13978053604230607229610383)
        ·
          refine ⟨20967080406345910844415575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13978053604230607229610383 20967080406345910844415575)
          ·
            refine ⟨31450620609518866266623363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20967080406345910844415575 31450620609518866266623363)
            ·
              refine ⟨47175930914278299399935045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31450620609518866266623363 47175930914278299399935045)
              ·
                refine ⟨8845487046427181137487821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47175930914278299399935045 8845487046427181137487821)
                ·
                  refine ⟨3317057642410192926557933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8845487046427181137487821 3317057642410192926557933)
                  ·
                    refine ⟨1243896615903822347459225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3317057642410192926557933 1243896615903822347459225)
                    ·
                      refine ⟨932922461927866760594419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1243896615903822347459225 932922461927866760594419)
                      ·
                        rfl

theorem cell23_1816860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_1816860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816860 prefixEnd_1816860 := by exact prefixLift 1816860
  have htrace : WordTrace (prefixWord ++ tailWord_1816860) baseStart_1816860 baseEnd_1816860 := by
    simpa [prefixWord, tailWord_1816860, baseEnd_1816860] using wordTrace_append hprefix tailTrace_1816860
  have hstable : (prefixWord ++ tailWord_1816860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816860).length < 2 ^ (prefixWord ++ tailWord_1816860).sum := by decide
  have hdescent : baseEnd_1816860 < baseStart_1816860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816861 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1816861 : Nat := 118140960795 + 1816861 * 2 ^ 59
def prefixEnd_1816861 : Nat := 4983230072969 + 3 ^ 40 * 1816861 * 2
def baseEnd_1816861 : Nat := 310974325136173752227305

theorem tailTrace_1816861 : CollatzResearch.WordTrace tailWord_1816861 prefixEnd_1816861 310974325136173752227305 := by
  unfold tailWord_1816861
  simp only [CollatzResearch.WordTrace]
  refine ⟨66266364670830367000050437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44177576447220244666700291 66266364670830367000050437)
  ·
    refine ⟨12424943375780693812509457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66266364670830367000050437 12424943375780693812509457)
    ·
      refine ⟨9318707531835520359382093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12424943375780693812509457 9318707531835520359382093)
      ·
        refine ⟨3494515324438320134768285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9318707531835520359382093 3494515324438320134768285)
        ·
          refine ⟨1310443246664370050538107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3494515324438320134768285 1310443246664370050538107)
          ·
            refine ⟨1965664869996555075807161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310443246664370050538107 1965664869996555075807161)
            ·
              refine ⟨1474248652497416306855371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965664869996555075807161 1474248652497416306855371)
              ·
                refine ⟨2211372978746124460283057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474248652497416306855371 2211372978746124460283057)
                ·
                  refine ⟨1658529734059593345212293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2211372978746124460283057 1658529734059593345212293)
                  ·
                    refine ⟨310974325136173752227305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1658529734059593345212293 310974325136173752227305)
                    ·
                      rfl

theorem cell23_1816861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1816861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816861 prefixEnd_1816861 := by exact prefixLift 1816861
  have htrace : WordTrace (prefixWord ++ tailWord_1816861) baseStart_1816861 baseEnd_1816861 := by
    simpa [prefixWord, tailWord_1816861, baseEnd_1816861] using wordTrace_append hprefix tailTrace_1816861
  have hstable : (prefixWord ++ tailWord_1816861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816861).length < 2 ^ (prefixWord ++ tailWord_1816861).sum := by decide
  have hdescent : baseEnd_1816861 < baseStart_1816861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816873 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 10, 2]
def baseStart_1816873 : Nat := 118140960795 + 1816873 * 2 ^ 59
def prefixEnd_1816873 : Nat := 4983230072969 + 3 ^ 40 * 1816873 * 2
def baseEnd_1816873 : Nat := 932929137176375209731859

theorem tailTrace_1816873 : CollatzResearch.WordTrace tailWord_1816873 prefixEnd_1816873 932929137176375209731859 := by
  unfold tailWord_1816873
  simp only [CollatzResearch.WordTrace]
  refine ⟨66266802346786893049487273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44177868231191262032991515 66266802346786893049487273)
  ·
    refine ⟨49700101760090169787115455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66266802346786893049487273 49700101760090169787115455)
    ·
      refine ⟨74550152640135254680673183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49700101760090169787115455 74550152640135254680673183)
      ·
        refine ⟨111825228960202882021009775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74550152640135254680673183 111825228960202882021009775)
        ·
          refine ⟨167737843440304323031514663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111825228960202882021009775 167737843440304323031514663)
          ·
            refine ⟨251606765160456484547271995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167737843440304323031514663 251606765160456484547271995)
            ·
              refine ⟨377410147740684726820907993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251606765160456484547271995 377410147740684726820907993)
              ·
                refine ⟨283057610805513545115680995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377410147740684726820907993 283057610805513545115680995)
                ·
                  refine ⟨424586416208270317673521493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283057610805513545115680995 424586416208270317673521493)
                  ·
                    refine ⟨1243905516235166946309145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 424586416208270317673521493 1243905516235166946309145)
                    ·
                      refine ⟨932929137176375209731859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1243905516235166946309145 932929137176375209731859)
                      ·
                        rfl

theorem cell23_1816873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 10, 2].length) (baseStart_1816873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816873 prefixEnd_1816873 := by exact prefixLift 1816873
  have htrace : WordTrace (prefixWord ++ tailWord_1816873) baseStart_1816873 baseEnd_1816873 := by
    simpa [prefixWord, tailWord_1816873, baseEnd_1816873] using wordTrace_append hprefix tailTrace_1816873
  have hstable : (prefixWord ++ tailWord_1816873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816873).length < 2 ^ (prefixWord ++ tailWord_1816873).sum := by decide
  have hdescent : baseEnd_1816873 < baseStart_1816873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816890 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2]
def baseStart_1816890 : Nat := 118140960795 + 1816890 * 2 ^ 59
def prefixEnd_1816890 : Nat := 4983230072969 + 3 ^ 40 * 1816890 * 2
def baseEnd_1816890 : Nat := 932937866347501643219281

theorem tailTrace_1816890 : CollatzResearch.WordTrace tailWord_1816890 prefixEnd_1816890 932937866347501643219281 := by
  unfold tailWord_1816890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16566855596931326238214031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44178281591816869968570749 16566855596931326238214031)
  ·
    refine ⟨24850283395396989357321047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16566855596931326238214031 24850283395396989357321047)
    ·
      refine ⟨37275425093095484035981571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24850283395396989357321047 37275425093095484035981571)
      ·
        refine ⟨55913137639643226053972357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37275425093095484035981571 55913137639643226053972357)
        ·
          refine ⟨10483713307433104885119817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55913137639643226053972357 10483713307433104885119817)
          ·
            refine ⟨7862784980574828663839863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10483713307433104885119817 7862784980574828663839863)
            ·
              refine ⟨11794177470862242995759795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7862784980574828663839863 11794177470862242995759795)
              ·
                refine ⟨17691266206293364493639693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11794177470862242995759795 17691266206293364493639693)
                ·
                  refine ⟨6634224827360011685114885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17691266206293364493639693 6634224827360011685114885)
                  ·
                    refine ⟨1243917155130002190959041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6634224827360011685114885 1243917155130002190959041)
                    ·
                      refine ⟨932937866347501643219281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1243917155130002190959041 932937866347501643219281)
                      ·
                        rfl

theorem cell23_1816890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_1816890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816890 prefixEnd_1816890 := by exact prefixLift 1816890
  have htrace : WordTrace (prefixWord ++ tailWord_1816890) baseStart_1816890 baseEnd_1816890 := by
    simpa [prefixWord, tailWord_1816890, baseEnd_1816890] using wordTrace_append hprefix tailTrace_1816890
  have hstable : (prefixWord ++ tailWord_1816890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816890).length < 2 ^ (prefixWord ++ tailWord_1816890).sum := by decide
  have hdescent : baseEnd_1816890 < baseStart_1816890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816896 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 11]
def baseStart_1816896 : Nat := 118140960795 + 1816896 * 2 ^ 59
def prefixEnd_1816896 : Nat := 4983230072969 + 3 ^ 40 * 1816896 * 2
def baseEnd_1816896 : Nat := 103660105247936513304917

theorem tailTrace_1816896 : CollatzResearch.WordTrace tailWord_1816896 prefixEnd_1816896 103660105247936513304917 := by
  unfold tailWord_1816896
  simp only [CollatzResearch.WordTrace]
  refine ⟨33133820612851783988787271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44178427483802378651716361 33133820612851783988787271)
  ·
    refine ⟨49700730919277675983180907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33133820612851783988787271 49700730919277675983180907)
    ·
      refine ⟨74551096378916513974771361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49700730919277675983180907 74551096378916513974771361)
      ·
        refine ⟨55913322284187385481078521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74551096378916513974771361 55913322284187385481078521)
        ·
          refine ⟨41934991713140539110808891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55913322284187385481078521 41934991713140539110808891)
          ·
            refine ⟨62902487569710808666213337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41934991713140539110808891 62902487569710808666213337)
            ·
              refine ⟨47176865677283106499660003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62902487569710808666213337 47176865677283106499660003)
              ·
                refine ⟨70765298515924659749490005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47176865677283106499660003 70765298515924659749490005)
                ·
                  refine ⟨103660105247936513304917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 70765298515924659749490005 103660105247936513304917)
                  ·
                    rfl

theorem cell23_1816896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 11].length) (baseStart_1816896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816896 prefixEnd_1816896 := by exact prefixLift 1816896
  have htrace : WordTrace (prefixWord ++ tailWord_1816896) baseStart_1816896 baseEnd_1816896 := by
    simpa [prefixWord, tailWord_1816896, baseEnd_1816896] using wordTrace_append hprefix tailTrace_1816896
  have hstable : (prefixWord ++ tailWord_1816896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816896).length < 2 ^ (prefixWord ++ tailWord_1816896).sum := by decide
  have hdescent : baseEnd_1816896 < baseStart_1816896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816903 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1816903 : Nat := 118140960795 + 1816903 * 2 ^ 59
def prefixEnd_1816903 : Nat := 4983230072969 + 3 ^ 40 * 1816903 * 2
def baseEnd_1816903 : Nat := 932944541596010092356721

theorem tailTrace_1816903 : CollatzResearch.WordTrace tailWord_1816903 prefixEnd_1816903 932944541596010092356721 := by
  unfold tailWord_1816903
  simp only [CollatzResearch.WordTrace]
  refine ⟨66267896536678208173079363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44178597691118805448719575 66267896536678208173079363)
  ·
    refine ⟨99401844805017312259619045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66267896536678208173079363 99401844805017312259619045)
    ·
      refine ⟨18637845900940746048678571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99401844805017312259619045 18637845900940746048678571)
      ·
        refine ⟨27956768851411119073017857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18637845900940746048678571 27956768851411119073017857)
        ·
          refine ⟨20967576638558339304763393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27956768851411119073017857 20967576638558339304763393)
          ·
            refine ⟨15725682478918754478572545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20967576638558339304763393 15725682478918754478572545)
            ·
              refine ⟨11794261859189065858929409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15725682478918754478572545 11794261859189065858929409)
              ·
                refine ⟨8845696394391799394197057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11794261859189065858929409 8845696394391799394197057)
                ·
                  refine ⟨6634272295793849545647793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8845696394391799394197057 6634272295793849545647793)
                  ·
                    refine ⟨4975704221845387159235845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6634272295793849545647793 4975704221845387159235845)
                    ·
                      refine ⟨932944541596010092356721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4975704221845387159235845 932944541596010092356721)
                      ·
                        rfl

theorem cell23_1816903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1816903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816903 prefixEnd_1816903 := by exact prefixLift 1816903
  have htrace : WordTrace (prefixWord ++ tailWord_1816903) baseStart_1816903 baseEnd_1816903 := by
    simpa [prefixWord, tailWord_1816903, baseEnd_1816903] using wordTrace_append hprefix tailTrace_1816903
  have hstable : (prefixWord ++ tailWord_1816903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816903).length < 2 ^ (prefixWord ++ tailWord_1816903).sum := by decide
  have hdescent : baseEnd_1816903 < baseStart_1816903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816930 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1816930 : Nat := 118140960795 + 1816930 * 2 ^ 59
def prefixEnd_1816930 : Nat := 4983230072969 + 3 ^ 40 * 1816930 * 2
def baseEnd_1816930 : Nat := 103662045063742387413233

theorem tailTrace_1816930 : CollatzResearch.WordTrace tailWord_1816930 prefixEnd_1816930 103662045063742387413233 := by
  unfold tailWord_1816930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16567220326895097946078061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44179254205053594522874829 16567220326895097946078061)
  ·
    refine ⟨6212707622585661729779273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16567220326895097946078061 6212707622585661729779273)
    ·
      refine ⟨4659530716939246297334455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6212707622585661729779273 4659530716939246297334455)
      ·
        refine ⟨6989296075408869446001683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4659530716939246297334455 6989296075408869446001683)
        ·
          refine ⟨10483944113113304169002525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989296075408869446001683 10483944113113304169002525)
          ·
            refine ⟨3931479042417489063375947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10483944113113304169002525 3931479042417489063375947)
            ·
              refine ⟨5897218563626233595063921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931479042417489063375947 5897218563626233595063921)
              ·
                refine ⟨4422913922719675196297941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5897218563626233595063921 4422913922719675196297941)
                ·
                  refine ⟨103662045063742387413233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4422913922719675196297941 103662045063742387413233)
                  ·
                    rfl

theorem cell23_1816930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1816930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816930 prefixEnd_1816930 := by exact prefixLift 1816930
  have htrace : WordTrace (prefixWord ++ tailWord_1816930) baseStart_1816930 baseEnd_1816930 := by
    simpa [prefixWord, tailWord_1816930, baseEnd_1816930] using wordTrace_append hprefix tailTrace_1816930
  have hstable : (prefixWord ++ tailWord_1816930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816930).length < 2 ^ (prefixWord ++ tailWord_1816930).sum := by decide
  have hdescent : baseEnd_1816930 < baseStart_1816930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816943 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 2, 5]
def baseStart_1816943 : Nat := 118140960795 + 1816943 * 2 ^ 59
def prefixEnd_1816943 : Nat := 4983230072969 + 3 ^ 40 * 1816943 * 2
def baseEnd_1816943 : Nat := 310988360274063311952179

theorem tailTrace_1816943 : CollatzResearch.WordTrace tailWord_1816943 prefixEnd_1816943 310988360274063311952179 := by
  unfold tailWord_1816943
  simp only [CollatzResearch.WordTrace]
  refine ⟨66269355456533295004535483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44179570304355530003023655 66269355456533295004535483)
  ·
    refine ⟨99404033184799942506803225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66269355456533295004535483 99404033184799942506803225)
    ·
      refine ⟨74553024888599956880102419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99404033184799942506803225 74553024888599956880102419)
      ·
        refine ⟨111829537332899935320153629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74553024888599956880102419 111829537332899935320153629)
        ·
          refine ⟨41936076499837475745057611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111829537332899935320153629 41936076499837475745057611)
          ·
            refine ⟨62904114749756213617586417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41936076499837475745057611 62904114749756213617586417)
            ·
              refine ⟨47178086062317160213189813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62904114749756213617586417 47178086062317160213189813)
              ·
                refine ⟨4422945568342233769986545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47178086062317160213189813 4422945568342233769986545)
                ·
                  refine ⟨3317209176256675327489909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4422945568342233769986545 3317209176256675327489909)
                  ·
                    refine ⟨310988360274063311952179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3317209176256675327489909 310988360274063311952179)
                    ·
                      rfl

theorem cell23_1816943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_1816943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1816943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1816943 prefixEnd_1816943 := by exact prefixLift 1816943
  have htrace : WordTrace (prefixWord ++ tailWord_1816943) baseStart_1816943 baseEnd_1816943 := by
    simpa [prefixWord, tailWord_1816943, baseEnd_1816943] using wordTrace_append hprefix tailTrace_1816943
  have hstable : (prefixWord ++ tailWord_1816943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816943).length < 2 ^ (prefixWord ++ tailWord_1816943).sum := by decide
  have hdescent : baseEnd_1816943 < baseStart_1816943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817017 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1817017 : Nat := 118140960795 + 1817017 * 2 ^ 59
def prefixEnd_1817017 : Nat := 4983230072969 + 3 ^ 40 * 1817017 * 2
def baseEnd_1817017 : Nat := 933003078390622646331197

theorem tailTrace_1817017 : CollatzResearch.WordTrace tailWord_1817017 prefixEnd_1817017 933003078390622646331197 := by
  unfold tailWord_1817017
  simp only [CollatzResearch.WordTrace]
  refine ⟨66272054458265205642729305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44181369638843470428486203 66272054458265205642729305)
  ·
    refine ⟨49704040843698904232046979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66272054458265205642729305 49704040843698904232046979)
    ·
      refine ⟨74556061265548356348070469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49704040843698904232046979 74556061265548356348070469)
      ·
        refine ⟨13979261487290316815263213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74556061265548356348070469 13979261487290316815263213)
        ·
          refine ⟨5242223057733868805723705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13979261487290316815263213 5242223057733868805723705)
          ·
            refine ⟨3931667293300401604292779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5242223057733868805723705 3931667293300401604292779)
            ·
              refine ⟨5897500939950602406439169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931667293300401604292779 5897500939950602406439169)
              ·
                refine ⟨4423125704962951804829377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5897500939950602406439169 4423125704962951804829377)
                ·
                  refine ⟨3317344278722213853622033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4423125704962951804829377 3317344278722213853622033)
                  ·
                    refine ⟨2488008209041660390216525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3317344278722213853622033 2488008209041660390216525)
                    ·
                      refine ⟨933003078390622646331197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2488008209041660390216525 933003078390622646331197)
                      ·
                        rfl

theorem cell23_1817017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1817017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817017 prefixEnd_1817017 := by exact prefixLift 1817017
  have htrace : WordTrace (prefixWord ++ tailWord_1817017) baseStart_1817017 baseEnd_1817017 := by
    simpa [prefixWord, tailWord_1817017, baseEnd_1817017] using wordTrace_append hprefix tailTrace_1817017
  have hstable : (prefixWord ++ tailWord_1817017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817017).length < 2 ^ (prefixWord ++ tailWord_1817017).sum := by decide
  have hdescent : baseEnd_1817017 < baseStart_1817017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817020 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 8]
def baseStart_1817020 : Nat := 118140960795 + 1817020 * 2 ^ 59
def prefixEnd_1817020 : Nat := 4983230072969 + 3 ^ 40 * 1817020 * 2
def baseEnd_1817020 : Nat := 103667179870287348288187

theorem tailTrace_1817020 : CollatzResearch.WordTrace tailWord_1817020 prefixEnd_1817020 103667179870287348288187 := by
  unfold tailWord_1817020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33136081938627168577544257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44181442584836224770059009 33136081938627168577544257)
  ·
    refine ⟨24852061453970376433158193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33136081938627168577544257 24852061453970376433158193)
    ·
      refine ⟨18639046090477782324868645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24852061453970376433158193 18639046090477782324868645)
      ·
        refine ⟨3494821141964584185912871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18639046090477782324868645 3494821141964584185912871)
        ·
          refine ⟨5242231712946876278869307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494821141964584185912871 5242231712946876278869307)
          ·
            refine ⟨7863347569420314418303961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5242231712946876278869307 7863347569420314418303961)
            ·
              refine ⟨5897510677065235813727971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7863347569420314418303961 5897510677065235813727971)
              ·
                refine ⟨8846266015597853720591957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897510677065235813727971 8846266015597853720591957)
                ·
                  refine ⟨103667179870287348288187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8846266015597853720591957 103667179870287348288187)
                  ·
                    rfl

theorem cell23_1817020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_1817020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817020 prefixEnd_1817020 := by exact prefixLift 1817020
  have htrace : WordTrace (prefixWord ++ tailWord_1817020) baseStart_1817020 baseEnd_1817020 := by
    simpa [prefixWord, tailWord_1817020, baseEnd_1817020] using wordTrace_append hprefix tailTrace_1817020
  have hstable : (prefixWord ++ tailWord_1817020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817020).length < 2 ^ (prefixWord ++ tailWord_1817020).sum := by decide
  have hdescent : baseEnd_1817020 < baseStart_1817020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817050 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_1817050 : Nat := 118140960795 + 1817050 * 2 ^ 59
def prefixEnd_1817050 : Nat := 4983230072969 + 3 ^ 40 * 1817050 * 2
def baseEnd_1817050 : Nat := 311006674417407005739515

theorem tailTrace_1817050 : CollatzResearch.WordTrace tailWord_1817050 prefixEnd_1817050 311006674417407005739515 := by
  unfold tailWord_1817050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16568314516786413069670151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44182172044763768185787069 16568314516786413069670151)
  ·
    refine ⟨24852471775179619604505227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16568314516786413069670151 24852471775179619604505227)
    ·
      refine ⟨37278707662769429406757841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24852471775179619604505227 37278707662769429406757841)
      ·
        refine ⟨27959030747077072055068381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37278707662769429406757841 27959030747077072055068381)
        ·
          refine ⟨10484636530153902020650643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27959030747077072055068381 10484636530153902020650643)
          ·
            refine ⟨15726954795230853030975965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484636530153902020650643 15726954795230853030975965)
            ·
              refine ⟨5897608048211569886615987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15726954795230853030975965 5897608048211569886615987)
              ·
                refine ⟨8846412072317354829923981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897608048211569886615987 8846412072317354829923981)
                ·
                  refine ⟨3317404527119008061221493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8846412072317354829923981 3317404527119008061221493)
                  ·
                    refine ⟨311006674417407005739515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3317404527119008061221493 311006674417407005739515)
                    ·
                      rfl

theorem cell23_1817050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_1817050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817050 prefixEnd_1817050 := by exact prefixLift 1817050
  have htrace : WordTrace (prefixWord ++ tailWord_1817050) baseStart_1817050 baseEnd_1817050 := by
    simpa [prefixWord, tailWord_1817050, baseEnd_1817050] using wordTrace_append hprefix tailTrace_1817050
  have hstable : (prefixWord ++ tailWord_1817050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817050).length < 2 ^ (prefixWord ++ tailWord_1817050).sum := by decide
  have hdescent : baseEnd_1817050 < baseStart_1817050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817067 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 1, 5]
def baseStart_1817067 : Nat := 118140960795 + 1817067 * 2 ^ 59
def prefixEnd_1817067 : Nat := 4983230072969 + 3 ^ 40 * 1817067 * 2
def baseEnd_1817067 : Nat := 311009584141115816901989

theorem tailTrace_1817067 : CollatzResearch.WordTrace tailWord_1817067 prefixEnd_1817067 311009584141115816901989 := by
  unfold tailWord_1817067
  simp only [CollatzResearch.WordTrace]
  refine ⟨66273878108084064182049455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44182585405389376121366303 66273878108084064182049455)
  ·
    refine ⟨99410817162126096273074183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66273878108084064182049455 99410817162126096273074183)
    ·
      refine ⟨149116225743189144409611275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99410817162126096273074183 149116225743189144409611275)
      ·
        refine ⟨223674338614783716614416913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149116225743189144409611275 223674338614783716614416913)
        ·
          refine ⟨167755753961087787460812685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223674338614783716614416913 167755753961087787460812685)
          ·
            refine ⟨62908407735407920297804757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167755753961087787460812685 62908407735407920297804757)
            ·
              refine ⟨1474415806298623131979799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62908407735407920297804757 1474415806298623131979799)
              ·
                refine ⟨2211623709447934697969699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474415806298623131979799 2211623709447934697969699)
                ·
                  refine ⟨3317435564171902046954549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211623709447934697969699 3317435564171902046954549)
                  ·
                    refine ⟨311009584141115816901989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3317435564171902046954549 311009584141115816901989)
                    ·
                      rfl

theorem cell23_1817067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 5].length) (baseStart_1817067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817067 prefixEnd_1817067 := by exact prefixLift 1817067
  have htrace : WordTrace (prefixWord ++ tailWord_1817067) baseStart_1817067 baseEnd_1817067 := by
    simpa [prefixWord, tailWord_1817067, baseEnd_1817067] using wordTrace_append hprefix tailTrace_1817067
  have hstable : (prefixWord ++ tailWord_1817067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817067).length < 2 ^ (prefixWord ++ tailWord_1817067).sum := by decide
  have hdescent : baseEnd_1817067 < baseStart_1817067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817081 : List Nat := [1, 2, 1, 3, 1, 2, 6, 2, 1, 1, 3]
def baseStart_1817081 : Nat := 118140960795 + 1817081 * 2 ^ 59
def prefixEnd_1817081 : Nat := 4983230072969 + 3 ^ 40 * 1817081 * 2
def baseEnd_1817081 : Nat := 933035941152510395930903

theorem tailTrace_1817081 : CollatzResearch.WordTrace tailWord_1817081 prefixEnd_1817081 933035941152510395930903 := by
  unfold tailWord_1817081
  simp only [CollatzResearch.WordTrace]
  refine ⟨66274388730033344573059097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44182925820022229715372731 66274388730033344573059097)
  ·
    refine ⟨49705791547525008429794323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66274388730033344573059097 49705791547525008429794323)
    ·
      refine ⟨74558687321287512644691485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49705791547525008429794323 74558687321287512644691485)
      ·
        refine ⟨27959507745482817241759307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74558687321287512644691485 27959507745482817241759307)
        ·
          refine ⟨41939261618224225862638961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27959507745482817241759307 41939261618224225862638961)
          ·
            refine ⟨31454446213668169396979221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41939261618224225862638961 31454446213668169396979221)
            ·
              refine ⟨1474427166265695440483401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31454446213668169396979221 1474427166265695440483401)
              ·
                refine ⟨1105820374699271580362551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474427166265695440483401 1105820374699271580362551)
                ·
                  refine ⟨1658730562048907370543827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105820374699271580362551 1658730562048907370543827)
                  ·
                    refine ⟨2488095843073361055815741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1658730562048907370543827 2488095843073361055815741)
                    ·
                      refine ⟨933035941152510395930903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2488095843073361055815741 933035941152510395930903)
                      ·
                        rfl

theorem cell23_1817081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_1817081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817081 prefixEnd_1817081 := by exact prefixLift 1817081
  have htrace : WordTrace (prefixWord ++ tailWord_1817081) baseStart_1817081 baseEnd_1817081 := by
    simpa [prefixWord, tailWord_1817081, baseEnd_1817081] using wordTrace_append hprefix tailTrace_1817081
  have hstable : (prefixWord ++ tailWord_1817081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817081).length < 2 ^ (prefixWord ++ tailWord_1817081).sum := by decide
  have hdescent : baseEnd_1817081 < baseStart_1817081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817107 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 3]
def baseStart_1817107 : Nat := 118140960795 + 1817107 * 2 ^ 59
def prefixEnd_1817107 : Nat := 4983230072969 + 3 ^ 40 * 1817107 * 2
def baseEnd_1817107 : Nat := 933049291649527294205783

theorem tailTrace_1817107 : CollatzResearch.WordTrace tailWord_1817107 prefixEnd_1817107 933049291649527294205783 := by
  unfold tailWord_1817107
  simp only [CollatzResearch.WordTrace]
  refine ⟨66275337027939151013505575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44183558018626100675670383 66275337027939151013505575)
  ·
    refine ⟨99413005541908726520258363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66275337027939151013505575 99413005541908726520258363)
    ·
      refine ⟨149119508312863089780387545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99413005541908726520258363 149119508312863089780387545)
      ·
        refine ⟨111839631234647317335290659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149119508312863089780387545 111839631234647317335290659)
        ·
          refine ⟨167759446851970976002935989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111839631234647317335290659 167759446851970976002935989)
          ·
            refine ⟨15727448142372279000275249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167759446851970976002935989 15727448142372279000275249)
            ·
              refine ⟨11795586106779209250206437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15727448142372279000275249 11795586106779209250206437)
              ·
                refine ⟨2211672395021101734413707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11795586106779209250206437 2211672395021101734413707)
                ·
                  refine ⟨3317508592531652601620561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211672395021101734413707 3317508592531652601620561)
                  ·
                    refine ⟨2488131444398739451215421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3317508592531652601620561 2488131444398739451215421)
                    ·
                      refine ⟨933049291649527294205783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2488131444398739451215421 933049291649527294205783)
                      ·
                        rfl

theorem cell23_1817107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 3].length) (baseStart_1817107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817107 prefixEnd_1817107 := by exact prefixLift 1817107
  have htrace : WordTrace (prefixWord ++ tailWord_1817107) baseStart_1817107 baseEnd_1817107 := by
    simpa [prefixWord, tailWord_1817107, baseEnd_1817107] using wordTrace_append hprefix tailTrace_1817107
  have hstable : (prefixWord ++ tailWord_1817107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817107).length < 2 ^ (prefixWord ++ tailWord_1817107).sum := by decide
  have hdescent : baseEnd_1817107 < baseStart_1817107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817108 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_1817108 : Nat := 118140960795 + 1817108 * 2 ^ 59
def prefixEnd_1817108 : Nat := 4983230072969 + 3 ^ 40 * 1817108 * 2
def baseEnd_1817108 : Nat := 933049805130181790293279

theorem tailTrace_1817108 : CollatzResearch.WordTrace tailWord_1817108 prefixEnd_1817108 933049805130181790293279 := by
  unfold tailWord_1817108
  simp only [CollatzResearch.WordTrace]
  refine ⟨33137686750467764092145989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44183582333957018789527985 33137686750467764092145989)
  ·
    refine ⟨6213316265712705767277373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33137686750467764092145989 6213316265712705767277373)
    ·
      refine ⟨2329993599642264662729015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6213316265712705767277373 2329993599642264662729015)
      ·
        refine ⟨3494990399463396994093523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2329993599642264662729015 3494990399463396994093523)
        ·
          refine ⟨5242485599195095491140285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494990399463396994093523 5242485599195095491140285)
          ·
            refine ⟨1965932099698160809177607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5242485599195095491140285 1965932099698160809177607)
            ·
              refine ⟨2948898149547241213766411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965932099698160809177607 2948898149547241213766411)
              ·
                refine ⟨4423347224320861820649617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948898149547241213766411 4423347224320861820649617)
                ·
                  refine ⟨3317510418240646365487213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4423347224320861820649617 3317510418240646365487213)
                  ·
                    refine ⟨1244066406840242387057705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3317510418240646365487213 1244066406840242387057705)
                    ·
                      refine ⟨933049805130181790293279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244066406840242387057705 933049805130181790293279)
                      ·
                        rfl

theorem cell23_1817108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_1817108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817108 prefixEnd_1817108 := by exact prefixLift 1817108
  have htrace : WordTrace (prefixWord ++ tailWord_1817108) baseStart_1817108 baseEnd_1817108 := by
    simpa [prefixWord, tailWord_1817108, baseEnd_1817108] using wordTrace_append hprefix tailTrace_1817108
  have hstable : (prefixWord ++ tailWord_1817108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817108).length < 2 ^ (prefixWord ++ tailWord_1817108).sum := by decide
  have hdescent : baseEnd_1817108 < baseStart_1817108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817117 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1817117 : Nat := 118140960795 + 1817117 * 2 ^ 59
def prefixEnd_1817117 : Nat := 4983230072969 + 3 ^ 40 * 1817117 * 2
def baseEnd_1817117 : Nat := 933054426456072255080737

theorem tailTrace_1817117 : CollatzResearch.WordTrace tailWord_1817117 prefixEnd_1817117 933054426456072255080737 := by
  unfold tailWord_1817117
  simp only [CollatzResearch.WordTrace]
  refine ⟨66275701757902922721369605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44183801171935281814246403 66275701757902922721369605)
  ·
    refine ⟨12426694079606798010256801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66275701757902922721369605 12426694079606798010256801)
    ·
      refine ⟨9320020559705098507692601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12426694079606798010256801 9320020559705098507692601)
      ·
        refine ⟨6990015419778823880769451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9320020559705098507692601 6990015419778823880769451)
        ·
          refine ⟨10485023129668235821154177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6990015419778823880769451 10485023129668235821154177)
          ·
            refine ⟨7863767347251176865865633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10485023129668235821154177 7863767347251176865865633)
            ·
              refine ⟨5897825510438382649399225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7863767347251176865865633 5897825510438382649399225)
              ·
                refine ⟨4423369132828786987049419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5897825510438382649399225 4423369132828786987049419)
                ·
                  refine ⟨6635053699243180480574129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423369132828786987049419 6635053699243180480574129)
                  ·
                    refine ⟨4976290274432385360430597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6635053699243180480574129 4976290274432385360430597)
                    ·
                      refine ⟨933054426456072255080737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4976290274432385360430597 933054426456072255080737)
                      ·
                        rfl

theorem cell23_1817117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1817117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817117 prefixEnd_1817117 := by exact prefixLift 1817117
  have htrace : WordTrace (prefixWord ++ tailWord_1817117) baseStart_1817117 baseEnd_1817117 := by
    simpa [prefixWord, tailWord_1817117, baseEnd_1817117] using wordTrace_append hprefix tailTrace_1817117
  have hstable : (prefixWord ++ tailWord_1817117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817117).length < 2 ^ (prefixWord ++ tailWord_1817117).sum := by decide
  have hdescent : baseEnd_1817117 < baseStart_1817117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817158 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1817158 : Nat := 118140960795 + 1817158 * 2 ^ 59
def prefixEnd_1817158 : Nat := 4983230072969 + 3 ^ 40 * 1817158 * 2
def baseEnd_1817158 : Nat := 933075479162906594668049

theorem tailTrace_1817158 : CollatzResearch.WordTrace tailWord_1817158 prefixEnd_1817158 933075479162906594668049 := by
  unfold tailWord_1817158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071162410961074585112879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44184798100502924482408085 2071162410961074585112879)
  ·
    refine ⟨3106743616441611877669319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2071162410961074585112879 3106743616441611877669319)
    ·
      refine ⟨4660115424662417816503979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106743616441611877669319 4660115424662417816503979)
      ·
        refine ⟨6990173136993626724755969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660115424662417816503979 6990173136993626724755969)
        ·
          refine ⟨5242629852745220043566977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6990173136993626724755969 5242629852745220043566977)
          ·
            refine ⟨3931972389558915032675233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5242629852745220043566977 3931972389558915032675233)
            ·
              refine ⟨2948979292169186274506425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3931972389558915032675233 2948979292169186274506425)
              ·
                refine ⟨2211734469126889705879819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2948979292169186274506425 2211734469126889705879819)
                ·
                  refine ⟨3317601703690334558819729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211734469126889705879819 3317601703690334558819729)
                  ·
                    refine ⟨2488201277767750919114797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3317601703690334558819729 2488201277767750919114797)
                    ·
                      refine ⟨933075479162906594668049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2488201277767750919114797 933075479162906594668049)
                      ·
                        rfl

theorem cell23_1817158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1817158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817158 prefixEnd_1817158 := by exact prefixLift 1817158
  have htrace : WordTrace (prefixWord ++ tailWord_1817158) baseStart_1817158 baseEnd_1817158 := by
    simpa [prefixWord, tailWord_1817158, baseEnd_1817158] using wordTrace_append hprefix tailTrace_1817158
  have hstable : (prefixWord ++ tailWord_1817158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817158).length < 2 ^ (prefixWord ++ tailWord_1817158).sum := by decide
  have hdescent : baseEnd_1817158 < baseStart_1817158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817160 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1817160 : Nat := 118140960795 + 1817160 * 2 ^ 59
def prefixEnd_1817160 : Nat := 4983230072969 + 3 ^ 40 * 1817160 * 2
def baseEnd_1817160 : Nat := 933076506124215586843039

theorem tailTrace_1817160 : CollatzResearch.WordTrace tailWord_1817160 prefixEnd_1817160 933076506124215586843039 := by
  unfold tailWord_1817160
  simp only [CollatzResearch.WordTrace]
  refine ⟨33138635048373570532592467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44184846731164760710123289 33138635048373570532592467)
  ·
    refine ⟨49707952572560355798888701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33138635048373570532592467 49707952572560355798888701)
    ·
      refine ⟨18640482214710133424583263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49707952572560355798888701 18640482214710133424583263)
      ·
        refine ⟨27960723322065200136874895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18640482214710133424583263 27960723322065200136874895)
        ·
          refine ⟨41941084983097800205312343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27960723322065200136874895 41941084983097800205312343)
          ·
            refine ⟨62911627474646700307968515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41941084983097800205312343 62911627474646700307968515)
            ·
              refine ⟨94367441211970050461952773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62911627474646700307968515 94367441211970050461952773)
              ·
                refine ⟨17693895227244384461616145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94367441211970050461952773 17693895227244384461616145)
                ·
                  refine ⟨13270421420433288346212109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17693895227244384461616145 13270421420433288346212109)
                  ·
                    refine ⟨4976408032662483129829541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13270421420433288346212109 4976408032662483129829541)
                    ·
                      refine ⟨933076506124215586843039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4976408032662483129829541 933076506124215586843039)
                      ·
                        rfl

theorem cell23_1817160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1817160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817160 prefixEnd_1817160 := by exact prefixLift 1817160
  have htrace : WordTrace (prefixWord ++ tailWord_1817160) baseStart_1817160 baseEnd_1817160 := by
    simpa [prefixWord, tailWord_1817160, baseEnd_1817160] using wordTrace_append hprefix tailTrace_1817160
  have hstable : (prefixWord ++ tailWord_1817160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817160).length < 2 ^ (prefixWord ++ tailWord_1817160).sum := by decide
  have hdescent : baseEnd_1817160 < baseStart_1817160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817205 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1817205 : Nat := 118140960795 + 1817205 * 2 ^ 59
def prefixEnd_1817205 : Nat := 4983230072969 + 3 ^ 40 * 1817205 * 2
def baseEnd_1817205 : Nat := 933099612753667910780333

theorem tailTrace_1817205 : CollatzResearch.WordTrace tailWord_1817205 prefixEnd_1817205 933099612753667910780333 := by
  unfold tailWord_1817205
  simp only [CollatzResearch.WordTrace]
  refine ⟨66278911381584113750573069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44185940921056075833715379 66278911381584113750573069)
  ·
    refine ⟨24854591768094042656464901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66278911381584113750573069 24854591768094042656464901)
    ·
      refine ⟨4660235956517632998087169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24854591768094042656464901 4660235956517632998087169)
      ·
        refine ⟨3495176967388224748565377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4660235956517632998087169 3495176967388224748565377)
        ·
          refine ⟨2621382725541168561424033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495176967388224748565377 2621382725541168561424033)
          ·
            refine ⟨1966037044155876421068025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2621382725541168561424033 1966037044155876421068025)
            ·
              refine ⟨1474527783116907315801019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966037044155876421068025 1474527783116907315801019)
              ·
                refine ⟨2211791674675360973701529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474527783116907315801019 2211791674675360973701529)
                ·
                  refine ⟨1658843756006520730276147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2211791674675360973701529 1658843756006520730276147)
                  ·
                    refine ⟨2488265634009781095414221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1658843756006520730276147 2488265634009781095414221)
                    ·
                      refine ⟨933099612753667910780333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2488265634009781095414221 933099612753667910780333)
                      ·
                        rfl

theorem cell23_1817205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1817205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817205 prefixEnd_1817205 := by exact prefixLift 1817205
  have htrace : WordTrace (prefixWord ++ tailWord_1817205) baseStart_1817205 baseEnd_1817205 := by
    simpa [prefixWord, tailWord_1817205, baseEnd_1817205] using wordTrace_append hprefix tailTrace_1817205
  have hstable : (prefixWord ++ tailWord_1817205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817205).length < 2 ^ (prefixWord ++ tailWord_1817205).sum := by decide
  have hdescent : baseEnd_1817205 < baseStart_1817205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817281 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1817281 : Nat := 118140960795 + 1817281 * 2 ^ 59
def prefixEnd_1817281 : Nat := 4983230072969 + 3 ^ 40 * 1817281 * 2
def baseEnd_1817281 : Nat := 311046212427803204476661

theorem tailTrace_1817281 : CollatzResearch.WordTrace tailWord_1817281 prefixEnd_1817281 311046212427803204476661 := by
  unfold tailWord_1817281
  simp only [CollatzResearch.WordTrace]
  refine ⟨66281683329308778730339697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44187788886205852486893131 66281683329308778730339697)
  ·
    refine ⟨49711262496981584047754773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66281683329308778730339697 49711262496981584047754773)
    ·
      refine ⟨2330215429546011752238505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49711262496981584047754773 2330215429546011752238505)
      ·
        refine ⟨1747661572159508814178879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2330215429546011752238505 1747661572159508814178879)
        ·
          refine ⟨2621492358239263221268319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747661572159508814178879 2621492358239263221268319)
          ·
            refine ⟨3932238537358894831902479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621492358239263221268319 3932238537358894831902479)
            ·
              refine ⟨5898357806038342247853719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932238537358894831902479 5898357806038342247853719)
              ·
                refine ⟨8847536709057513371780579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898357806038342247853719 8847536709057513371780579)
                ·
                  refine ⟨13271305063586270057670869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8847536709057513371780579 13271305063586270057670869)
                  ·
                    refine ⟨311046212427803204476661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13271305063586270057670869 311046212427803204476661)
                    ·
                      rfl

theorem cell23_1817281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1817281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817281 prefixEnd_1817281 := by exact prefixLift 1817281
  have htrace : WordTrace (prefixWord ++ tailWord_1817281) baseStart_1817281 baseEnd_1817281 := by
    simpa [prefixWord, tailWord_1817281, baseEnd_1817281] using wordTrace_append hprefix tailTrace_1817281
  have hstable : (prefixWord ++ tailWord_1817281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817281).length < 2 ^ (prefixWord ++ tailWord_1817281).sum := by decide
  have hdescent : baseEnd_1817281 < baseStart_1817281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817284 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1817284 : Nat := 118140960795 + 1817284 * 2 ^ 59
def prefixEnd_1817284 : Nat := 4983230072969 + 3 ^ 40 * 1817284 * 2
def baseEnd_1817284 : Nat := 933140177725373101692469

theorem tailTrace_1817284 : CollatzResearch.WordTrace tailWord_1817284 prefixEnd_1817284 933140177725373101692469 := by
  unfold tailWord_1817284
  simp only [CollatzResearch.WordTrace]
  refine ⟨33140896374148955121349453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44187861832198606828465937 33140896374148955121349453)
  ·
    refine ⟨12427836140305858170506045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33140896374148955121349453 12427836140305858170506045)
    ·
      refine ⟨4660438552614696813939767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12427836140305858170506045 4660438552614696813939767)
      ·
        refine ⟨6990657828922045220909651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660438552614696813939767 6990657828922045220909651)
        ·
          refine ⟨10485986743383067831364477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6990657828922045220909651 10485986743383067831364477)
          ·
            refine ⟨3932245028768650436761679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10485986743383067831364477 3932245028768650436761679)
            ·
              refine ⟨5898367543152975655142519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932245028768650436761679 5898367543152975655142519)
              ·
                refine ⟨8847551314729463482713779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898367543152975655142519 8847551314729463482713779)
                ·
                  refine ⟨13271326972094195224070669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8847551314729463482713779 13271326972094195224070669)
                  ·
                    refine ⟨4976747614535323209026501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13271326972094195224070669 4976747614535323209026501)
                    ·
                      refine ⟨933140177725373101692469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4976747614535323209026501 933140177725373101692469)
                      ·
                        rfl

theorem cell23_1817284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1817284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817284 prefixEnd_1817284 := by exact prefixLift 1817284
  have htrace : WordTrace (prefixWord ++ tailWord_1817284) baseStart_1817284 baseEnd_1817284 := by
    simpa [prefixWord, tailWord_1817284, baseEnd_1817284] using wordTrace_append hprefix tailTrace_1817284
  have hstable : (prefixWord ++ tailWord_1817284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817284).length < 2 ^ (prefixWord ++ tailWord_1817284).sum := by decide
  have hdescent : baseEnd_1817284 < baseStart_1817284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817311 : List Nat := [1, 1, 2, 3, 2, 3, 2, 4, 1, 4]
def baseStart_1817311 : Nat := 118140960795 + 1817311 * 2 ^ 59
def prefixEnd_1817311 : Nat := 4983230072969 + 3 ^ 40 * 1817311 * 2
def baseEnd_1817311 : Nat := 311051347234348165351615

theorem tailTrace_1817311 : CollatzResearch.WordTrace tailWord_1817311 prefixEnd_1817311 311051347234348165351615 := by
  unfold tailWord_1817311
  simp only [CollatzResearch.WordTrace]
  refine ⟨66282777519200093853931787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44188518346133395902621191 66282777519200093853931787)
  ·
    refine ⟨99424166278800140780897681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66282777519200093853931787 99424166278800140780897681)
    ·
      refine ⟨74568124709100105585673261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99424166278800140780897681 74568124709100105585673261)
      ·
        refine ⟨27963046765912539594627473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74568124709100105585673261 27963046765912539594627473)
        ·
          refine ⟨20972285074434404695970605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27963046765912539594627473 20972285074434404695970605)
          ·
            refine ⟨7864606902912901760988977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20972285074434404695970605 7864606902912901760988977)
            ·
              refine ⟨5898455177184676320741733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7864606902912901760988977 5898455177184676320741733)
              ·
                refine ⟨1105960345722126810139075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5898455177184676320741733 1105960345722126810139075)
                ·
                  refine ⟨1658940518583190215208613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105960345722126810139075 1658940518583190215208613)
                  ·
                    refine ⟨311051347234348165351615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1658940518583190215208613 311051347234348165351615)
                    ·
                      rfl

theorem cell23_1817311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 4].length) (baseStart_1817311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817311 prefixEnd_1817311 := by exact prefixLift 1817311
  have htrace : WordTrace (prefixWord ++ tailWord_1817311) baseStart_1817311 baseEnd_1817311 := by
    simpa [prefixWord, tailWord_1817311, baseEnd_1817311] using wordTrace_append hprefix tailTrace_1817311
  have hstable : (prefixWord ++ tailWord_1817311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817311).length < 2 ^ (prefixWord ++ tailWord_1817311).sum := by decide
  have hdescent : baseEnd_1817311 < baseStart_1817311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817334 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1817334 : Nat := 118140960795 + 1817334 * 2 ^ 59
def prefixEnd_1817334 : Nat := 4983230072969 + 3 ^ 40 * 1817334 * 2
def baseEnd_1817334 : Nat := 933165851758097906067239

theorem tailTrace_1817334 : CollatzResearch.WordTrace tailWord_1817334 prefixEnd_1817334 933165851758097906067239 := by
  unfold tailWord_1817334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4142726024882298048876191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44189077598744512521346037 4142726024882298048876191)
  ·
    refine ⟨6214089037323447073314287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4142726024882298048876191 6214089037323447073314287)
    ·
      refine ⟨9321133555985170609971431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6214089037323447073314287 9321133555985170609971431)
      ·
        refine ⟨13981700333977755914957147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9321133555985170609971431 13981700333977755914957147)
        ·
          refine ⟨20972550500966633872435721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13981700333977755914957147 20972550500966633872435721)
          ·
            refine ⟨15729412875724975404326791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20972550500966633872435721 15729412875724975404326791)
            ·
              refine ⟨23594119313587463106490187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15729412875724975404326791 23594119313587463106490187)
              ·
                refine ⟨35391178970381194659735281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23594119313587463106490187 35391178970381194659735281)
                ·
                  refine ⟨26543384227785895994801461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35391178970381194659735281 26543384227785895994801461)
                  ·
                    refine ⟨2488442271354927749512637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26543384227785895994801461 2488442271354927749512637)
                    ·
                      refine ⟨933165851758097906067239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2488442271354927749512637 933165851758097906067239)
                      ·
                        rfl

theorem cell23_1817334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1817334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817334 prefixEnd_1817334 := by exact prefixLift 1817334
  have htrace : WordTrace (prefixWord ++ tailWord_1817334) baseStart_1817334 baseEnd_1817334 := by
    simpa [prefixWord, tailWord_1817334, baseEnd_1817334] using wordTrace_append hprefix tailTrace_1817334
  have hstable : (prefixWord ++ tailWord_1817334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817334).length < 2 ^ (prefixWord ++ tailWord_1817334).sum := by decide
  have hdescent : baseEnd_1817334 < baseStart_1817334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817337 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 3, 5]
def baseStart_1817337 : Nat := 118140960795 + 1817337 * 2 ^ 59
def prefixEnd_1817337 : Nat := 4983230072969 + 3 ^ 40 * 1817337 * 2
def baseEnd_1817337 : Nat := 311055797400020464776575

theorem tailTrace_1817337 : CollatzResearch.WordTrace tailWord_1817337 prefixEnd_1817337 311055797400020464776575 := by
  unfold tailWord_1817337
  simp only [CollatzResearch.WordTrace]
  refine ⟨66283725817105900294378265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44189150544737266862918843 66283725817105900294378265)
  ·
    refine ⟨49712794362829425220783699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66283725817105900294378265 49712794362829425220783699)
    ·
      refine ⟨74569191544244137831175549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49712794362829425220783699 74569191544244137831175549)
      ·
        refine ⟨27963446829091551686690831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74569191544244137831175549 27963446829091551686690831)
        ·
          refine ⟨41945170243637327530036247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27963446829091551686690831 41945170243637327530036247)
          ·
            refine ⟨62917755365455991295054371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41945170243637327530036247 62917755365455991295054371)
            ·
              refine ⟨94376633048183986942581557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62917755365455991295054371 94376633048183986942581557)
              ·
                refine ⟨8847809348267248775867021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94376633048183986942581557 8847809348267248775867021)
                ·
                  refine ⟨3317928505600218290950133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8847809348267248775867021 3317928505600218290950133)
                  ·
                    refine ⟨311055797400020464776575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3317928505600218290950133 311055797400020464776575)
                    ·
                      rfl

theorem cell23_1817337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_1817337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817337 prefixEnd_1817337 := by exact prefixLift 1817337
  have htrace : WordTrace (prefixWord ++ tailWord_1817337) baseStart_1817337 baseEnd_1817337 := by
    simpa [prefixWord, tailWord_1817337, baseEnd_1817337] using wordTrace_append hprefix tailTrace_1817337
  have hstable : (prefixWord ++ tailWord_1817337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817337).length < 2 ^ (prefixWord ++ tailWord_1817337).sum := by decide
  have hdescent : baseEnd_1817337 < baseStart_1817337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817354 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_1817354 : Nat := 118140960795 + 1817354 * 2 ^ 59
def prefixEnd_1817354 : Nat := 4983230072969 + 3 ^ 40 * 1817354 * 2
def baseEnd_1817354 : Nat := 311058707123729275939049

theorem tailTrace_1817354 : CollatzResearch.WordTrace tailWord_1817354 prefixEnd_1817354 311058707123729275939049 := by
  unfold tailWord_1817354
  simp only [CollatzResearch.WordTrace]
  refine ⟨16571086464511078049436779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44189563905362874798498077 16571086464511078049436779)
  ·
    refine ⟨24856629696766617074155169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16571086464511078049436779 24856629696766617074155169)
    ·
      refine ⟨18642472272574962805616377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24856629696766617074155169 18642472272574962805616377)
      ·
        refine ⟨13981854204431222104212283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18642472272574962805616377 13981854204431222104212283)
        ·
          refine ⟨20972781306646833156318425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13981854204431222104212283 20972781306646833156318425)
          ·
            refine ⟨15729585979985124867238819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20972781306646833156318425 15729585979985124867238819)
            ·
              refine ⟨23594378969977687300858229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15729585979985124867238819 23594378969977687300858229)
              ·
                refine ⟨2211973028435408184455459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23594378969977687300858229 2211973028435408184455459)
                ·
                  refine ⟨3317959542653112276683189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211973028435408184455459 3317959542653112276683189)
                  ·
                    refine ⟨311058707123729275939049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3317959542653112276683189 311058707123729275939049)
                    ·
                      rfl

theorem cell23_1817354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_1817354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817354 prefixEnd_1817354 := by exact prefixLift 1817354
  have htrace : WordTrace (prefixWord ++ tailWord_1817354) baseStart_1817354 baseEnd_1817354 := by
    simpa [prefixWord, tailWord_1817354, baseEnd_1817354] using wordTrace_append hprefix tailTrace_1817354
  have hstable : (prefixWord ++ tailWord_1817354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817354).length < 2 ^ (prefixWord ++ tailWord_1817354).sum := by decide
  have hdescent : baseEnd_1817354 < baseStart_1817354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817362 : List Nat := [3, 2, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1817362 : Nat := 118140960795 + 1817362 * 2 ^ 59
def prefixEnd_1817362 : Nat := 4983230072969 + 3 ^ 40 * 1817362 * 2
def baseEnd_1817362 : Nat := 311060076405474598839037

theorem tailTrace_1817362 : CollatzResearch.WordTrace tailWord_1817362 prefixEnd_1817362 311060076405474598839037 := by
  unfold tailWord_1817362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16571159410503832391009585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44189758428010219709358893 16571159410503832391009585)
  ·
    refine ⟨12428369557877874293257189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16571159410503832391009585 12428369557877874293257189)
    ·
      refine ⟨2330319292102101429985723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12428369557877874293257189 2330319292102101429985723)
      ·
        refine ⟨3495478938153152144978585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330319292102101429985723 3495478938153152144978585)
        ·
          refine ⟨2621609203614864108733939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495478938153152144978585 2621609203614864108733939)
          ·
            refine ⟨3932413805422296163100909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621609203614864108733939 3932413805422296163100909)
            ·
              refine ⟨1474655177033361061162841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3932413805422296163100909 1474655177033361061162841)
              ·
                refine ⟨1105991382775020795872131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474655177033361061162841 1105991382775020795872131)
                ·
                  refine ⟨1658987074162531193808197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105991382775020795872131 1658987074162531193808197)
                  ·
                    refine ⟨311060076405474598839037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1658987074162531193808197 311060076405474598839037)
                    ·
                      rfl

theorem cell23_1817362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1817362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817362 prefixEnd_1817362 := by exact prefixLift 1817362
  have htrace : WordTrace (prefixWord ++ tailWord_1817362) baseStart_1817362 baseEnd_1817362 := by
    simpa [prefixWord, tailWord_1817362, baseEnd_1817362] using wordTrace_append hprefix tailTrace_1817362
  have hstable : (prefixWord ++ tailWord_1817362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817362).length < 2 ^ (prefixWord ++ tailWord_1817362).sum := by decide
  have hdescent : baseEnd_1817362 < baseStart_1817362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817384 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1817384 : Nat := 118140960795 + 1817384 * 2 ^ 59
def prefixEnd_1817384 : Nat := 4983230072969 + 3 ^ 40 * 1817384 * 2
def baseEnd_1817384 : Nat := 311063841930274236814003

theorem tailTrace_1817384 : CollatzResearch.WordTrace tailWord_1817384 prefixEnd_1817384 311063841930274236814003 := by
  unfold tailWord_1817384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33142720023967813660669603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44190293365290418214226137 33142720023967813660669603)
  ·
    refine ⟨49714080035951720491004405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33142720023967813660669603 49714080035951720491004405)
    ·
      refine ⟨4660695003370473796031663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49714080035951720491004405 4660695003370473796031663)
      ·
        refine ⟨6991042505055710694047495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660695003370473796031663 6991042505055710694047495)
        ·
          refine ⟨10486563757583566041071243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6991042505055710694047495 10486563757583566041071243)
          ·
            refine ⟨15729845636375349061606865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10486563757583566041071243 15729845636375349061606865)
            ·
              refine ⟨11797384227281511796205149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15729845636375349061606865 11797384227281511796205149)
              ·
                refine ⟨4424019085230566923576931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11797384227281511796205149 4424019085230566923576931)
                ·
                  refine ⟨6636028627845850385365397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424019085230566923576931 6636028627845850385365397)
                  ·
                    refine ⟨311063841930274236814003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6636028627845850385365397 311063841930274236814003)
                    ·
                      rfl

theorem cell23_1817384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1817384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817384 prefixEnd_1817384 := by exact prefixLift 1817384
  have htrace : WordTrace (prefixWord ++ tailWord_1817384) baseStart_1817384 baseEnd_1817384 := by
    simpa [prefixWord, tailWord_1817384, baseEnd_1817384] using wordTrace_append hprefix tailTrace_1817384
  have hstable : (prefixWord ++ tailWord_1817384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817384).length < 2 ^ (prefixWord ++ tailWord_1817384).sum := by decide
  have hdescent : baseEnd_1817384 < baseStart_1817384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817451 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 3, 3, 2]
def baseStart_1817451 : Nat := 118140960795 + 1817451 * 2 ^ 59
def prefixEnd_1817451 : Nat := 4983230072969 + 3 ^ 40 * 1817451 * 2
def baseEnd_1817451 : Nat := 933225928994673948304201

theorem tailTrace_1817451 : CollatzResearch.WordTrace tailWord_1817451 prefixEnd_1817451 933225928994673948304201 := by
  unfold tailWord_1817451
  simp only [CollatzResearch.WordTrace]
  refine ⟨66287883738692897764028207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44191922492461931842685471 66287883738692897764028207)
  ·
    refine ⟨99431825608039346646042311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66287883738692897764028207 99431825608039346646042311)
    ·
      refine ⟨149147738412059019969063467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99431825608039346646042311 149147738412059019969063467)
      ·
        refine ⟨223721607618088529953595201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149147738412059019969063467 223721607618088529953595201)
        ·
          refine ⟨167791205713566397465196401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223721607618088529953595201 167791205713566397465196401)
          ·
            refine ⟨125843404285174798098897301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167791205713566397465196401 125843404285174798098897301)
            ·
              refine ⟨5898909575867568660885811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125843404285174798098897301 5898909575867568660885811)
              ·
                refine ⟨8848364363801352991328717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898909575867568660885811 8848364363801352991328717)
                ·
                  refine ⟨3318136636425507371748269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8848364363801352991328717 3318136636425507371748269)
                  ·
                    refine ⟨1244301238659565264405601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3318136636425507371748269 1244301238659565264405601)
                    ·
                      refine ⟨933225928994673948304201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244301238659565264405601 933225928994673948304201)
                      ·
                        rfl

theorem cell23_1817451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 3, 2].length) (baseStart_1817451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817451 prefixEnd_1817451 := by exact prefixLift 1817451
  have htrace : WordTrace (prefixWord ++ tailWord_1817451) baseStart_1817451 baseEnd_1817451 := by
    simpa [prefixWord, tailWord_1817451, baseEnd_1817451] using wordTrace_append hprefix tailTrace_1817451
  have hstable : (prefixWord ++ tailWord_1817451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817451).length < 2 ^ (prefixWord ++ tailWord_1817451).sum := by decide
  have hdescent : baseEnd_1817451 < baseStart_1817451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817462 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1817462 : Nat := 118140960795 + 1817462 * 2 ^ 59
def prefixEnd_1817462 : Nat := 4983230072969 + 3 ^ 40 * 1817462 * 2
def baseEnd_1817462 : Nat := 933231577281873405266651

theorem tailTrace_1817462 : CollatzResearch.WordTrace tailWord_1817462 prefixEnd_1817462 933231577281873405266651 := by
  unfold tailWord_1817462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143017808853315415167415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44192189961102031095119093 4143017808853315415167415)
  ·
    refine ⟨6214526713279973122751123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4143017808853315415167415 6214526713279973122751123)
    ·
      refine ⟨9321790069919959684126685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6214526713279973122751123 9321790069919959684126685)
      ·
        refine ⟨3495671276219984881547507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9321790069919959684126685 3495671276219984881547507)
        ·
          refine ⟨5243506914329977322321261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3495671276219984881547507 5243506914329977322321261)
          ·
            refine ⟨1966315092873741495870473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5243506914329977322321261 1966315092873741495870473)
            ·
              refine ⟨1474736319655306121902855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966315092873741495870473 1474736319655306121902855)
              ·
                refine ⟨2212104479482959182854283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474736319655306121902855 2212104479482959182854283)
                ·
                  refine ⟨3318156719224438774281425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212104479482959182854283 3318156719224438774281425)
                  ·
                    refine ⟨2488617539418329080711069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3318156719224438774281425 2488617539418329080711069)
                    ·
                      refine ⟨933231577281873405266651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2488617539418329080711069 933231577281873405266651)
                      ·
                        rfl

theorem cell23_1817462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1817462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817462 prefixEnd_1817462 := by exact prefixLift 1817462
  have htrace : WordTrace (prefixWord ++ tailWord_1817462) baseStart_1817462 baseEnd_1817462 := by
    simpa [prefixWord, tailWord_1817462, baseEnd_1817462] using wordTrace_append hprefix tailTrace_1817462
  have hstable : (prefixWord ++ tailWord_1817462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817462).length < 2 ^ (prefixWord ++ tailWord_1817462).sum := by decide
  have hdescent : baseEnd_1817462 < baseStart_1817462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817484 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1817484 : Nat := 118140960795 + 1817484 * 2 ^ 59
def prefixEnd_1817484 : Nat := 4983230072969 + 3 ^ 40 * 1817484 * 2
def baseEnd_1817484 : Nat := 933242873856272319191549

theorem tailTrace_1817484 : CollatzResearch.WordTrace tailWord_1817484 prefixEnd_1817484 933242873856272319191549 := by
  unfold tailWord_1817484
  simp only [CollatzResearch.WordTrace]
  refine ⟨33144543673786672199989753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44192724898382229599986337 33144543673786672199989753)
  ·
    refine ⟨24858407755340004149992315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33144543673786672199989753 24858407755340004149992315)
    ·
      refine ⟨37287611633010006224988473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24858407755340004149992315 37287611633010006224988473)
      ·
        refine ⟨27965708724757504668741355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37287611633010006224988473 27965708724757504668741355)
        ·
          refine ⟨41948563087136257003112033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27965708724757504668741355 41948563087136257003112033)
          ·
            refine ⟨31461422315352192752334025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41948563087136257003112033 31461422315352192752334025)
            ·
              refine ⟨23596066736514144564250519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31461422315352192752334025 23596066736514144564250519)
              ·
                refine ⟨35394100104771216846375779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23596066736514144564250519 35394100104771216846375779)
                ·
                  refine ⟨53091150157156825269563669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35394100104771216846375779 53091150157156825269563669)
                  ·
                    refine ⟨2488647663616726184510797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53091150157156825269563669 2488647663616726184510797)
                    ·
                      refine ⟨933242873856272319191549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2488647663616726184510797 933242873856272319191549)
                      ·
                        rfl

theorem cell23_1817484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1817484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817484 prefixEnd_1817484 := by exact prefixLift 1817484
  have htrace : WordTrace (prefixWord ++ tailWord_1817484) baseStart_1817484 baseEnd_1817484 := by
    simpa [prefixWord, tailWord_1817484, baseEnd_1817484] using wordTrace_append hprefix tailTrace_1817484
  have hstable : (prefixWord ++ tailWord_1817484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817484).length < 2 ^ (prefixWord ++ tailWord_1817484).sum := by decide
  have hdescent : baseEnd_1817484 < baseStart_1817484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817504 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 7]
def baseStart_1817504 : Nat := 118140960795 + 1817504 * 2 ^ 59
def prefixEnd_1817504 : Nat := 4983230072969 + 3 ^ 40 * 1817504 * 2
def baseEnd_1817504 : Nat := 103694793718818026771273

theorem tailTrace_1817504 : CollatzResearch.WordTrace tailWord_1817504 prefixEnd_1817504 103694793718818026771273 := by
  unfold tailWord_1817504
  simp only [CollatzResearch.WordTrace]
  refine ⟨33144908403750443907853783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44193211205000591877138377 33144908403750443907853783)
  ·
    refine ⟨49717362605625665861780675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33144908403750443907853783 49717362605625665861780675)
    ·
      refine ⟨74576043908438498792671013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49717362605625665861780675 74576043908438498792671013)
      ·
        refine ⟨13983008232832218523625815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74576043908438498792671013 13983008232832218523625815)
        ·
          refine ⟨20974512349248327785438723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13983008232832218523625815 20974512349248327785438723)
          ·
            refine ⟨31461768523872491678158085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20974512349248327785438723 31461768523872491678158085)
            ·
              refine ⟨5899081598226092189654641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31461768523872491678158085 5899081598226092189654641)
              ·
                refine ⟨4424311198669569142240981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5899081598226092189654641 4424311198669569142240981)
                ·
                  refine ⟨103694793718818026771273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4424311198669569142240981 103694793718818026771273)
                  ·
                    rfl

theorem cell23_1817504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 7].length) (baseStart_1817504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817504 prefixEnd_1817504 := by exact prefixLift 1817504
  have htrace : WordTrace (prefixWord ++ tailWord_1817504) baseStart_1817504 baseEnd_1817504 := by
    simpa [prefixWord, tailWord_1817504, baseEnd_1817504] using wordTrace_append hprefix tailTrace_1817504
  have hstable : (prefixWord ++ tailWord_1817504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817504).length < 2 ^ (prefixWord ++ tailWord_1817504).sum := by decide
  have hdescent : baseEnd_1817504 < baseStart_1817504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817584 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_1817584 : Nat := 118140960795 + 1817584 * 2 ^ 59
def prefixEnd_1817584 : Nat := 4983230072969 + 3 ^ 40 * 1817584 * 2
def baseEnd_1817584 : Nat := 933294221921721927941089

theorem tailTrace_1817584 : CollatzResearch.WordTrace tailWord_1817584 prefixEnd_1817584 933294221921721927941089 := by
  unfold tailWord_1817584
  simp only [CollatzResearch.WordTrace]
  refine ⟨33146367323605530739309903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44195156431474040985746537 33146367323605530739309903)
  ·
    refine ⟨49719550985408296108964855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33146367323605530739309903 49719550985408296108964855)
    ·
      refine ⟨74579326478112444163447283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49719550985408296108964855 74579326478112444163447283)
      ·
        refine ⟨111868989717168666245170925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74579326478112444163447283 111868989717168666245170925)
        ·
          refine ⟨41950871143938249841939097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111868989717168666245170925 41950871143938249841939097)
          ·
            refine ⟨31463153357953687381454323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41950871143938249841939097 31463153357953687381454323)
            ·
              refine ⟨47194730036930531072181485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31463153357953687381454323 47194730036930531072181485)
              ·
                refine ⟨17698023763848949152068057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47194730036930531072181485 17698023763848949152068057)
                ·
                  refine ⟨13273517822886711864051043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17698023763848949152068057 13273517822886711864051043)
                  ·
                    refine ⟨19910276734330067796076565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13273517822886711864051043 19910276734330067796076565)
                    ·
                      refine ⟨933294221921721927941089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19910276734330067796076565 933294221921721927941089)
                      ·
                        rfl

theorem cell23_1817584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_1817584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817584 prefixEnd_1817584 := by exact prefixLift 1817584
  have htrace : WordTrace (prefixWord ++ tailWord_1817584) baseStart_1817584 baseEnd_1817584 := by
    simpa [prefixWord, tailWord_1817584, baseEnd_1817584] using wordTrace_append hprefix tailTrace_1817584
  have hstable : (prefixWord ++ tailWord_1817584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817584).length < 2 ^ (prefixWord ++ tailWord_1817584).sum := by decide
  have hdescent : baseEnd_1817584 < baseStart_1817584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817589 : List Nat := [1, 3, 5, 2, 1, 2, 2, 2, 5]
def baseStart_1817589 : Nat := 118140960795 + 1817589 * 2 ^ 59
def prefixEnd_1817589 : Nat := 4983230072969 + 3 ^ 40 * 1817589 * 2
def baseEnd_1817589 : Nat := 103699643258332712042063

theorem tailTrace_1817589 : CollatzResearch.WordTrace tailWord_1817589 prefixEnd_1817589 103699643258332712042063 := by
  unfold tailWord_1817589
  simp only [CollatzResearch.WordTrace]
  refine ⟨66292917012192947332551821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44195278008128631555034547 66292917012192947332551821)
  ·
    refine ⟨24859843879572355249706933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66292917012192947332551821 24859843879572355249706933)
    ·
      refine ⟨2330610363709908304660025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24859843879572355249706933 2330610363709908304660025)
      ·
        refine ⟨1747957772782431228495019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2330610363709908304660025 1747957772782431228495019)
        ·
          refine ⟨2621936659173646842742529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747957772782431228495019 2621936659173646842742529)
          ·
            refine ⟨1966452494380235132056897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2621936659173646842742529 1966452494380235132056897)
            ·
              refine ⟨1474839370785176349042673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966452494380235132056897 1474839370785176349042673)
              ·
                refine ⟨1106129528088882261782005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474839370785176349042673 1106129528088882261782005)
                ·
                  refine ⟨103699643258332712042063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106129528088882261782005 103699643258332712042063)
                  ·
                    rfl

theorem cell23_1817589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_1817589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817589 prefixEnd_1817589 := by exact prefixLift 1817589
  have htrace : WordTrace (prefixWord ++ tailWord_1817589) baseStart_1817589 baseEnd_1817589 := by
    simpa [prefixWord, tailWord_1817589, baseEnd_1817589] using wordTrace_append hprefix tailTrace_1817589
  have hstable : (prefixWord ++ tailWord_1817589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817589).length < 2 ^ (prefixWord ++ tailWord_1817589).sum := by decide
  have hdescent : baseEnd_1817589 < baseStart_1817589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817594 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 8]
def baseStart_1817594 : Nat := 118140960795 + 1817594 * 2 ^ 59
def prefixEnd_1817594 : Nat := 4983230072969 + 3 ^ 40 * 1817594 * 2
def baseEnd_1817594 : Nat := 103699928525362987646227

theorem tailTrace_1817594 : CollatzResearch.WordTrace tailWord_1817594 prefixEnd_1817594 103699928525362987646227 := by
  unfold tailWord_1817594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16573274844293708296620959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44195399584783222124322557 16573274844293708296620959)
  ·
    refine ⟨24859912266440562444931439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16573274844293708296620959 24859912266440562444931439)
    ·
      refine ⟨37289868399660843667397159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24859912266440562444931439 37289868399660843667397159)
      ·
        refine ⟨55934802599491265501095739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37289868399660843667397159 55934802599491265501095739)
        ·
          refine ⟨83902203899236898251643609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55934802599491265501095739 83902203899236898251643609)
          ·
            refine ⟨62926652924427673688732707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83902203899236898251643609 62926652924427673688732707)
            ·
              refine ⟨94389979386641510533099061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62926652924427673688732707 94389979386641510533099061)
              ·
                refine ⟨8849060567497641612478037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94389979386641510533099061 8849060567497641612478037)
                ·
                  refine ⟨103699928525362987646227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8849060567497641612478037 103699928525362987646227)
                  ·
                    rfl

theorem cell23_1817594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_1817594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817594 prefixEnd_1817594 := by exact prefixLift 1817594
  have htrace : WordTrace (prefixWord ++ tailWord_1817594) baseStart_1817594 baseEnd_1817594 := by
    simpa [prefixWord, tailWord_1817594, baseEnd_1817594] using wordTrace_append hprefix tailTrace_1817594
  have hstable : (prefixWord ++ tailWord_1817594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817594).length < 2 ^ (prefixWord ++ tailWord_1817594).sum := by decide
  have hdescent : baseEnd_1817594 < baseStart_1817594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817611 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 6]
def baseStart_1817611 : Nat := 118140960795 + 1817611 * 2 ^ 59
def prefixEnd_1817611 : Nat := 4983230072969 + 3 ^ 40 * 1817611 * 2
def baseEnd_1817611 : Nat := 103700898433265924700385

theorem tailTrace_1817611 : CollatzResearch.WordTrace tailWord_1817611 prefixEnd_1817611 103700898433265924700385 := by
  unfold tailWord_1817611
  simp only [CollatzResearch.WordTrace]
  refine ⟨66293719418113245089852687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44195812945408830059901791 66293719418113245089852687)
  ·
    refine ⟨99440579127169867634779031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66293719418113245089852687 99440579127169867634779031)
    ·
      refine ⟨149160868690754801452168547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99440579127169867634779031 149160868690754801452168547)
      ·
        refine ⟨223741303036132202178252821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149160868690754801452168547 223741303036132202178252821)
        ·
          refine ⟨10487873579818696977105601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223741303036132202178252821 10487873579818696977105601)
          ·
            refine ⟨7865905184864022732829201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10487873579818696977105601 7865905184864022732829201)
            ·
              refine ⟨5899428888648017049621901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7865905184864022732829201 5899428888648017049621901)
              ·
                refine ⟨2212285833243006393608213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5899428888648017049621901 2212285833243006393608213)
                ·
                  refine ⟨103700898433265924700385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2212285833243006393608213 103700898433265924700385)
                  ·
                    rfl

theorem cell23_1817611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 6].length) (baseStart_1817611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817611 prefixEnd_1817611 := by exact prefixLift 1817611
  have htrace : WordTrace (prefixWord ++ tailWord_1817611) baseStart_1817611 baseEnd_1817611 := by
    simpa [prefixWord, tailWord_1817611, baseEnd_1817611] using wordTrace_append hprefix tailTrace_1817611
  have hstable : (prefixWord ++ tailWord_1817611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817611).length < 2 ^ (prefixWord ++ tailWord_1817611).sum := by decide
  have hdescent : baseEnd_1817611 < baseStart_1817611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817648 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 4, 3, 2]
def baseStart_1817648 : Nat := 118140960795 + 1817648 * 2 ^ 59
def prefixEnd_1817648 : Nat := 4983230072969 + 3 ^ 40 * 1817648 * 2
def baseEnd_1817648 : Nat := 933327084683609677540795

theorem tailTrace_1817648 : CollatzResearch.WordTrace tailWord_1817648 prefixEnd_1817648 933327084683609677540795 := by
  unfold tailWord_1817648
  simp only [CollatzResearch.WordTrace]
  refine ⟨33147534459489600204474799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44196712612652800272633065 33147534459489600204474799)
  ·
    refine ⟨49721301689234400306712199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33147534459489600204474799 49721301689234400306712199)
    ·
      refine ⟨74581952533851600460068299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49721301689234400306712199 74581952533851600460068299)
      ·
        refine ⟨111872928800777400690102449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74581952533851600460068299 111872928800777400690102449)
        ·
          refine ⟨83904696600583050517576837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111872928800777400690102449 83904696600583050517576837)
          ·
            refine ⟨15732130612609321972045657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83904696600583050517576837 15732130612609321972045657)
            ·
              refine ⟨11799097959456991479034243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15732130612609321972045657 11799097959456991479034243)
              ·
                refine ⟨17698646939185487218551365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11799097959456991479034243 17698646939185487218551365)
                ·
                  refine ⟨3318496301097278853478381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17698646939185487218551365 3318496301097278853478381)
                  ·
                    refine ⟨1244436112911479570054393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3318496301097278853478381 1244436112911479570054393)
                    ·
                      refine ⟨933327084683609677540795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244436112911479570054393 933327084683609677540795)
                      ·
                        rfl

theorem cell23_1817648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 3, 2].length) (baseStart_1817648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817648 prefixEnd_1817648 := by exact prefixLift 1817648
  have htrace : WordTrace (prefixWord ++ tailWord_1817648) baseStart_1817648 baseEnd_1817648 := by
    simpa [prefixWord, tailWord_1817648, baseEnd_1817648] using wordTrace_append hprefix tailTrace_1817648
  have hstable : (prefixWord ++ tailWord_1817648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817648).length < 2 ^ (prefixWord ++ tailWord_1817648).sum := by decide
  have hdescent : baseEnd_1817648 < baseStart_1817648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817678 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_1817678 : Nat := 118140960795 + 1817678 * 2 ^ 59
def prefixEnd_1817678 : Nat := 4983230072969 + 3 ^ 40 * 1817678 * 2
def baseEnd_1817678 : Nat := 933342489103244560165657

theorem tailTrace_1817678 : CollatzResearch.WordTrace tailWord_1817678 prefixEnd_1817678 933342489103244560165657 := by
  unfold tailWord_1817678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287020388608814441567711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44197442072580343688361125 8287020388608814441567711)
  ·
    refine ⟨12430530582913221662351567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8287020388608814441567711 12430530582913221662351567)
    ·
      refine ⟨18645795874369832493527351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12430530582913221662351567 18645795874369832493527351)
      ·
        refine ⟨27968693811554748740291027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18645795874369832493527351 27968693811554748740291027)
        ·
          refine ⟨41953040717332123110436541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27968693811554748740291027 41953040717332123110436541)
          ·
            refine ⟨15732390268999546166413703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41953040717332123110436541 15732390268999546166413703)
            ·
              refine ⟨23598585403499319249620555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15732390268999546166413703 23598585403499319249620555)
              ·
                refine ⟨35397878105248978874430833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23598585403499319249620555 35397878105248978874430833)
                ·
                  refine ⟨26548408578936734155823125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35397878105248978874430833 26548408578936734155823125)
                  ·
                    refine ⟨1244456652137659413554209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26548408578936734155823125 1244456652137659413554209)
                    ·
                      refine ⟨933342489103244560165657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244456652137659413554209 933342489103244560165657)
                      ·
                        rfl

theorem cell23_1817678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_1817678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817678 prefixEnd_1817678 := by exact prefixLift 1817678
  have htrace : WordTrace (prefixWord ++ tailWord_1817678) baseStart_1817678 baseEnd_1817678 := by
    simpa [prefixWord, tailWord_1817678, baseEnd_1817678] using wordTrace_append hprefix tailTrace_1817678
  have hstable : (prefixWord ++ tailWord_1817678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817678).length < 2 ^ (prefixWord ++ tailWord_1817678).sum := by decide
  have hdescent : baseEnd_1817678 < baseStart_1817678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817718 : List Nat := [5, 1, 1, 2, 1, 1, 4, 8]
def baseStart_1817718 : Nat := 118140960795 + 1817718 * 2 ^ 59
def prefixEnd_1817718 : Nat := 4983230072969 + 3 ^ 40 * 1817718 * 2
def baseEnd_1817718 : Nat := 34569001049237940876499

theorem tailTrace_1817718 : CollatzResearch.WordTrace tailWord_1817718 prefixEnd_1817718 34569001049237940876499 := by
  unfold tailWord_1817718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143601376795350147749863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44198414685817068242665205 4143601376795350147749863)
  ·
    refine ⟨6215402065193025221624795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4143601376795350147749863 6215402065193025221624795)
    ·
      refine ⟨9323103097789537832437193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215402065193025221624795 9323103097789537832437193)
      ·
        refine ⟨6992327323342153374327895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9323103097789537832437193 6992327323342153374327895)
        ·
          refine ⟨10488490985013230061491843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992327323342153374327895 10488490985013230061491843)
          ·
            refine ⟨15732736477519845092237765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488490985013230061491843 15732736477519845092237765)
            ·
              refine ⟨2949888089534970954794581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15732736477519845092237765 2949888089534970954794581)
              ·
                refine ⟨34569001049237940876499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2949888089534970954794581 34569001049237940876499)
                ·
                  rfl

theorem cell23_1817718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_1817718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817718 prefixEnd_1817718 := by exact prefixLift 1817718
  have htrace : WordTrace (prefixWord ++ tailWord_1817718) baseStart_1817718 baseEnd_1817718 := by
    simpa [prefixWord, tailWord_1817718, baseEnd_1817718] using wordTrace_append hprefix tailTrace_1817718
  have hstable : (prefixWord ++ tailWord_1817718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817718).length < 2 ^ (prefixWord ++ tailWord_1817718).sum := by decide
  have hdescent : baseEnd_1817718 < baseStart_1817718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817726 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1817726 : Nat := 118140960795 + 1817726 * 2 ^ 59
def prefixEnd_1817726 : Nat := 4983230072969 + 3 ^ 40 * 1817726 * 2
def baseEnd_1817726 : Nat := 311122378724886790788479

theorem tailTrace_1817726 : CollatzResearch.WordTrace tailWord_1817726 prefixEnd_1817726 311122378724886790788479 := by
  unfold tailWord_1817726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287239226587077466286129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44198609208464413153526021 8287239226587077466286129)
  ·
    refine ⟨6215429419940308099714597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8287239226587077466286129 6215429419940308099714597)
    ·
      refine ⟨1165393016238807768696487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6215429419940308099714597 1165393016238807768696487)
      ·
        refine ⟨1748089524358211653044731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165393016238807768696487 1748089524358211653044731)
        ·
          refine ⟨2622134286537317479567097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748089524358211653044731 2622134286537317479567097)
          ·
            refine ⟨1966600714902988109675323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622134286537317479567097 1966600714902988109675323)
            ·
              refine ⟨2949901072354482164512985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966600714902988109675323 2949901072354482164512985)
              ·
                refine ⟨2212425804265861623384739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2949901072354482164512985 2212425804265861623384739)
                ·
                  refine ⟨3318638706398792435077109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212425804265861623384739 3318638706398792435077109)
                  ·
                    refine ⟨311122378724886790788479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3318638706398792435077109 311122378724886790788479)
                    ·
                      rfl

theorem cell23_1817726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1817726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817726 prefixEnd_1817726 := by exact prefixLift 1817726
  have htrace : WordTrace (prefixWord ++ tailWord_1817726) baseStart_1817726 baseEnd_1817726 := by
    simpa [prefixWord, tailWord_1817726, baseEnd_1817726] using wordTrace_append hprefix tailTrace_1817726
  have hstable : (prefixWord ++ tailWord_1817726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817726).length < 2 ^ (prefixWord ++ tailWord_1817726).sum := by decide
  have hdescent : baseEnd_1817726 < baseStart_1817726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817732 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1817732 : Nat := 118140960795 + 1817732 * 2 ^ 59
def prefixEnd_1817732 : Nat := 4983230072969 + 3 ^ 40 * 1817732 * 2
def baseEnd_1817732 : Nat := 933370217058587348890409

theorem tailTrace_1817732 : CollatzResearch.WordTrace tailWord_1817732 prefixEnd_1817732 933370217058587348890409 := by
  unfold tailWord_1817732
  simp only [CollatzResearch.WordTrace]
  refine ⟨33149066325337441377503725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44198755100449921836671633 33149066325337441377503725)
  ·
    refine ⟨12430899872001540516563897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33149066325337441377503725 12430899872001540516563897)
    ·
      refine ⟨9323174904001155387422923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12430899872001540516563897 9323174904001155387422923)
      ·
        refine ⟨13984762356001733081134385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323174904001155387422923 13984762356001733081134385)
        ·
          refine ⟨10488571767001299810850789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13984762356001733081134385 10488571767001299810850789)
          ·
            refine ⟨1966607206312743714534523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10488571767001299810850789 1966607206312743714534523)
            ·
              refine ⟨2949910809469115571801785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966607206312743714534523 2949910809469115571801785)
              ·
                refine ⟨2212433107101836678851339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2949910809469115571801785 2212433107101836678851339)
                ·
                  refine ⟨3318649660652755018277009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212433107101836678851339 3318649660652755018277009)
                  ·
                    refine ⟨2488987245489566263707757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3318649660652755018277009 2488987245489566263707757)
                    ·
                      refine ⟨933370217058587348890409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2488987245489566263707757 933370217058587348890409)
                      ·
                        rfl

theorem cell23_1817732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1817732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817732 prefixEnd_1817732 := by exact prefixLift 1817732
  have htrace : WordTrace (prefixWord ++ tailWord_1817732) baseStart_1817732 baseEnd_1817732 := by
    simpa [prefixWord, tailWord_1817732, baseEnd_1817732] using wordTrace_append hprefix tailTrace_1817732
  have hstable : (prefixWord ++ tailWord_1817732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817732).length < 2 ^ (prefixWord ++ tailWord_1817732).sum := by decide
  have hdescent : baseEnd_1817732 < baseStart_1817732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817778 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_1817778 : Nat := 118140960795 + 1817778 * 2 ^ 59
def prefixEnd_1817778 : Nat := 4983230072969 + 3 ^ 40 * 1817778 * 2
def baseEnd_1817778 : Nat := 311131279056231389638399

theorem tailTrace_1817778 : CollatzResearch.WordTrace tailWord_1817778 prefixEnd_1817778 311131279056231389638399 := by
  unfold tailWord_1817778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16574952602127058152795497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44199873605672155074121325 16574952602127058152795497)
  ·
    refine ⟨12431214451595293614596623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16574952602127058152795497 12431214451595293614596623)
    ·
      refine ⟨18646821677392940421894935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12431214451595293614596623 18646821677392940421894935)
      ·
        refine ⟨27970232516089410632842403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18646821677392940421894935 27970232516089410632842403)
        ·
          refine ⟨41955348774134115949263605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27970232516089410632842403 41955348774134115949263605)
          ·
            refine ⟨3933313947575073370243463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41955348774134115949263605 3933313947575073370243463)
            ·
              refine ⟨5899970921362610055365195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933313947575073370243463 5899970921362610055365195)
              ·
                refine ⟨8849956382043915083047793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5899970921362610055365195 8849956382043915083047793)
                ·
                  refine ⟨6637467286532936312285845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8849956382043915083047793 6637467286532936312285845)
                  ·
                    refine ⟨311131279056231389638399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6637467286532936312285845 311131279056231389638399)
                    ·
                      rfl

theorem cell23_1817778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_1817778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817778 prefixEnd_1817778 := by exact prefixLift 1817778
  have htrace : WordTrace (prefixWord ++ tailWord_1817778) baseStart_1817778 baseEnd_1817778 := by
    simpa [prefixWord, tailWord_1817778, baseEnd_1817778] using wordTrace_append hprefix tailTrace_1817778
  have hstable : (prefixWord ++ tailWord_1817778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817778).length < 2 ^ (prefixWord ++ tailWord_1817778).sum := by decide
  have hdescent : baseEnd_1817778 < baseStart_1817778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817785 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 1, 4, 2]
def baseStart_1817785 : Nat := 118140960795 + 1817785 * 2 ^ 59
def prefixEnd_1817785 : Nat := 4983230072969 + 3 ^ 40 * 1817785 * 2
def baseEnd_1817785 : Nat := 933397431533275641527665

theorem tailTrace_1817785 : CollatzResearch.WordTrace tailWord_1817785 prefixEnd_1817785 933397431533275641527665 := by
  unfold tailWord_1817785
  simp only [CollatzResearch.WordTrace]
  refine ⟨66300065719482872806686809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44200043812988581871124539 66300065719482872806686809)
  ·
    refine ⟨49725049289612154605015107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66300065719482872806686809 49725049289612154605015107)
    ·
      refine ⟨74587573934418231907522661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49725049289612154605015107 74587573934418231907522661)
      ·
        refine ⟨13985170112703418482660499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74587573934418231907522661 13985170112703418482660499)
        ·
          refine ⟨20977755169055127723990749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13985170112703418482660499 20977755169055127723990749)
          ·
            refine ⟨7866658188395672896496531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20977755169055127723990749 7866658188395672896496531)
            ·
              refine ⟨11799987282593509344744797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866658188395672896496531 11799987282593509344744797)
              ·
                refine ⟨4424995230972566004279299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11799987282593509344744797 4424995230972566004279299)
                ·
                  refine ⟨6637492846458849006418949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424995230972566004279299 6637492846458849006418949)
                  ·
                    refine ⟨1244529908711034188703553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6637492846458849006418949 1244529908711034188703553)
                    ·
                      refine ⟨933397431533275641527665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244529908711034188703553 933397431533275641527665)
                      ·
                        rfl

theorem cell23_1817785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_1817785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817785 prefixEnd_1817785 := by exact prefixLift 1817785
  have htrace : WordTrace (prefixWord ++ tailWord_1817785) baseStart_1817785 baseEnd_1817785 := by
    simpa [prefixWord, tailWord_1817785, baseEnd_1817785] using wordTrace_append hprefix tailTrace_1817785
  have hstable : (prefixWord ++ tailWord_1817785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817785).length < 2 ^ (prefixWord ++ tailWord_1817785).sum := by decide
  have hdescent : baseEnd_1817785 < baseStart_1817785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817791 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 9]
def baseStart_1817791 : Nat := 118140960795 + 1817791 * 2 ^ 59
def prefixEnd_1817791 : Nat := 4983230072969 + 3 ^ 40 * 1817791 * 2
def baseEnd_1817791 : Nat := 103711168046355846450293

theorem tailTrace_1817791 : CollatzResearch.WordTrace tailWord_1817791 prefixEnd_1817791 103711168046355846450293 := by
  unfold tailWord_1817791
  simp only [CollatzResearch.WordTrace]
  refine ⟨66300284557461135831405227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44200189704974090554270151 66300284557461135831405227)
  ·
    refine ⟨99450426836191703747107841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66300284557461135831405227 99450426836191703747107841)
    ·
      refine ⟨74587820127143777810330881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99450426836191703747107841 74587820127143777810330881)
      ·
        refine ⟨55940865095357833357748161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74587820127143777810330881 55940865095357833357748161)
        ·
          refine ⟨41955648821518375018311121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55940865095357833357748161 41955648821518375018311121)
          ·
            refine ⟨31466736616138781263733341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41955648821518375018311121 31466736616138781263733341)
            ·
              refine ⟨11800026231052042973900003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31466736616138781263733341 11800026231052042973900003)
              ·
                refine ⟨17700039346578064460850005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11800026231052042973900003 17700039346578064460850005)
                ·
                  refine ⟨103711168046355846450293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17700039346578064460850005 103711168046355846450293)
                  ·
                    rfl

theorem cell23_1817791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 9].length) (baseStart_1817791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817791 prefixEnd_1817791 := by exact prefixLift 1817791
  have htrace : WordTrace (prefixWord ++ tailWord_1817791) baseStart_1817791 baseEnd_1817791 := by
    simpa [prefixWord, tailWord_1817791, baseEnd_1817791] using wordTrace_append hprefix tailTrace_1817791
  have hstable : (prefixWord ++ tailWord_1817791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817791).length < 2 ^ (prefixWord ++ tailWord_1817791).sum := by decide
  have hdescent : baseEnd_1817791 < baseStart_1817791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817806 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_1817806 : Nat := 118140960795 + 1817806 * 2 ^ 59
def prefixEnd_1817806 : Nat := 4983230072969 + 3 ^ 40 * 1817806 * 2
def baseEnd_1817806 : Nat := 933408214627020059365069

theorem tailTrace_1817806 : CollatzResearch.WordTrace tailWord_1817806 prefixEnd_1817806 933408214627020059365069 := by
  unfold tailWord_1817806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287603956550849174150159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44200554434937862262134181 8287603956550849174150159)
  ·
    refine ⟨12431405934826273761225239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8287603956550849174150159 12431405934826273761225239)
    ·
      refine ⟨18647108902239410641837859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12431405934826273761225239 18647108902239410641837859)
      ·
        refine ⟨27970663353359115962756789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18647108902239410641837859 27970663353359115962756789)
        ·
          refine ⟨2622249689377417121508449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27970663353359115962756789 2622249689377417121508449)
          ·
            refine ⟨1966687267033062841131337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622249689377417121508449 1966687267033062841131337)
            ·
              refine ⟨1475015450274797130848503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966687267033062841131337 1475015450274797130848503)
              ·
                refine ⟨2212523175412195696272755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475015450274797130848503 2212523175412195696272755)
                ·
                  refine ⟨3318784763118293544409133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212523175412195696272755 3318784763118293544409133)
                  ·
                    refine ⟨1244544286169360079153425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3318784763118293544409133 1244544286169360079153425)
                    ·
                      refine ⟨933408214627020059365069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244544286169360079153425 933408214627020059365069)
                      ·
                        rfl

theorem cell23_1817806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_1817806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817806 prefixEnd_1817806 := by exact prefixLift 1817806
  have htrace : WordTrace (prefixWord ++ tailWord_1817806) baseStart_1817806 baseEnd_1817806 := by
    simpa [prefixWord, tailWord_1817806, baseEnd_1817806] using wordTrace_append hprefix tailTrace_1817806
  have hstable : (prefixWord ++ tailWord_1817806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817806).length < 2 ^ (prefixWord ++ tailWord_1817806).sum := by decide
  have hdescent : baseEnd_1817806 < baseStart_1817806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817825 : List Nat := [1, 2, 3, 1, 3, 2, 2, 4, 5]
def baseStart_1817825 : Nat := 118140960795 + 1817825 * 2 ^ 59
def prefixEnd_1817825 : Nat := 4983230072969 + 3 ^ 40 * 1817825 * 2
def baseEnd_1817825 : Nat := 103713107862161720558609

theorem tailTrace_1817825 : CollatzResearch.WordTrace tailWord_1817825 prefixEnd_1817825 103713107862161720558609 := by
  unfold tailWord_1817825
  simp only [CollatzResearch.WordTrace]
  refine ⟨66301524639337959638142929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44201016426225306425428619 66301524639337959638142929)
  ·
    refine ⟨49726143479503469728607197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66301524639337959638142929 49726143479503469728607197)
    ·
      refine ⟨18647303804813801148227699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49726143479503469728607197 18647303804813801148227699)
      ·
        refine ⟨27970955707220701722341549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18647303804813801148227699 27970955707220701722341549)
        ·
          refine ⟨10489108390207763145878081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27970955707220701722341549 10489108390207763145878081)
          ·
            refine ⟨7866831292655822359408561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10489108390207763145878081 7866831292655822359408561)
            ·
              refine ⟨5900123469491866769556421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7866831292655822359408561 5900123469491866769556421)
              ·
                refine ⟨1106273150529725019291829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5900123469491866769556421 1106273150529725019291829)
                ·
                  refine ⟨103713107862161720558609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106273150529725019291829 103713107862161720558609)
                  ·
                    rfl

theorem cell23_1817825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 5].length) (baseStart_1817825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817825 prefixEnd_1817825 := by exact prefixLift 1817825
  have htrace : WordTrace (prefixWord ++ tailWord_1817825) baseStart_1817825 baseEnd_1817825 := by
    simpa [prefixWord, tailWord_1817825, baseEnd_1817825] using wordTrace_append hprefix tailTrace_1817825
  have hstable : (prefixWord ++ tailWord_1817825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817825).length < 2 ^ (prefixWord ++ tailWord_1817825).sum := by decide
  have hdescent : baseEnd_1817825 < baseStart_1817825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817838 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1817838 : Nat := 118140960795 + 1817838 * 2 ^ 59
def prefixEnd_1817838 : Nat := 4983230072969 + 3 ^ 40 * 1817838 * 2
def baseEnd_1817838 : Nat := 311141548669321311388307

theorem tailTrace_1817838 : CollatzResearch.WordTrace tailWord_1817838 prefixEnd_1817838 311141548669321311388307 := by
  unfold tailWord_1817838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287749848536357857295771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44201332525527241905577445 8287749848536357857295771)
  ·
    refine ⟨12431624772804536785943657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8287749848536357857295771 12431624772804536785943657)
    ·
      refine ⟨9323718579603402589457743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12431624772804536785943657 9323718579603402589457743)
      ·
        refine ⟨13985577869405103884186615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323718579603402589457743 13985577869405103884186615)
        ·
          refine ⟨20978366804107655826279923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13985577869405103884186615 20978366804107655826279923)
          ·
            refine ⟨31467550206161483739419885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20978366804107655826279923 31467550206161483739419885)
            ·
              refine ⟨11800331327310556402282457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31467550206161483739419885 11800331327310556402282457)
              ·
                refine ⟨8850248495482917301711843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11800331327310556402282457 8850248495482917301711843)
                ·
                  refine ⟨13275372743224375952567765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850248495482917301711843 13275372743224375952567765)
                  ·
                    refine ⟨311141548669321311388307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13275372743224375952567765 311141548669321311388307)
                    ·
                      rfl

theorem cell23_1817838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1817838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817838 prefixEnd_1817838 := by exact prefixLift 1817838
  have htrace : WordTrace (prefixWord ++ tailWord_1817838) baseStart_1817838 baseEnd_1817838 := by
    simpa [prefixWord, tailWord_1817838, baseEnd_1817838] using wordTrace_append hprefix tailTrace_1817838
  have hstable : (prefixWord ++ tailWord_1817838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817838).length < 2 ^ (prefixWord ++ tailWord_1817838).sum := by decide
  have hdescent : baseEnd_1817838 < baseStart_1817838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817959 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_1817959 : Nat := 118140960795 + 1817959 * 2 ^ 59
def prefixEnd_1817959 : Nat := 4983230072969 + 3 ^ 40 * 1817959 * 2
def baseEnd_1817959 : Nat := 933486777167157960751865

theorem tailTrace_1817959 : CollatzResearch.WordTrace tailWord_1817959 prefixEnd_1817959 933486777167157960751865 := by
  unfold tailWord_1817959
  simp only [CollatzResearch.WordTrace]
  refine ⟨66306412020852500523520931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44204274680568333682347287 66306412020852500523520931)
  ·
    refine ⟨99459618031278750785281397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66306412020852500523520931 99459618031278750785281397)
    ·
      refine ⟨9324339190432382886120131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99459618031278750785281397 9324339190432382886120131)
      ·
        refine ⟨13986508785648574329180197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9324339190432382886120131 13986508785648574329180197)
        ·
          refine ⟨2622470397309107686721287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13986508785648574329180197 2622470397309107686721287)
          ·
            refine ⟨3933705595963661530081931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622470397309107686721287 3933705595963661530081931)
            ·
              refine ⟨5900558393945492295122897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933705595963661530081931 5900558393945492295122897)
              ·
                refine ⟨4425418795459119221342173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5900558393945492295122897 4425418795459119221342173)
                ·
                  refine ⟨1659532048297169708003315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4425418795459119221342173 1659532048297169708003315)
                  ·
                    refine ⟨2489298072445754562004973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1659532048297169708003315 2489298072445754562004973)
                    ·
                      refine ⟨933486777167157960751865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2489298072445754562004973 933486777167157960751865)
                      ·
                        rfl

theorem cell23_1817959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_1817959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817959 prefixEnd_1817959 := by exact prefixLift 1817959
  have htrace : WordTrace (prefixWord ++ tailWord_1817959) baseStart_1817959 baseEnd_1817959 := by
    simpa [prefixWord, tailWord_1817959, baseEnd_1817959] using wordTrace_append hprefix tailTrace_1817959
  have hstable : (prefixWord ++ tailWord_1817959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817959).length < 2 ^ (prefixWord ++ tailWord_1817959).sum := by decide
  have hdescent : baseEnd_1817959 < baseStart_1817959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817975 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 4, 4]
def baseStart_1817975 : Nat := 118140960795 + 1817975 * 2 ^ 59
def prefixEnd_1817975 : Nat := 4983230072969 + 3 ^ 40 * 1817975 * 2
def baseEnd_1817975 : Nat := 311164997619209966050597

theorem tailTrace_1817975 : CollatzResearch.WordTrace tailWord_1817975 prefixEnd_1817975 311164997619209966050597 := by
  unfold tailWord_1817975
  simp only [CollatzResearch.WordTrace]
  refine ⟨66306995588794535256103379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44204663725863023504068919 66306995588794535256103379)
  ·
    refine ⟨99460493383191802884155069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66306995588794535256103379 99460493383191802884155069)
    ·
      refine ⟨37297685018696926081558151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99460493383191802884155069 37297685018696926081558151)
      ·
        refine ⟨55946527528045389122337227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37297685018696926081558151 55946527528045389122337227)
        ·
          refine ⟨83919791292068083683505841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55946527528045389122337227 83919791292068083683505841)
          ·
            refine ⟨62939843469051062762629381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83919791292068083683505841 62939843469051062762629381)
            ·
              refine ⟨11801220650447074267993009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62939843469051062762629381 11801220650447074267993009)
              ·
                refine ⟨8850915487835305700994757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11801220650447074267993009 8850915487835305700994757)
                ·
                  refine ⟨1659546653969119818936517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8850915487835305700994757 1659546653969119818936517)
                  ·
                    refine ⟨311164997619209966050597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1659546653969119818936517 311164997619209966050597)
                    ·
                      rfl

theorem cell23_1817975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_1817975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817975 prefixEnd_1817975 := by exact prefixLift 1817975
  have htrace : WordTrace (prefixWord ++ tailWord_1817975) baseStart_1817975 baseEnd_1817975 := by
    simpa [prefixWord, tailWord_1817975, baseEnd_1817975] using wordTrace_append hprefix tailTrace_1817975
  have hstable : (prefixWord ++ tailWord_1817975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817975).length < 2 ^ (prefixWord ++ tailWord_1817975).sum := by decide
  have hdescent : baseEnd_1817975 < baseStart_1817975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817992 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 4, 4]
def baseStart_1817992 : Nat := 118140960795 + 1817992 * 2 ^ 59
def prefixEnd_1817992 : Nat := 4983230072969 + 3 ^ 40 * 1817992 * 2
def baseEnd_1817992 : Nat := 311167907342918777213071

theorem tailTrace_1817992 : CollatzResearch.WordTrace tailWord_1817992 prefixEnd_1817992 311167907342918777213071 := by
  unfold tailWord_1817992
  simp only [CollatzResearch.WordTrace]
  refine ⟨33153807814866473579736115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44205077086488631439648153 33153807814866473579736115)
  ·
    refine ⟨49730711722299710369604173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33153807814866473579736115 49730711722299710369604173)
    ·
      refine ⟨18649016895862391388601565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49730711722299710369604173 18649016895862391388601565)
      ·
        refine ⟨6993381335948396770725587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18649016895862391388601565 6993381335948396770725587)
        ·
          refine ⟨10490072003922595156088381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993381335948396770725587 10490072003922595156088381)
          ·
            refine ⟨3933777001470973183533143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10490072003922595156088381 3933777001470973183533143)
            ·
              refine ⟨5900665502206459775299715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933777001470973183533143 5900665502206459775299715)
              ·
                refine ⟨8850998253309689662949573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900665502206459775299715 8850998253309689662949573)
                ·
                  refine ⟨1659562172495566811803045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8850998253309689662949573 1659562172495566811803045)
                  ·
                    refine ⟨311167907342918777213071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1659562172495566811803045 311167907342918777213071)
                    ·
                      rfl

theorem cell23_1817992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_1817992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1817992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1817992 prefixEnd_1817992 := by exact prefixLift 1817992
  have htrace : WordTrace (prefixWord ++ tailWord_1817992) baseStart_1817992 baseEnd_1817992 := by
    simpa [prefixWord, tailWord_1817992, baseEnd_1817992] using wordTrace_append hprefix tailTrace_1817992
  have hstable : (prefixWord ++ tailWord_1817992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817992).length < 2 ^ (prefixWord ++ tailWord_1817992).sum := by decide
  have hdescent : baseEnd_1817992 < baseStart_1817992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818009 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 2, 4]
def baseStart_1818009 : Nat := 118140960795 + 1818009 * 2 ^ 59
def prefixEnd_1818009 : Nat := 4983230072969 + 3 ^ 40 * 1818009 * 2
def baseEnd_1818009 : Nat := 311170817066627588375545

theorem tailTrace_1818009 : CollatzResearch.WordTrace tailWord_1818009 prefixEnd_1818009 311170817066627588375545 := by
  unfold tailWord_1818009
  simp only [CollatzResearch.WordTrace]
  refine ⟨66308235670671359062841081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44205490447114239375227387 66308235670671359062841081)
  ·
    refine ⟨49731176753003519297130811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66308235670671359062841081 49731176753003519297130811)
    ·
      refine ⟨74596765129505278945696217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49731176753003519297130811 74596765129505278945696217)
      ·
        refine ⟨55947573847128959209272163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74596765129505278945696217 55947573847128959209272163)
        ·
          refine ⟨83921360770693438813908245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55947573847128959209272163 83921360770693438813908245)
          ·
            refine ⟨3933813786126254944401949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83921360770693438813908245 3933813786126254944401949)
            ·
              refine ⟨1475180169797345604150731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3933813786126254944401949 1475180169797345604150731)
              ·
                refine ⟨2212770254696018406226097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475180169797345604150731 2212770254696018406226097)
                ·
                  refine ⟨1659577691022013804669573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2212770254696018406226097 1659577691022013804669573)
                  ·
                    refine ⟨311170817066627588375545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1659577691022013804669573 311170817066627588375545)
                    ·
                      rfl

theorem cell23_1818009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 4].length) (baseStart_1818009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818009 prefixEnd_1818009 := by exact prefixLift 1818009
  have htrace : WordTrace (prefixWord ++ tailWord_1818009) baseStart_1818009 baseEnd_1818009 := by
    simpa [prefixWord, tailWord_1818009, baseEnd_1818009] using wordTrace_append hprefix tailTrace_1818009
  have hstable : (prefixWord ++ tailWord_1818009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818009).length < 2 ^ (prefixWord ++ tailWord_1818009).sum := by decide
  have hdescent : baseEnd_1818009 < baseStart_1818009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818042 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2]
def baseStart_1818042 : Nat := 118140960795 + 1818042 * 2 ^ 59
def prefixEnd_1818042 : Nat := 4983230072969 + 3 ^ 40 * 1818042 * 2
def baseEnd_1818042 : Nat := 933529396061481136013983

theorem tailTrace_1818042 : CollatzResearch.WordTrace tailWord_1818042 prefixEnd_1818042 933529396061481136013983 := by
  unfold tailWord_1818042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16577359819887951424698095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44206292853034537132528253 16577359819887951424698095)
  ·
    refine ⟨24866039729831927137047143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16577359819887951424698095 24866039729831927137047143)
    ·
      refine ⟨37299059594747890705570715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24866039729831927137047143 37299059594747890705570715)
      ·
        refine ⟨55948589392121836058356073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37299059594747890705570715 55948589392121836058356073)
        ·
          refine ⟨41961442044091377043767055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55948589392121836058356073 41961442044091377043767055)
          ·
            refine ⟨62942163066137065565650583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41961442044091377043767055 62942163066137065565650583)
            ·
              refine ⟨94413244599205598348475875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62942163066137065565650583 94413244599205598348475875)
              ·
                refine ⟨141619866898808397522713813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94413244599205598348475875 141619866898808397522713813)
                ·
                  refine ⟨3319215630440821816938605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 141619866898808397522713813 3319215630440821816938605)
                  ·
                    refine ⟨1244705861415308181351977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319215630440821816938605 1244705861415308181351977)
                    ·
                      refine ⟨933529396061481136013983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244705861415308181351977 933529396061481136013983)
                      ·
                        rfl

theorem cell23_1818042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_1818042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818042 prefixEnd_1818042 := by exact prefixLift 1818042
  have htrace : WordTrace (prefixWord ++ tailWord_1818042) baseStart_1818042 baseEnd_1818042 := by
    simpa [prefixWord, tailWord_1818042, baseEnd_1818042] using wordTrace_append hprefix tailTrace_1818042
  have hstable : (prefixWord ++ tailWord_1818042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818042).length < 2 ^ (prefixWord ++ tailWord_1818042).sum := by decide
  have hdescent : baseEnd_1818042 < baseStart_1818042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818045 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1818045 : Nat := 118140960795 + 1818045 * 2 ^ 59
def prefixEnd_1818045 : Nat := 4983230072969 + 3 ^ 40 * 1818045 * 2
def baseEnd_1818045 : Nat := 933530936503444624276469

theorem tailTrace_1818045 : CollatzResearch.WordTrace tailWord_1818045 prefixEnd_1818045 933530936503444624276469 := by
  unfold tailWord_1818045
  simp only [CollatzResearch.WordTrace]
  refine ⟨66309548698540937211151589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44206365799027291474101059 66309548698540937211151589)
  ·
    refine ⟨12433040380976425727090923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66309548698540937211151589 12433040380976425727090923)
    ·
      refine ⟨18649560571464638590636385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12433040380976425727090923 18649560571464638590636385)
      ·
        refine ⟨13987170428598478942977289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18649560571464638590636385 13987170428598478942977289)
        ·
          refine ⟨10490377821448859207232967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13987170428598478942977289 10490377821448859207232967)
          ·
            refine ⟨15735566732173288810849451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10490377821448859207232967 15735566732173288810849451)
            ·
              refine ⟨23603350098259933216274177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15735566732173288810849451 23603350098259933216274177)
              ·
                refine ⟨17702512573694949912205633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23603350098259933216274177 17702512573694949912205633)
                ·
                  refine ⟨13276884430271212434154225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17702512573694949912205633 13276884430271212434154225)
                  ·
                    refine ⟨9957663322703409325615669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13276884430271212434154225 9957663322703409325615669)
                    ·
                      refine ⟨933530936503444624276469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9957663322703409325615669 933530936503444624276469)
                      ·
                        rfl

theorem cell23_1818045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1818045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818045 prefixEnd_1818045 := by exact prefixLift 1818045
  have htrace : WordTrace (prefixWord ++ tailWord_1818045) baseStart_1818045 baseEnd_1818045 := by
    simpa [prefixWord, tailWord_1818045, baseEnd_1818045] using wordTrace_append hprefix tailTrace_1818045
  have hstable : (prefixWord ++ tailWord_1818045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818045).length < 2 ^ (prefixWord ++ tailWord_1818045).sum := by decide
  have hdescent : baseEnd_1818045 < baseStart_1818045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818055 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1818055 : Nat := 118140960795 + 1818055 * 2 ^ 59
def prefixEnd_1818055 : Nat := 4983230072969 + 3 ^ 40 * 1818055 * 2
def baseEnd_1818055 : Nat := 933536071309989585151423

theorem tailTrace_1818055 : CollatzResearch.WordTrace tailWord_1818055 prefixEnd_1818055 933536071309989585151423 := by
  unfold tailWord_1818055
  simp only [CollatzResearch.WordTrace]
  refine ⟨66309913428504708919015619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44206608952336472612677079 66309913428504708919015619)
  ·
    refine ⟨99464870142757063378523429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66309913428504708919015619 99464870142757063378523429)
    ·
      refine ⟨18649663151766949383473143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99464870142757063378523429 18649663151766949383473143)
      ·
        refine ⟨27974494727650424075209715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18649663151766949383473143 27974494727650424075209715)
        ·
          refine ⟨41961742091475636112814573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27974494727650424075209715 41961742091475636112814573)
          ·
            refine ⟨15735653284303363542305465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41961742091475636112814573 15735653284303363542305465)
            ·
              refine ⟨11801739963227522656729099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15735653284303363542305465 11801739963227522656729099)
              ·
                refine ⟨17702609944841283985093649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11801739963227522656729099 17702609944841283985093649)
                ·
                  refine ⟨13276957458630962988820237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17702609944841283985093649 13276957458630962988820237)
                  ·
                    refine ⟨4978859046986611120807589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13276957458630962988820237 4978859046986611120807589)
                    ·
                      refine ⟨933536071309989585151423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4978859046986611120807589 933536071309989585151423)
                      ·
                        rfl

theorem cell23_1818055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1818055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818055 prefixEnd_1818055 := by exact prefixLift 1818055
  have htrace : WordTrace (prefixWord ++ tailWord_1818055) baseStart_1818055 baseEnd_1818055 := by
    simpa [prefixWord, tailWord_1818055, baseEnd_1818055] using wordTrace_append hprefix tailTrace_1818055
  have hstable : (prefixWord ++ tailWord_1818055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818055).length < 2 ^ (prefixWord ++ tailWord_1818055).sum := by decide
  have hdescent : baseEnd_1818055 < baseStart_1818055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818106 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2]
def baseStart_1818106 : Nat := 118140960795 + 1818106 * 2 ^ 59
def prefixEnd_1818106 : Nat := 4983230072969 + 3 ^ 40 * 1818106 * 2
def baseEnd_1818106 : Nat := 933562258823368885613689

theorem tailTrace_1818106 : CollatzResearch.WordTrace tailWord_1818106 prefixEnd_1818106 933562258823368885613689 := by
  unfold tailWord_1818106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16577943387829986157280543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44207849034213296419414781 16577943387829986157280543)
  ·
    refine ⟨24866915081744979235920815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16577943387829986157280543 24866915081744979235920815)
    ·
      refine ⟨37300372622617468853881223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24866915081744979235920815 37300372622617468853881223)
      ·
        refine ⟨55950558933926203280821835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37300372622617468853881223 55950558933926203280821835)
        ·
          refine ⟨83925838400889304921232753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55950558933926203280821835 83925838400889304921232753)
          ·
            refine ⟨62944378800666978690924565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83925838400889304921232753 62944378800666978690924565)
            ·
              refine ⟨2950517756281264626137089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62944378800666978690924565 2950517756281264626137089)
              ·
                refine ⟨2212888317210948469602817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950517756281264626137089 2212888317210948469602817)
                ·
                  refine ⟨1659666237908211352202113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2212888317210948469602817 1659666237908211352202113)
                  ·
                    refine ⟨1244749678431158514151585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1659666237908211352202113 1244749678431158514151585)
                    ·
                      refine ⟨933562258823368885613689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244749678431158514151585 933562258823368885613689)
                      ·
                        rfl

theorem cell23_1818106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_1818106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818106 prefixEnd_1818106 := by exact prefixLift 1818106
  have htrace : WordTrace (prefixWord ++ tailWord_1818106) baseStart_1818106 baseEnd_1818106 := by
    simpa [prefixWord, tailWord_1818106, baseEnd_1818106] using wordTrace_append hprefix tailTrace_1818106
  have hstable : (prefixWord ++ tailWord_1818106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818106).length < 2 ^ (prefixWord ++ tailWord_1818106).sum := by decide
  have hdescent : baseEnd_1818106 < baseStart_1818106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818122 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_1818122 : Nat := 118140960795 + 1818122 * 2 ^ 59
def prefixEnd_1818122 : Nat := 4983230072969 + 3 ^ 40 * 1818122 * 2
def baseEnd_1818122 : Nat := 933570474513840823013615

theorem tailTrace_1818122 : CollatzResearch.WordTrace tailWord_1818122 prefixEnd_1818122 933570474513840823013615 := by
  unfold tailWord_1818122
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578089279815494840426155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44208238079507986241136413 16578089279815494840426155)
  ·
    refine ⟨24867133919723242260639233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16578089279815494840426155 24867133919723242260639233)
    ·
      refine ⟨18650350439792431695479425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24867133919723242260639233 18650350439792431695479425)
      ·
        refine ⟨13987762829844323771609569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18650350439792431695479425 13987762829844323771609569)
        ·
          refine ⟨10490822122383242828707177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13987762829844323771609569 10490822122383242828707177)
          ·
            refine ⟨7868116591787432121530383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10490822122383242828707177 7868116591787432121530383)
            ·
              refine ⟨11802174887681148182295575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868116591787432121530383 11802174887681148182295575)
              ·
                refine ⟨17703262331521722273443363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11802174887681148182295575 17703262331521722273443363)
                ·
                  refine ⟨26554893497282583410165045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17703262331521722273443363 26554893497282583410165045)
                  ·
                    refine ⟨2489521265370242194702973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26554893497282583410165045 2489521265370242194702973)
                    ·
                      refine ⟨933570474513840823013615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2489521265370242194702973 933570474513840823013615)
                      ·
                        rfl

theorem cell23_1818122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_1818122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818122 prefixEnd_1818122 := by exact prefixLift 1818122
  have htrace : WordTrace (prefixWord ++ tailWord_1818122) baseStart_1818122 baseEnd_1818122 := by
    simpa [prefixWord, tailWord_1818122, baseEnd_1818122] using wordTrace_append hprefix tailTrace_1818122
  have hstable : (prefixWord ++ tailWord_1818122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818122).length < 2 ^ (prefixWord ++ tailWord_1818122).sum := by decide
  have hdescent : baseEnd_1818122 < baseStart_1818122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818162 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1818162 : Nat := 118140960795 + 1818162 * 2 ^ 59
def prefixEnd_1818162 : Nat := 4983230072969 + 3 ^ 40 * 1818162 * 2
def baseEnd_1818162 : Nat := 933591013740020666513431

theorem tailTrace_1818162 : CollatzResearch.WordTrace tailWord_1818162 prefixEnd_1818162 933591013740020666513431 := by
  unfold tailWord_1818162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578454009779266548290185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44209210692744710795440493 16578454009779266548290185)
  ·
    refine ⟨12433840507334449911217639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16578454009779266548290185 12433840507334449911217639)
    ·
      refine ⟨18650760761001674866826459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12433840507334449911217639 18650760761001674866826459)
      ·
        refine ⟨27976141141502512300239689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18650760761001674866826459 27976141141502512300239689)
        ·
          refine ⟨20982105856126884225179767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27976141141502512300239689 20982105856126884225179767)
          ·
            refine ⟨31473158784190326337769651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20982105856126884225179767 31473158784190326337769651)
            ·
              refine ⟨47209738176285489506654477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31473158784190326337769651 47209738176285489506654477)
              ·
                refine ⟨17703651816107058564995429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47209738176285489506654477 17703651816107058564995429)
                ·
                  refine ⟨3319434715520073480936643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17703651816107058564995429 3319434715520073480936643)
                  ·
                    refine ⟨4979152073280110221404965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3319434715520073480936643 4979152073280110221404965)
                    ·
                      refine ⟨933591013740020666513431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4979152073280110221404965 933591013740020666513431)
                      ·
                        rfl

theorem cell23_1818162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1818162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818162 prefixEnd_1818162 := by exact prefixLift 1818162
  have htrace : WordTrace (prefixWord ++ tailWord_1818162) baseStart_1818162 baseEnd_1818162 := by
    simpa [prefixWord, tailWord_1818162, baseEnd_1818162] using wordTrace_append hprefix tailTrace_1818162
  have hstable : (prefixWord ++ tailWord_1818162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818162).length < 2 ^ (prefixWord ++ tailWord_1818162).sum := by decide
  have hdescent : baseEnd_1818162 < baseStart_1818162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818216 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1818216 : Nat := 118140960795 + 1818216 * 2 ^ 59
def prefixEnd_1818216 : Nat := 4983230072969 + 3 ^ 40 * 1818216 * 2
def baseEnd_1818216 : Nat := 933618741695363455238183

theorem tailTrace_1818216 : CollatzResearch.WordTrace tailWord_1818216 prefixEnd_1818216 933618741695363455238183 := by
  unfold tailWord_1818216
  simp only [CollatzResearch.WordTrace]
  refine ⟨33157892790460716707813251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44210523720614288943751001 33157892790460716707813251)
  ·
    refine ⟨49736839185691075061719877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33157892790460716707813251 49736839185691075061719877)
    ·
      refine ⟨9325657347317076574072477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49736839185691075061719877 9325657347317076574072477)
      ·
        refine ⟨3497121505243903715277179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9325657347317076574072477 3497121505243903715277179)
        ·
          refine ⟨5245682257865855572915769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497121505243903715277179 5245682257865855572915769)
          ·
            refine ⟨3934261693399391679686827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5245682257865855572915769 3934261693399391679686827)
            ·
              refine ⟨5901392540099087519530241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934261693399391679686827 5901392540099087519530241)
              ·
                refine ⟨4426044405074315639647681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901392540099087519530241 4426044405074315639647681)
                ·
                  refine ⟨3319533303805736729735761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4426044405074315639647681 3319533303805736729735761)
                  ·
                    refine ⟨2489649977854302547301821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3319533303805736729735761 2489649977854302547301821)
                    ·
                      refine ⟨933618741695363455238183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2489649977854302547301821 933618741695363455238183)
                      ·
                        rfl

theorem cell23_1818216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1818216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818216 prefixEnd_1818216 := by exact prefixLift 1818216
  have htrace : WordTrace (prefixWord ++ tailWord_1818216) baseStart_1818216 baseEnd_1818216 := by
    simpa [prefixWord, tailWord_1818216, baseEnd_1818216] using wordTrace_append hprefix tailTrace_1818216
  have hstable : (prefixWord ++ tailWord_1818216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818216).length < 2 ^ (prefixWord ++ tailWord_1818216).sum := by decide
  have hdescent : baseEnd_1818216 < baseStart_1818216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818249 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 1, 5]
def baseStart_1818249 : Nat := 118140960795 + 1818249 * 2 ^ 59
def prefixEnd_1818249 : Nat := 4983230072969 + 3 ^ 40 * 1818249 * 2
def baseEnd_1818249 : Nat := 311211895518987275375177

theorem tailTrace_1818249 : CollatzResearch.WordTrace tailWord_1818249 prefixEnd_1818249 311211895518987275375177 := by
  unfold tailWord_1818249
  simp only [CollatzResearch.WordTrace]
  refine ⟨66316989189801880051577801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44211326126534586701051867 66316989189801880051577801)
  ·
    refine ⟨49737741892351410038683351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66316989189801880051577801 49737741892351410038683351)
    ·
      refine ⟨74606612838527115058025027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49737741892351410038683351 74606612838527115058025027)
      ·
        refine ⟨111909919257790672587037541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74606612838527115058025027 111909919257790672587037541)
        ·
          refine ⟨20983109860835751110069539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111909919257790672587037541 20983109860835751110069539)
          ·
            refine ⟨31474664791253626665104309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20983109860835751110069539 31474664791253626665104309)
            ·
              refine ⟨2950749824180027499853529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31474664791253626665104309 2950749824180027499853529)
              ·
                refine ⟨2213062368135020624890147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950749824180027499853529 2213062368135020624890147)
                ·
                  refine ⟨3319593552202530937335221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213062368135020624890147 3319593552202530937335221)
                  ·
                    refine ⟨311211895518987275375177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3319593552202530937335221 311211895518987275375177)
                    ·
                      rfl

theorem cell23_1818249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_1818249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818249 prefixEnd_1818249 := by exact prefixLift 1818249
  have htrace : WordTrace (prefixWord ++ tailWord_1818249) baseStart_1818249 baseEnd_1818249 := by
    simpa [prefixWord, tailWord_1818249, baseEnd_1818249] using wordTrace_append hprefix tailTrace_1818249
  have hstable : (prefixWord ++ tailWord_1818249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818249).length < 2 ^ (prefixWord ++ tailWord_1818249).sum := by decide
  have hdescent : baseEnd_1818249 < baseStart_1818249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818274 : List Nat := [3, 3, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_1818274 : Nat := 118140960795 + 1818274 * 2 ^ 59
def prefixEnd_1818274 : Nat := 4983230072969 + 3 ^ 40 * 1818274 * 2
def baseEnd_1818274 : Nat := 311216174524441409437639

theorem tailTrace_1818274 : CollatzResearch.WordTrace tailWord_1818274 prefixEnd_1818274 311216174524441409437639 := by
  unfold tailWord_1818274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579475253677827330309469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44211934009807539547491917 16579475253677827330309469)
  ·
    refine ⟨6217303220129185248866051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16579475253677827330309469 6217303220129185248866051)
    ·
      refine ⟨9325954830193777873299077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6217303220129185248866051 9325954830193777873299077)
      ·
        refine ⟨1748616530661333351243577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9325954830193777873299077 1748616530661333351243577)
        ·
          refine ⟨1311462397996000013432683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748616530661333351243577 1311462397996000013432683)
          ·
            refine ⟨1967193596994000020149025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311462397996000013432683 1967193596994000020149025)
            ·
              refine ⟨1475395197745500015111769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967193596994000020149025 1475395197745500015111769)
              ·
                refine ⟨1106546398309125011333827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475395197745500015111769 1106546398309125011333827)
                ·
                  refine ⟨1659819597463687517000741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106546398309125011333827 1659819597463687517000741)
                  ·
                    refine ⟨311216174524441409437639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1659819597463687517000741 311216174524441409437639)
                    ·
                      rfl

theorem cell23_1818274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_1818274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818274 prefixEnd_1818274 := by exact prefixLift 1818274
  have htrace : WordTrace (prefixWord ++ tailWord_1818274) baseStart_1818274 baseEnd_1818274 := by
    simpa [prefixWord, tailWord_1818274, baseEnd_1818274] using wordTrace_append hprefix tailTrace_1818274
  have hstable : (prefixWord ++ tailWord_1818274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818274).length < 2 ^ (prefixWord ++ tailWord_1818274).sum := by decide
  have hdescent : baseEnd_1818274 < baseStart_1818274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818346 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_1818346 : Nat := 118140960795 + 1818346 * 2 ^ 59
def prefixEnd_1818346 : Nat := 4983230072969 + 3 ^ 40 * 1818346 * 2
def baseEnd_1818346 : Nat := 933685494180447946612585

theorem tailTrace_1818346 : CollatzResearch.WordTrace tailWord_1818346 prefixEnd_1818346 933685494180447946612585 := by
  unfold tailWord_1818346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16580131767612616404464723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44213684713633643745239261 16580131767612616404464723)
  ·
    refine ⟨24870197651418924606697085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16580131767612616404464723 24870197651418924606697085)
    ·
      refine ⟨9326324119282096727511407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24870197651418924606697085 9326324119282096727511407)
      ·
        refine ⟨13989486178923145091267111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9326324119282096727511407 13989486178923145091267111)
        ·
          refine ⟨20984229268384717636900667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13989486178923145091267111 20984229268384717636900667)
          ·
            refine ⟨31476343902577076455351001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20984229268384717636900667 31476343902577076455351001)
            ·
              refine ⟨23607257926932807341513251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31476343902577076455351001 23607257926932807341513251)
              ·
                refine ⟨35410886890399211012269877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23607257926932807341513251 35410886890399211012269877)
                ·
                  refine ⟨3319770645974926032400301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35410886890399211012269877 3319770645974926032400301)
                  ·
                    refine ⟨1244913992240597262150113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319770645974926032400301 1244913992240597262150113)
                    ·
                      refine ⟨933685494180447946612585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244913992240597262150113 933685494180447946612585)
                      ·
                        rfl

theorem cell23_1818346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_1818346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818346 prefixEnd_1818346 := by exact prefixLift 1818346
  have htrace : WordTrace (prefixWord ++ tailWord_1818346) baseStart_1818346 baseEnd_1818346 := by
    simpa [prefixWord, tailWord_1818346, baseEnd_1818346] using wordTrace_append hprefix tailTrace_1818346
  have hstable : (prefixWord ++ tailWord_1818346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818346).length < 2 ^ (prefixWord ++ tailWord_1818346).sum := by decide
  have hdescent : baseEnd_1818346 < baseStart_1818346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818352 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 1, 8]
def baseStart_1818352 : Nat := 118140960795 + 1818352 * 2 ^ 59
def prefixEnd_1818352 : Nat := 4983230072969 + 3 ^ 40 * 1818352 * 2
def baseEnd_1818352 : Nat := 311229525021458307712519

theorem tailTrace_1818352 : CollatzResearch.WordTrace tailWord_1818352 prefixEnd_1818352 311229525021458307712519 := by
  unfold tailWord_1818352
  simp only [CollatzResearch.WordTrace]
  refine ⟨33160372954214364321288655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44213830605619152428384873 33160372954214364321288655)
  ·
    refine ⟨49740559431321546481932983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33160372954214364321288655 49740559431321546481932983)
    ·
      refine ⟨74610839146982319722899475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49740559431321546481932983 74610839146982319722899475)
      ·
        refine ⟨111916258720473479584349213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74610839146982319722899475 111916258720473479584349213)
        ·
          refine ⟨41968597020177554844130955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111916258720473479584349213 41968597020177554844130955)
          ·
            refine ⟨62952895530266332266196433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41968597020177554844130955 62952895530266332266196433)
            ·
              refine ⟨47214671647699749199647325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62952895530266332266196433 47214671647699749199647325)
              ·
                refine ⟨17705501867887405949867747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47214671647699749199647325 17705501867887405949867747)
                ·
                  refine ⟨26558252801831108924801621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17705501867887405949867747 26558252801831108924801621)
                  ·
                    refine ⟨311229525021458307712519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26558252801831108924801621 311229525021458307712519)
                    ·
                      rfl

theorem cell23_1818352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_1818352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818352 prefixEnd_1818352 := by exact prefixLift 1818352
  have htrace : WordTrace (prefixWord ++ tailWord_1818352) baseStart_1818352 baseEnd_1818352 := by
    simpa [prefixWord, tailWord_1818352, baseEnd_1818352] using wordTrace_append hprefix tailTrace_1818352
  have hstable : (prefixWord ++ tailWord_1818352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818352).length < 2 ^ (prefixWord ++ tailWord_1818352).sum := by decide
  have hdescent : baseEnd_1818352 < baseStart_1818352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818374 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1818374 : Nat := 118140960795 + 1818374 * 2 ^ 59
def prefixEnd_1818374 : Nat := 4983230072969 + 3 ^ 40 * 1818374 * 2
def baseEnd_1818374 : Nat := 933699871638773837062457

theorem tailTrace_1818374 : CollatzResearch.WordTrace tailWord_1818374 prefixEnd_1818374 933699871638773837062457 := by
  unfold tailWord_1818374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072548384823407074996193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44214365542899350933252117 2072548384823407074996193)
  ·
    refine ⟨1554411288617555306247145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2072548384823407074996193 1554411288617555306247145)
    ·
      refine ⟨1165808466463166479685359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1554411288617555306247145 1165808466463166479685359)
      ·
        refine ⟨1748712699694749719528039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165808466463166479685359 1748712699694749719528039)
        ·
          refine ⟨2623069049542124579292059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748712699694749719528039 2623069049542124579292059)
          ·
            refine ⟨3934603574313186868938089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623069049542124579292059 3934603574313186868938089)
            ·
              refine ⟨2950952680734890151703567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934603574313186868938089 2950952680734890151703567)
              ·
                refine ⟨4426429021102335227555351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950952680734890151703567 4426429021102335227555351)
                ·
                  refine ⟨6639643531653502841333027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426429021102335227555351 6639643531653502841333027)
                  ·
                    refine ⟨9959465297480254261999541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6639643531653502841333027 9959465297480254261999541)
                    ·
                      refine ⟨933699871638773837062457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9959465297480254261999541 933699871638773837062457)
                      ·
                        rfl

theorem cell23_1818374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1818374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818374 prefixEnd_1818374 := by exact prefixLift 1818374
  have htrace : WordTrace (prefixWord ++ tailWord_1818374) baseStart_1818374 baseEnd_1818374 := by
    simpa [prefixWord, tailWord_1818374, baseEnd_1818374] using wordTrace_append hprefix tailTrace_1818374
  have hstable : (prefixWord ++ tailWord_1818374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818374).length < 2 ^ (prefixWord ++ tailWord_1818374).sum := by decide
  have hdescent : baseEnd_1818374 < baseStart_1818374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818376 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_1818376 : Nat := 118140960795 + 1818376 * 2 ^ 59
def prefixEnd_1818376 : Nat := 4983230072969 + 3 ^ 40 * 1818376 * 2
def baseEnd_1818376 : Nat := 933700898600082829237447

theorem tailTrace_1818376 : CollatzResearch.WordTrace tailWord_1818376 prefixEnd_1818376 933700898600082829237447 := by
  unfold tailWord_1818376
  simp only [CollatzResearch.WordTrace]
  refine ⟨33160810630170890370725491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44214414173561187160967321 33160810630170890370725491)
  ·
    refine ⟨49741215945256335556088237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33160810630170890370725491 49741215945256335556088237)
    ·
      refine ⟨18652955979471125833533089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49741215945256335556088237 18652955979471125833533089)
      ·
        refine ⟨13989716984603344375149817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18652955979471125833533089 13989716984603344375149817)
        ·
          refine ⟨10492287738452508281362363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13989716984603344375149817 10492287738452508281362363)
          ·
            refine ⟨15738431607678762422043545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492287738452508281362363 15738431607678762422043545)
            ·
              refine ⟨11803823705759071816532659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15738431607678762422043545 11803823705759071816532659)
              ·
                refine ⟨17705735558638607724798989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11803823705759071816532659 17705735558638607724798989)
                ·
                  refine ⟨6639650834489477896799621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17705735558638607724798989 6639650834489477896799621)
                  ·
                    refine ⟨1244934531466777105649929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6639650834489477896799621 1244934531466777105649929)
                    ·
                      refine ⟨933700898600082829237447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244934531466777105649929 933700898600082829237447)
                      ·
                        rfl

theorem cell23_1818376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_1818376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818376 prefixEnd_1818376 := by exact prefixLift 1818376
  have htrace : WordTrace (prefixWord ++ tailWord_1818376) baseStart_1818376 baseEnd_1818376 := by
    simpa [prefixWord, tailWord_1818376, baseEnd_1818376] using wordTrace_append hprefix tailTrace_1818376
  have hstable : (prefixWord ++ tailWord_1818376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818376).length < 2 ^ (prefixWord ++ tailWord_1818376).sum := by decide
  have hdescent : baseEnd_1818376 < baseStart_1818376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818388 : List Nat := [2, 4, 4, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1818388 : Nat := 118140960795 + 1818388 * 2 ^ 59
def prefixEnd_1818388 : Nat := 4983230072969 + 3 ^ 40 * 1818388 * 2
def baseEnd_1818388 : Nat := 933707060367936782287393

theorem tailTrace_1818388 : CollatzResearch.WordTrace tailWord_1818388 prefixEnd_1818388 933707060367936782287393 := by
  unfold tailWord_1818388
  simp only [CollatzResearch.WordTrace]
  refine ⟨33161029468149153395443909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44214705957532204527258545 33161029468149153395443909)
  ·
    refine ⟨6217693025277966261645733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33161029468149153395443909 6217693025277966261645733)
    ·
      refine ⟨1165817442239618674058575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6217693025277966261645733 1165817442239618674058575)
      ·
        refine ⟨1748726163359428011087863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165817442239618674058575 1748726163359428011087863)
        ·
          refine ⟨2623089245039142016631795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748726163359428011087863 2623089245039142016631795)
          ·
            refine ⟨3934633867558713024947693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623089245039142016631795 3934633867558713024947693)
            ·
              refine ⟨1475487700334517384355385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3934633867558713024947693 1475487700334517384355385)
              ·
                refine ⟨1106615775250888038266539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475487700334517384355385 1106615775250888038266539)
                ·
                  refine ⟨1659923662876332057399809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106615775250888038266539 1659923662876332057399809)
                  ·
                    refine ⟨1244942747157249043049857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1659923662876332057399809 1244942747157249043049857)
                    ·
                      refine ⟨933707060367936782287393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244942747157249043049857 933707060367936782287393)
                      ·
                        rfl

theorem cell23_1818388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1818388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818388 prefixEnd_1818388 := by exact prefixLift 1818388
  have htrace : WordTrace (prefixWord ++ tailWord_1818388) baseStart_1818388 baseEnd_1818388 := by
    simpa [prefixWord, tailWord_1818388, baseEnd_1818388] using wordTrace_append hprefix tailTrace_1818388
  have hstable : (prefixWord ++ tailWord_1818388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818388).length < 2 ^ (prefixWord ++ tailWord_1818388).sum := by decide
  have hdescent : baseEnd_1818388 < baseStart_1818388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818414 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1818414 : Nat := 118140960795 + 1818414 * 2 ^ 59
def prefixEnd_1818414 : Nat := 4983230072969 + 3 ^ 40 * 1818414 * 2
def baseEnd_1818414 : Nat := 933720410864953680562273

theorem tailTrace_1818414 : CollatzResearch.WordTrace tailWord_1818414 prefixEnd_1818414 933720410864953680562273 := by
  unfold tailWord_1818414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290375904275514153916787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44215338156136075487556197 8290375904275514153916787)
  ·
    refine ⟨12435563856413271230875181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8290375904275514153916787 12435563856413271230875181)
    ·
      refine ⟨4663336446154976711578193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12435563856413271230875181 4663336446154976711578193)
      ·
        refine ⟨3497502334616232533683645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4663336446154976711578193 3497502334616232533683645)
        ·
          refine ⟨1311563375481087200131367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3497502334616232533683645 1311563375481087200131367)
          ·
            refine ⟨1967345063221630800197051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311563375481087200131367 1967345063221630800197051)
            ·
              refine ⟨2951017594832446200295577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967345063221630800197051 2951017594832446200295577)
              ·
                refine ⟨2213263196124334650221683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2951017594832446200295577 2213263196124334650221683)
                ·
                  refine ⟨3319894794186501975332525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213263196124334650221683 3319894794186501975332525)
                  ·
                    refine ⟨1244960547819938240749697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319894794186501975332525 1244960547819938240749697)
                    ·
                      refine ⟨933720410864953680562273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1244960547819938240749697 933720410864953680562273)
                      ·
                        rfl

theorem cell23_1818414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1818414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818414 prefixEnd_1818414 := by exact prefixLift 1818414
  have htrace : WordTrace (prefixWord ++ tailWord_1818414) baseStart_1818414 baseEnd_1818414 := by
    simpa [prefixWord, tailWord_1818414, baseEnd_1818414] using wordTrace_append hprefix tailTrace_1818414
  have hstable : (prefixWord ++ tailWord_1818414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818414).length < 2 ^ (prefixWord ++ tailWord_1818414).sum := by decide
  have hdescent : baseEnd_1818414 < baseStart_1818414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818439 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1818439 : Nat := 118140960795 + 1818439 * 2 ^ 59
def prefixEnd_1818439 : Nat := 4983230072969 + 3 ^ 40 * 1818439 * 2
def baseEnd_1818439 : Nat := 933733247881316082749657

theorem tailTrace_1818439 : CollatzResearch.WordTrace tailWord_1818439 prefixEnd_1818439 933733247881316082749657 := by
  unfold tailWord_1818439
  simp only [CollatzResearch.WordTrace]
  refine ⟨66323919059113542500994371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44215946039409028333996247 66323919059113542500994371)
  ·
    refine ⟨99485878588670313751491557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66323919059113542500994371 99485878588670313751491557)
    ·
      refine ⟨18653602235375683828404667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99485878588670313751491557 18653602235375683828404667)
      ·
        refine ⟨27980403353063525742607001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18653602235375683828404667 27980403353063525742607001)
        ·
          refine ⟨20985302514797644306955251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27980403353063525742607001 20985302514797644306955251)
          ·
            refine ⟨31477953772196466460432877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20985302514797644306955251 31477953772196466460432877)
            ·
              refine ⟨11804232664573674922662329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31477953772196466460432877 11804232664573674922662329)
              ·
                refine ⟨8853174498430256191996747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11804232664573674922662329 8853174498430256191996747)
                ·
                  refine ⟨13279761747645384287995121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8853174498430256191996747 13279761747645384287995121)
                  ·
                    refine ⟨9959821310734038215996341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13279761747645384287995121 9959821310734038215996341)
                    ·
                      refine ⟨933733247881316082749657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9959821310734038215996341 933733247881316082749657)
                      ·
                        rfl

theorem cell23_1818439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1818439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818439 prefixEnd_1818439 := by exact prefixLift 1818439
  have htrace : WordTrace (prefixWord ++ tailWord_1818439) baseStart_1818439 baseEnd_1818439 := by
    simpa [prefixWord, tailWord_1818439, baseEnd_1818439] using wordTrace_append hprefix tailTrace_1818439
  have hstable : (prefixWord ++ tailWord_1818439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818439).length < 2 ^ (prefixWord ++ tailWord_1818439).sum := by decide
  have hdescent : baseEnd_1818439 < baseStart_1818439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818450 : List Nat := [3, 2, 2, 1, 1, 5, 2, 2, 5]
def baseStart_1818450 : Nat := 118140960795 + 1818450 * 2 ^ 59
def prefixEnd_1818450 : Nat := 4983230072969 + 3 ^ 40 * 1818450 * 2
def baseEnd_1818450 : Nat := 103748766240946171079123

theorem tailTrace_1818450 : CollatzResearch.WordTrace tailWord_1818450 prefixEnd_1818450 103748766240946171079123 := by
  unfold tailWord_1818450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16581080065518422844911201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44216213508049127586429869 16581080065518422844911201)
  ·
    refine ⟨12435810049138817133683401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16581080065518422844911201 12435810049138817133683401)
    ·
      refine ⟨9326857536854112850262551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12435810049138817133683401 9326857536854112850262551)
      ·
        refine ⟨13990286305281169275393827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9326857536854112850262551 13990286305281169275393827)
        ·
          refine ⟨20985429457921753913090741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13990286305281169275393827 20985429457921753913090741)
          ·
            refine ⟨1967384011680164429352257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20985429457921753913090741 1967384011680164429352257)
            ·
              refine ⟨1475538008760123322014193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967384011680164429352257 1475538008760123322014193)
              ·
                refine ⟨1106653506570092491510645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475538008760123322014193 1106653506570092491510645)
                ·
                  refine ⟨103748766240946171079123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106653506570092491510645 103748766240946171079123)
                  ·
                    rfl

theorem cell23_1818450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_1818450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818450 prefixEnd_1818450 := by exact prefixLift 1818450
  have htrace : WordTrace (prefixWord ++ tailWord_1818450) baseStart_1818450 baseEnd_1818450 := by
    simpa [prefixWord, tailWord_1818450, baseEnd_1818450] using wordTrace_append hprefix tailTrace_1818450
  have hstable : (prefixWord ++ tailWord_1818450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818450).length < 2 ^ (prefixWord ++ tailWord_1818450).sum := by decide
  have hdescent : baseEnd_1818450 < baseStart_1818450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818476 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_1818476 : Nat := 118140960795 + 1818476 * 2 ^ 59
def prefixEnd_1818476 : Nat := 4983230072969 + 3 ^ 40 * 1818476 * 2
def baseEnd_1818476 : Nat := 311250748888510812662329

theorem tailTrace_1818476 : CollatzResearch.WordTrace tailWord_1818476 prefixEnd_1818476 311250748888510812662329 := by
  unfold tailWord_1818476
  simp only [CollatzResearch.WordTrace]
  refine ⟨33162634279989748910045641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44216845706652998546727521 33162634279989748910045641)
  ·
    refine ⟨24871975709992311682534231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33162634279989748910045641 24871975709992311682534231)
    ·
      refine ⟨37307963564988467523801347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24871975709992311682534231 37307963564988467523801347)
      ·
        refine ⟨55961945347482701285702021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37307963564988467523801347 55961945347482701285702021)
        ·
          refine ⟨10492864752653006491069129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55961945347482701285702021 10492864752653006491069129)
          ·
            refine ⟨7869648564489754868301847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10492864752653006491069129 7869648564489754868301847)
            ·
              refine ⟨11804472846734632302452771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869648564489754868301847 11804472846734632302452771)
              ·
                refine ⟨17706709270101948453679157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11804472846734632302452771 17706709270101948453679157)
                ·
                  refine ⟨1660003994072057667532421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17706709270101948453679157 1660003994072057667532421)
                  ·
                    refine ⟨311250748888510812662329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1660003994072057667532421 311250748888510812662329)
                    ·
                      rfl

theorem cell23_1818476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_1818476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818476 prefixEnd_1818476 := by exact prefixLift 1818476
  have htrace : WordTrace (prefixWord ++ tailWord_1818476) baseStart_1818476 baseEnd_1818476 := by
    simpa [prefixWord, tailWord_1818476, baseEnd_1818476] using wordTrace_append hprefix tailTrace_1818476
  have hstable : (prefixWord ++ tailWord_1818476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818476).length < 2 ^ (prefixWord ++ tailWord_1818476).sum := by decide
  have hdescent : baseEnd_1818476 < baseStart_1818476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818489 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 8]
def baseStart_1818489 : Nat := 118140960795 + 1818489 * 2 ^ 59
def prefixEnd_1818489 : Nat := 4983230072969 + 3 ^ 40 * 1818489 * 2
def baseEnd_1818489 : Nat := 103750991323782320791603

theorem tailTrace_1818489 : CollatzResearch.WordTrace tailWord_1818489 prefixEnd_1818489 103750991323782320791603 := by
  unfold tailWord_1818489
  simp only [CollatzResearch.WordTrace]
  refine ⟨66325742708932401040314521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44217161805954934026876347 66325742708932401040314521)
  ·
    refine ⟨49744307031699300780235891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66325742708932401040314521 49744307031699300780235891)
    ·
      refine ⟨74616460547548951170353837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49744307031699300780235891 74616460547548951170353837)
      ·
        refine ⟨27981172705330856688882689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74616460547548951170353837 27981172705330856688882689)
        ·
          refine ⟨20985879528998142516662017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27981172705330856688882689 20985879528998142516662017)
          ·
            refine ⟨15739409646748606887496513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20985879528998142516662017 15739409646748606887496513)
            ·
              refine ⟨11804557235061455165622385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15739409646748606887496513 11804557235061455165622385)
              ·
                refine ⟨8853417926296091374216789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11804557235061455165622385 8853417926296091374216789)
                ·
                  refine ⟨103750991323782320791603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8853417926296091374216789 103750991323782320791603)
                  ·
                    rfl

theorem cell23_1818489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 8].length) (baseStart_1818489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818489 prefixEnd_1818489 := by exact prefixLift 1818489
  have htrace : WordTrace (prefixWord ++ tailWord_1818489) baseStart_1818489 baseEnd_1818489 := by
    simpa [prefixWord, tailWord_1818489, baseEnd_1818489] using wordTrace_append hprefix tailTrace_1818489
  have hstable : (prefixWord ++ tailWord_1818489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818489).length < 2 ^ (prefixWord ++ tailWord_1818489).sum := by decide
  have hdescent : baseEnd_1818489 < baseStart_1818489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818543 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 2, 3, 2]
def baseStart_1818543 : Nat := 118140960795 + 1818543 * 2 ^ 59
def prefixEnd_1818543 : Nat := 4983230072969 + 3 ^ 40 * 1818543 * 2
def baseEnd_1818543 : Nat := 933786649869383675849179

theorem tailTrace_1818543 : CollatzResearch.WordTrace tailWord_1818543 prefixEnd_1818543 933786649869383675849179 := by
  unfold tailWord_1818543
  simp only [CollatzResearch.WordTrace]
  refine ⟨66327712250736768262780283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44218474833824512175186855 66327712250736768262780283)
  ·
    refine ⟨99491568376105152394170425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66327712250736768262780283 99491568376105152394170425)
    ·
      refine ⟨74618676282078864295627819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99491568376105152394170425 74618676282078864295627819)
      ·
        refine ⟨111928014423118296443441729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74618676282078864295627819 111928014423118296443441729)
        ·
          refine ⟨83946010817338722332581297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111928014423118296443441729 83946010817338722332581297)
          ·
            refine ⟨62959508113004041749435973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83946010817338722332581297 62959508113004041749435973)
            ·
              refine ⟨11804907771188257828019245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62959508113004041749435973 11804907771188257828019245)
              ·
                refine ⟨4426840414195596685507217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11804907771188257828019245 4426840414195596685507217)
                ·
                  refine ⟨3320130310646697514130413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4426840414195596685507217 3320130310646697514130413)
                  ·
                    refine ⟨1245048866492511567798905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320130310646697514130413 1245048866492511567798905)
                    ·
                      refine ⟨933786649869383675849179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245048866492511567798905 933786649869383675849179)
                      ·
                        rfl

theorem cell23_1818543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 3, 2].length) (baseStart_1818543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818543 prefixEnd_1818543 := by exact prefixLift 1818543
  have htrace : WordTrace (prefixWord ++ tailWord_1818543) baseStart_1818543 baseEnd_1818543 := by
    simpa [prefixWord, tailWord_1818543, baseEnd_1818543] using wordTrace_append hprefix tailTrace_1818543
  have hstable : (prefixWord ++ tailWord_1818543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818543).length < 2 ^ (prefixWord ++ tailWord_1818543).sum := by decide
  have hdescent : baseEnd_1818543 < baseStart_1818543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818576 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_1818576 : Nat := 118140960795 + 1818576 * 2 ^ 59
def prefixEnd_1818576 : Nat := 4983230072969 + 3 ^ 40 * 1818576 * 2
def baseEnd_1818576 : Nat := 933803594730982046736527

theorem tailTrace_1818576 : CollatzResearch.WordTrace tailWord_1818576 prefixEnd_1818576 933803594730982046736527 := by
  unfold tailWord_1818576
  simp only [CollatzResearch.WordTrace]
  refine ⟨33164457929808607449365791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44219277239744809932487721 33164457929808607449365791)
  ·
    refine ⟨49746686894712911174048687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33164457929808607449365791 49746686894712911174048687)
    ·
      refine ⟨74620030342069366761073031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49746686894712911174048687 74620030342069366761073031)
      ·
        refine ⟨111930045513104050141609547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74620030342069366761073031 111930045513104050141609547)
        ·
          refine ⟨167895068269656075212414321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111930045513104050141609547 167895068269656075212414321)
          ·
            refine ⟨125921301202242056409310741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167895068269656075212414321 125921301202242056409310741)
            ·
              refine ⟨5902560993855096394186441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125921301202242056409310741 5902560993855096394186441)
              ·
                refine ⟨4426920745391322295639831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5902560993855096394186441 4426920745391322295639831)
                ·
                  refine ⟨6640381118086983443459747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426920745391322295639831 6640381118086983443459747)
                  ·
                    refine ⟨9960571677130475165189621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6640381118086983443459747 9960571677130475165189621)
                    ·
                      refine ⟨933803594730982046736527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9960571677130475165189621 933803594730982046736527)
                      ·
                        rfl

theorem cell23_1818576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_1818576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818576 prefixEnd_1818576 := by exact prefixLift 1818576
  have htrace : WordTrace (prefixWord ++ tailWord_1818576) baseStart_1818576 baseEnd_1818576 := by
    simpa [prefixWord, tailWord_1818576, baseEnd_1818576] using wordTrace_append hprefix tailTrace_1818576
  have hstable : (prefixWord ++ tailWord_1818576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818576).length < 2 ^ (prefixWord ++ tailWord_1818576).sum := by decide
  have hdescent : baseEnd_1818576 < baseStart_1818576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818583 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 2, 4]
def baseStart_1818583 : Nat := 118140960795 + 1818583 * 2 ^ 59
def prefixEnd_1818583 : Nat := 4983230072969 + 3 ^ 40 * 1818583 * 2
def baseEnd_1818583 : Nat := 311269063031854506449665

theorem tailTrace_1818583 : CollatzResearch.WordTrace tailWord_1818583 prefixEnd_1818583 311269063031854506449665 := by
  unfold tailWord_1818583
  simp only [CollatzResearch.WordTrace]
  refine ⟨66329171170591855094236403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44219447447061236729490935 66329171170591855094236403)
  ·
    refine ⟨99493756755887782641354605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66329171170591855094236403 99493756755887782641354605)
    ·
      refine ⟨37310158783457918490507977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99493756755887782641354605 37310158783457918490507977)
      ·
        refine ⟨27982619087593438867880983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37310158783457918490507977 27982619087593438867880983)
        ·
          refine ⟨41973928631390158301821475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27982619087593438867880983 41973928631390158301821475)
          ·
            refine ⟨62960892947085237452732213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41973928631390158301821475 62960892947085237452732213)
            ·
              refine ⟨5902583713789241011193645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62960892947085237452732213 5902583713789241011193645)
              ·
                refine ⟨2213468892670965379197617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5902583713789241011193645 2213468892670965379197617)
                ·
                  refine ⟨1660101669503224034398213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2213468892670965379197617 1660101669503224034398213)
                  ·
                    refine ⟨311269063031854506449665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1660101669503224034398213 311269063031854506449665)
                    ·
                      rfl

theorem cell23_1818583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_1818583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818583 prefixEnd_1818583 := by exact prefixLift 1818583
  have htrace : WordTrace (prefixWord ++ tailWord_1818583) baseStart_1818583 baseEnd_1818583 := by
    simpa [prefixWord, tailWord_1818583, baseEnd_1818583] using wordTrace_append hprefix tailTrace_1818583
  have hstable : (prefixWord ++ tailWord_1818583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818583).length < 2 ^ (prefixWord ++ tailWord_1818583).sum := by decide
  have hdescent : baseEnd_1818583 < baseStart_1818583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818594 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_1818594 : Nat := 118140960795 + 1818594 * 2 ^ 59
def prefixEnd_1818594 : Nat := 4983230072969 + 3 ^ 40 * 1818594 * 2
def baseEnd_1818594 : Nat := 933812837382762976311445

theorem tailTrace_1818594 : CollatzResearch.WordTrace tailWord_1818594 prefixEnd_1818594 933812837382762976311445 := by
  unfold tailWord_1818594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16582393093388000993221709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44219714915701335981924557 16582393093388000993221709)
  ·
    refine ⟨6218397410020500372458141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16582393093388000993221709 6218397410020500372458141)
    ·
      refine ⟨2331899028757687639671803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6218397410020500372458141 2331899028757687639671803)
      ·
        refine ⟨3497848543136531459507705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2331899028757687639671803 3497848543136531459507705)
        ·
          refine ⟨2623386407352398594630779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3497848543136531459507705 2623386407352398594630779)
          ·
            refine ⟨3935079611028597891946169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623386407352398594630779 3935079611028597891946169)
            ·
              refine ⟨2951309708271448418959627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3935079611028597891946169 2951309708271448418959627)
              ·
                refine ⟨4426964562407172628439441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951309708271448418959627 4426964562407172628439441)
                ·
                  refine ⟨3320223421805379471329581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4426964562407172628439441 3320223421805379471329581)
                  ·
                    refine ⟨1245083783177017301748593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320223421805379471329581 1245083783177017301748593)
                    ·
                      refine ⟨933812837382762976311445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245083783177017301748593 933812837382762976311445)
                      ·
                        rfl

theorem cell23_1818594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_1818594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818594 prefixEnd_1818594 := by exact prefixLift 1818594
  have htrace : WordTrace (prefixWord ++ tailWord_1818594) baseStart_1818594 baseEnd_1818594 := by
    simpa [prefixWord, tailWord_1818594, baseEnd_1818594] using wordTrace_append hprefix tailTrace_1818594
  have hstable : (prefixWord ++ tailWord_1818594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818594).length < 2 ^ (prefixWord ++ tailWord_1818594).sum := by decide
  have hdescent : baseEnd_1818594 < baseStart_1818594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818607 : List Nat := [1, 1, 2, 1, 4, 2, 2, 5, 1, 2, 2]
def baseStart_1818607 : Nat := 118140960795 + 1818607 * 2 ^ 59
def prefixEnd_1818607 : Nat := 4983230072969 + 3 ^ 40 * 1818607 * 2
def baseEnd_1818607 : Nat := 933819512631271425448885

theorem tailTrace_1818607 : CollatzResearch.WordTrace tailWord_1818607 prefixEnd_1818607 933819512631271425448885 := by
  unfold tailWord_1818607
  simp only [CollatzResearch.WordTrace]
  refine ⟨66330046522504907193110075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44220031015003271462073383 66330046522504907193110075)
  ·
    refine ⟨99495069783757360789665113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66330046522504907193110075 99495069783757360789665113)
    ·
      refine ⟨74621302337818020592248835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99495069783757360789665113 74621302337818020592248835)
      ·
        refine ⟨111931953506727030888373253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74621302337818020592248835 111931953506727030888373253)
        ·
          refine ⟨20987241282511318291569985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111931953506727030888373253 20987241282511318291569985)
          ·
            refine ⟨15740430961883488718677489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20987241282511318291569985 15740430961883488718677489)
            ·
              refine ⟨11805323221412616539008117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15740430961883488718677489 11805323221412616539008117)
              ·
                refine ⟨1106749052007432800532011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11805323221412616539008117 1106749052007432800532011)
                ·
                  refine ⟨1660123578011149200798017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106749052007432800532011 1660123578011149200798017)
                  ·
                    refine ⟨1245092683508361900598513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1660123578011149200798017 1245092683508361900598513)
                    ·
                      refine ⟨933819512631271425448885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245092683508361900598513 933819512631271425448885)
                      ·
                        rfl

theorem cell23_1818607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 2, 2].length) (baseStart_1818607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818607 prefixEnd_1818607 := by exact prefixLift 1818607
  have htrace : WordTrace (prefixWord ++ tailWord_1818607) baseStart_1818607 baseEnd_1818607 := by
    simpa [prefixWord, tailWord_1818607, baseEnd_1818607] using wordTrace_append hprefix tailTrace_1818607
  have hstable : (prefixWord ++ tailWord_1818607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818607).length < 2 ^ (prefixWord ++ tailWord_1818607).sum := by decide
  have hdescent : baseEnd_1818607 < baseStart_1818607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818623 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 3]
def baseStart_1818623 : Nat := 118140960795 + 1818623 * 2 ^ 59
def prefixEnd_1818623 : Nat := 4983230072969 + 3 ^ 40 * 1818623 * 2
def baseEnd_1818623 : Nat := 933827728321743362848811

theorem tailTrace_1818623 : CollatzResearch.WordTrace tailWord_1818623 prefixEnd_1818623 933827728321743362848811 := by
  unfold tailWord_1818623
  simp only [CollatzResearch.WordTrace]
  refine ⟨66330630090446941925692523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44220420060297961283795015 66330630090446941925692523)
  ·
    refine ⟨99495945135670412888538785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66330630090446941925692523 99495945135670412888538785)
    ·
      refine ⟨74621958851752809666404089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99495945135670412888538785 74621958851752809666404089)
      ·
        refine ⟨55966469138814607249803067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74621958851752809666404089 55966469138814607249803067)
        ·
          refine ⟨83949703708221910874704601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55966469138814607249803067 83949703708221910874704601)
          ·
            refine ⟨62962277781166433156028451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83949703708221910874704601 62962277781166433156028451)
            ·
              refine ⟨94443416671749649734042677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62962277781166433156028451 94443416671749649734042677)
              ·
                refine ⟨8854070312976529662566501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94443416671749649734042677 8854070312976529662566501)
                ·
                  refine ⟨1660138183683099311731219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8854070312976529662566501 1660138183683099311731219)
                  ·
                    refine ⟨2490207275524648967596829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1660138183683099311731219 2490207275524648967596829)
                    ·
                      refine ⟨933827728321743362848811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2490207275524648967596829 933827728321743362848811)
                      ·
                        rfl

theorem cell23_1818623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_1818623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818623 prefixEnd_1818623 := by exact prefixLift 1818623
  have htrace : WordTrace (prefixWord ++ tailWord_1818623) baseStart_1818623 baseEnd_1818623 := by
    simpa [prefixWord, tailWord_1818623, baseEnd_1818623] using wordTrace_append hprefix tailTrace_1818623
  have hstable : (prefixWord ++ tailWord_1818623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818623).length < 2 ^ (prefixWord ++ tailWord_1818623).sum := by decide
  have hdescent : baseEnd_1818623 < baseStart_1818623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818650 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2]
def baseStart_1818650 : Nat := 118140960795 + 1818650 * 2 ^ 59
def prefixEnd_1818650 : Nat := 4983230072969 + 3 ^ 40 * 1818650 * 2
def baseEnd_1818650 : Nat := 933841592299414757211187

theorem tailTrace_1818650 : CollatzResearch.WordTrace tailWord_1818650 prefixEnd_1818650 933841592299414757211187 := by
  unfold tailWord_1818650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16582903715337281384231351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44221076574232750357950269 16582903715337281384231351)
  ·
    refine ⟨24874355573005922076347027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16582903715337281384231351 24874355573005922076347027)
    ·
      refine ⟨37311533359508883114520541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24874355573005922076347027 37311533359508883114520541)
      ·
        refine ⟨13991825009815831167945203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37311533359508883114520541 13991825009815831167945203)
        ·
          refine ⟨20987737514723746751917805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13991825009815831167945203 20987737514723746751917805)
          ·
            refine ⟨7870401568021405031969177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20987737514723746751917805 7870401568021405031969177)
            ·
              refine ⟨5902801176016053773976883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7870401568021405031969177 5902801176016053773976883)
              ·
                refine ⟨8854201764024080660965325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5902801176016053773976883 8854201764024080660965325)
                ·
                  refine ⟨3320325661509030247861997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8854201764024080660965325 3320325661509030247861997)
                  ·
                    refine ⟨1245122123065886342948249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320325661509030247861997 1245122123065886342948249)
                    ·
                      refine ⟨933841592299414757211187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245122123065886342948249 933841592299414757211187)
                      ·
                        rfl

theorem cell23_1818650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_1818650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818650 prefixEnd_1818650 := by exact prefixLift 1818650
  have htrace : WordTrace (prefixWord ++ tailWord_1818650) baseStart_1818650 baseEnd_1818650 := by
    simpa [prefixWord, tailWord_1818650, baseEnd_1818650] using wordTrace_append hprefix tailTrace_1818650
  have hstable : (prefixWord ++ tailWord_1818650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818650).length < 2 ^ (prefixWord ++ tailWord_1818650).sum := by decide
  have hdescent : baseEnd_1818650 < baseStart_1818650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818720 : List Nat := [2, 1, 1, 3, 2, 3, 3, 3, 5]
def baseStart_1818720 : Nat := 118140960795 + 1818720 * 2 ^ 59
def prefixEnd_1818720 : Nat := 4983230072969 + 3 ^ 40 * 1818720 * 2
def baseEnd_1818720 : Nat := 103764170660581053703985

theorem tailTrace_1818720 : CollatzResearch.WordTrace tailWord_1818720 prefixEnd_1818720 103764170660581053703985 := by
  unfold tailWord_1818720
  simp only [CollatzResearch.WordTrace]
  refine ⟨33167083985547763745986807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44222778647397018327982409 33167083985547763745986807)
  ·
    refine ⟨49750625978321645618980211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33167083985547763745986807 49750625978321645618980211)
    ·
      refine ⟨74625938967482468428470317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49750625978321645618980211 74625938967482468428470317)
      ·
        refine ⟨27984727112805925660676369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74625938967482468428470317 27984727112805925660676369)
        ·
          refine ⟨20988545334604444245507277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27984727112805925660676369 20988545334604444245507277)
          ·
            refine ⟨7870704500476666592065229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20988545334604444245507277 7870704500476666592065229)
            ·
              refine ⟨2951514187678749972024461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7870704500476666592065229 2951514187678749972024461)
              ·
                refine ⟨1106817820379531239509173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2951514187678749972024461 1106817820379531239509173)
                ·
                  refine ⟨103764170660581053703985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106817820379531239509173 103764170660581053703985)
                  ·
                    rfl

theorem cell23_1818720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 5].length) (baseStart_1818720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818720 prefixEnd_1818720 := by exact prefixLift 1818720
  have htrace : WordTrace (prefixWord ++ tailWord_1818720) baseStart_1818720 baseEnd_1818720 := by
    simpa [prefixWord, tailWord_1818720, baseEnd_1818720] using wordTrace_append hprefix tailTrace_1818720
  have hstable : (prefixWord ++ tailWord_1818720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818720).length < 2 ^ (prefixWord ++ tailWord_1818720).sum := by decide
  have hdescent : baseEnd_1818720 < baseStart_1818720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818743 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_1818743 : Nat := 118140960795 + 1818743 * 2 ^ 59
def prefixEnd_1818743 : Nat := 4983230072969 + 3 ^ 40 * 1818743 * 2
def baseEnd_1818743 : Nat := 933889346000282893348259

theorem tailTrace_1818743 : CollatzResearch.WordTrace tailWord_1818743 prefixEnd_1818743 933889346000282893348259 := by
  unfold tailWord_1818743
  simp only [CollatzResearch.WordTrace]
  refine ⟨66335006850012202420060883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44223337900008134946707255 66335006850012202420060883)
  ·
    refine ⟨99502510275018303630091325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66335006850012202420060883 99502510275018303630091325)
    ·
      refine ⟨37313441353131863861284247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99502510275018303630091325 37313441353131863861284247)
      ·
        refine ⟨55970162029697795791926371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37313441353131863861284247 55970162029697795791926371)
        ·
          refine ⟨83955243044546693687889557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55970162029697795791926371 83955243044546693687889557)
          ·
            refine ⟨3935402017713126266619823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83955243044546693687889557 3935402017713126266619823)
            ·
              refine ⟨5903103026569689399929735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3935402017713126266619823 5903103026569689399929735)
              ·
                refine ⟨8854654539854534099894603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903103026569689399929735 8854654539854534099894603)
                ·
                  refine ⟨13281981809781801149841905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8854654539854534099894603 13281981809781801149841905)
                  ·
                    refine ⟨9961486357336350862381429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13281981809781801149841905 9961486357336350862381429)
                    ·
                      refine ⟨933889346000282893348259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9961486357336350862381429 933889346000282893348259)
                      ·
                        rfl

theorem cell23_1818743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_1818743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818743 prefixEnd_1818743 := by exact prefixLift 1818743
  have htrace : WordTrace (prefixWord ++ tailWord_1818743) baseStart_1818743 baseEnd_1818743 := by
    simpa [prefixWord, tailWord_1818743, baseEnd_1818743] using wordTrace_append hprefix tailTrace_1818743
  have hstable : (prefixWord ++ tailWord_1818743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818743).length < 2 ^ (prefixWord ++ tailWord_1818743).sum := by decide
  have hdescent : baseEnd_1818743 < baseStart_1818743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818803 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 3]
def baseStart_1818803 : Nat := 118140960795 + 1818803 * 2 ^ 59
def prefixEnd_1818803 : Nat := 4983230072969 + 3 ^ 40 * 1818803 * 2
def baseEnd_1818803 : Nat := 933920154839552658597983

theorem tailTrace_1818803 : CollatzResearch.WordTrace tailWord_1818803 prefixEnd_1818803 933920154839552658597983 := by
  unfold tailWord_1818803
  simp only [CollatzResearch.WordTrace]
  refine ⟨66337195229794832667245063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44224796819863221778163375 66337195229794832667245063)
  ·
    refine ⟨99505792844692249000867595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66337195229794832667245063 99505792844692249000867595)
    ·
      refine ⟨149258689267038373501301393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99505792844692249000867595 149258689267038373501301393)
      ·
        refine ⟨111944016950278780125976045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149258689267038373501301393 111944016950278780125976045)
        ·
          refine ⟨41979006356354542547241017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111944016950278780125976045 41979006356354542547241017)
          ·
            refine ⟨31484254767265906910430763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41979006356354542547241017 31484254767265906910430763)
            ·
              refine ⟨47226382150898860365646145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31484254767265906910430763 47226382150898860365646145)
              ·
                refine ⟨35419786613174145274234609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47226382150898860365646145 35419786613174145274234609)
                ·
                  refine ⟨26564839959880608955675957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35419786613174145274234609 26564839959880608955675957)
                  ·
                    refine ⟨2490453746238807089594621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26564839959880608955675957 2490453746238807089594621)
                    ·
                      refine ⟨933920154839552658597983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2490453746238807089594621 933920154839552658597983)
                      ·
                        rfl

theorem cell23_1818803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_1818803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818803 prefixEnd_1818803 := by exact prefixLift 1818803
  have htrace : WordTrace (prefixWord ++ tailWord_1818803) baseStart_1818803 baseEnd_1818803 := by
    simpa [prefixWord, tailWord_1818803, baseEnd_1818803] using wordTrace_append hprefix tailTrace_1818803
  have hstable : (prefixWord ++ tailWord_1818803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818803).length < 2 ^ (prefixWord ++ tailWord_1818803).sum := by decide
  have hdescent : baseEnd_1818803 < baseStart_1818803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818880 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 3]
def baseStart_1818880 : Nat := 118140960795 + 1818880 * 2 ^ 59
def prefixEnd_1818880 : Nat := 4983230072969 + 3 ^ 40 * 1818880 * 2
def baseEnd_1818880 : Nat := 933959692849948857335129

theorem tailTrace_1818880 : CollatzResearch.WordTrace tailWord_1818880 prefixEnd_1818880 933959692849948857335129 := by
  unfold tailWord_1818880
  simp only [CollatzResearch.WordTrace]
  refine ⟨33170001825257937408899047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44226669100343916545198729 33170001825257937408899047)
  ·
    refine ⟨49755002737886906113348571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33170001825257937408899047 49755002737886906113348571)
    ·
      refine ⟨74632504106830359170022857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49755002737886906113348571 74632504106830359170022857)
      ·
        refine ⟨55974378080122769377517143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74632504106830359170022857 55974378080122769377517143)
        ·
          refine ⟨83961567120184154066275715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55974378080122769377517143 83961567120184154066275715)
          ·
            refine ⟨125942350680276231099413573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83961567120184154066275715 125942350680276231099413573)
            ·
              refine ⟨23614190752551793331140045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125942350680276231099413573 23614190752551793331140045)
              ·
                refine ⟨8855321532206922499177517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23614190752551793331140045 8855321532206922499177517)
                ·
                  refine ⟨3320745574577595937191569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8855321532206922499177517 3320745574577595937191569)
                  ·
                    refine ⟨2490559180933196952893677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3320745574577595937191569 2490559180933196952893677)
                    ·
                      refine ⟨933959692849948857335129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2490559180933196952893677 933959692849948857335129)
                      ·
                        rfl

theorem cell23_1818880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_1818880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818880 prefixEnd_1818880 := by exact prefixLift 1818880
  have htrace : WordTrace (prefixWord ++ tailWord_1818880) baseStart_1818880 baseEnd_1818880 := by
    simpa [prefixWord, tailWord_1818880, baseEnd_1818880] using wordTrace_append hprefix tailTrace_1818880
  have hstable : (prefixWord ++ tailWord_1818880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818880).length < 2 ^ (prefixWord ++ tailWord_1818880).sum := by decide
  have hdescent : baseEnd_1818880 < baseStart_1818880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818883 : List Nat := [1, 1, 1, 3, 2, 3, 3, 9]
def baseStart_1818883 : Nat := 118140960795 + 1818883 * 2 ^ 59
def prefixEnd_1818883 : Nat := 4983230072969 + 3 ^ 40 * 1818883 * 2
def baseEnd_1818883 : Nat := 34591156788589346133245

theorem tailTrace_1818883 : CollatzResearch.WordTrace tailWord_1818883 prefixEnd_1818883 34591156788589346133245 := by
  unfold tailWord_1818883
  simp only [CollatzResearch.WordTrace]
  refine ⟨66340113069505006330157303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44226742046336670886771535 66340113069505006330157303)
  ·
    refine ⟨99510169604257509495235955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66340113069505006330157303 99510169604257509495235955)
    ·
      refine ⟨149265254406386264242853933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99510169604257509495235955 149265254406386264242853933)
      ·
        refine ⟨55974470402394849091070225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149265254406386264242853933 55974470402394849091070225)
        ·
          refine ⟨41980852801796136818302669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55974470402394849091070225 41980852801796136818302669)
          ·
            refine ⟨15742819800673551306863501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41980852801796136818302669 15742819800673551306863501)
            ·
              refine ⟨5903557425252581740073813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15742819800673551306863501 5903557425252581740073813)
              ·
                refine ⟨34591156788589346133245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5903557425252581740073813 34591156788589346133245)
                ·
                  rfl

theorem cell23_1818883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 9].length) (baseStart_1818883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818883 prefixEnd_1818883 := by exact prefixLift 1818883
  have htrace : WordTrace (prefixWord ++ tailWord_1818883) baseStart_1818883 baseEnd_1818883 := by
    simpa [prefixWord, tailWord_1818883, baseEnd_1818883] using wordTrace_append hprefix tailTrace_1818883
  have hstable : (prefixWord ++ tailWord_1818883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818883).length < 2 ^ (prefixWord ++ tailWord_1818883).sum := by decide
  have hdescent : baseEnd_1818883 < baseStart_1818883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818890 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1818890 : Nat := 118140960795 + 1818890 * 2 ^ 59
def prefixEnd_1818890 : Nat := 4983230072969 + 3 ^ 40 * 1818890 * 2
def baseEnd_1818890 : Nat := 933964827656493818210083

theorem tailTrace_1818890 : CollatzResearch.WordTrace tailWord_1818890 prefixEnd_1818890 933964827656493818210083 := by
  unfold tailWord_1818890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16585092095119911631415531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44226912253653097683774749 16585092095119911631415531)
  ·
    refine ⟨24877638142679867447123297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16585092095119911631415531 24877638142679867447123297)
    ·
      refine ⟨18658228607009900585342473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24877638142679867447123297 18658228607009900585342473)
      ·
        refine ⟨13993671455257425439006855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18658228607009900585342473 13993671455257425439006855)
        ·
          refine ⟨20990507182886138158510283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13993671455257425439006855 20990507182886138158510283)
          ·
            refine ⟨31485760774329207237765425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20990507182886138158510283 31485760774329207237765425)
            ·
              refine ⟨23614320580746905428324069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31485760774329207237765425 23614320580746905428324069)
              ·
                refine ⟨4427685108890044767810763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23614320580746905428324069 4427685108890044767810763)
                ·
                  refine ⟨6641527663335067151716145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427685108890044767810763 6641527663335067151716145)
                  ·
                    refine ⟨4981145747501300363787109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6641527663335067151716145 4981145747501300363787109)
                    ·
                      refine ⟨933964827656493818210083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4981145747501300363787109 933964827656493818210083)
                      ·
                        rfl

theorem cell23_1818890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1818890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818890 prefixEnd_1818890 := by exact prefixLift 1818890
  have htrace : WordTrace (prefixWord ++ tailWord_1818890) baseStart_1818890 baseEnd_1818890 := by
    simpa [prefixWord, tailWord_1818890, baseEnd_1818890] using wordTrace_append hprefix tailTrace_1818890
  have hstable : (prefixWord ++ tailWord_1818890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818890).length < 2 ^ (prefixWord ++ tailWord_1818890).sum := by decide
  have hdescent : baseEnd_1818890 < baseStart_1818890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818897 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_1818897 : Nat := 118140960795 + 1818897 * 2 ^ 59
def prefixEnd_1818897 : Nat := 4983230072969 + 3 ^ 40 * 1818897 * 2
def baseEnd_1818897 : Nat := 933968422021075290822551

theorem tailTrace_1818897 : CollatzResearch.WordTrace tailWord_1818897 prefixEnd_1818897 933968422021075290822551 := by
  unfold tailWord_1818897
  simp only [CollatzResearch.WordTrace]
  refine ⟨66340623691454286721166945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44227082460969524480777963 66340623691454286721166945)
  ·
    refine ⟨49755467768590715040875209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66340623691454286721166945 49755467768590715040875209)
    ·
      refine ⟨37316600826443036280656407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49755467768590715040875209 37316600826443036280656407)
      ·
        refine ⟨55974901239664554420984611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37316600826443036280656407 55974901239664554420984611)
        ·
          refine ⟨83962351859496831631476917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55974901239664554420984611 83962351859496831631476917)
          ·
            refine ⟨7871470486827827965450961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83962351859496831631476917 7871470486827827965450961)
            ·
              refine ⟨5903602865120870974088221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7871470486827827965450961 5903602865120870974088221)
              ·
                refine ⟨2213851074420326615283083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5903602865120870974088221 2213851074420326615283083)
                ·
                  refine ⟨3320776611630489922924625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213851074420326615283083 3320776611630489922924625)
                  ·
                    refine ⟨2490582458722867442193469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3320776611630489922924625 2490582458722867442193469)
                    ·
                      refine ⟨933968422021075290822551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2490582458722867442193469 933968422021075290822551)
                      ·
                        rfl

theorem cell23_1818897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_1818897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818897 prefixEnd_1818897 := by exact prefixLift 1818897
  have htrace : WordTrace (prefixWord ++ tailWord_1818897) baseStart_1818897 baseEnd_1818897 := by
    simpa [prefixWord, tailWord_1818897, baseEnd_1818897] using wordTrace_append hprefix tailTrace_1818897
  have hstable : (prefixWord ++ tailWord_1818897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818897).length < 2 ^ (prefixWord ++ tailWord_1818897).sum := by decide
  have hdescent : baseEnd_1818897 < baseStart_1818897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818911 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 3, 2, 2]
def baseStart_1818911 : Nat := 118140960795 + 1818911 * 2 ^ 59
def prefixEnd_1818911 : Nat := 4983230072969 + 3 ^ 40 * 1818911 * 2
def baseEnd_1818911 : Nat := 933975610750238236047487

theorem tailTrace_1818911 : CollatzResearch.WordTrace tailWord_1818911 prefixEnd_1818911 933975610750238236047487 := by
  unfold tailWord_1818911
  simp only [CollatzResearch.WordTrace]
  refine ⟨66341134313403567112176587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44227422875602378074784391 66341134313403567112176587)
  ·
    refine ⟨99511701470105350668264881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66341134313403567112176587 99511701470105350668264881)
    ·
      refine ⟨74633776102579013001198661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99511701470105350668264881 74633776102579013001198661)
      ·
        refine ⟨13993833019233564937724749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74633776102579013001198661 13993833019233564937724749)
        ·
          refine ⟨5247687382212586851646781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13993833019233564937724749 5247687382212586851646781)
          ·
            refine ⟨1967882768329720069367543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5247687382212586851646781 1967882768329720069367543)
            ·
              refine ⟨2951824152494580104051315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967882768329720069367543 2951824152494580104051315)
              ·
                refine ⟨4427736228741870156076973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951824152494580104051315 4427736228741870156076973)
                ·
                  refine ⟨1660401085778201308528865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4427736228741870156076973 1660401085778201308528865)
                  ·
                    refine ⟨1245300814333650981396649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1660401085778201308528865 1245300814333650981396649)
                    ·
                      refine ⟨933975610750238236047487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245300814333650981396649 933975610750238236047487)
                      ·
                        rfl

theorem cell23_1818911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_1818911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818911 prefixEnd_1818911 := by exact prefixLift 1818911
  have htrace : WordTrace (prefixWord ++ tailWord_1818911) baseStart_1818911 baseEnd_1818911 := by
    simpa [prefixWord, tailWord_1818911, baseEnd_1818911] using wordTrace_append hprefix tailTrace_1818911
  have hstable : (prefixWord ++ tailWord_1818911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818911).length < 2 ^ (prefixWord ++ tailWord_1818911).sum := by decide
  have hdescent : baseEnd_1818911 < baseStart_1818911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818948 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1818948 : Nat := 118140960795 + 1818948 * 2 ^ 59
def prefixEnd_1818948 : Nat := 4983230072969 + 3 ^ 40 * 1818948 * 2
def baseEnd_1818948 : Nat := 933994609534454591284817

theorem tailTrace_1818948 : CollatzResearch.WordTrace tailWord_1818948 prefixEnd_1818948 933994609534454591284817 := by
  unfold tailWord_1818948
  simp only [CollatzResearch.WordTrace]
  refine ⟨33171241907134761215636749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44228322542846348287515665 33171241907134761215636749)
  ·
    refine ⟨12439215715175535455863781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33171241907134761215636749 12439215715175535455863781)
    ·
      refine ⟨2332352946595412897974459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12439215715175535455863781 2332352946595412897974459)
      ·
        refine ⟨3498529419893119346961689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332352946595412897974459 3498529419893119346961689)
        ·
          refine ⟨2623897064919839510221267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3498529419893119346961689 2623897064919839510221267)
          ·
            refine ⟨3935845597379759265331901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623897064919839510221267 3935845597379759265331901)
            ·
              refine ⟨1475942099017409724499463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3935845597379759265331901 1475942099017409724499463)
              ·
                refine ⟨2213913148526114586749195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475942099017409724499463 2213913148526114586749195)
                ·
                  refine ⟨3320869722789171880123793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213913148526114586749195 3320869722789171880123793)
                  ·
                    refine ⟨2490652292091878910092845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3320869722789171880123793 2490652292091878910092845)
                    ·
                      refine ⟨933994609534454591284817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2490652292091878910092845 933994609534454591284817)
                      ·
                        rfl

theorem cell23_1818948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1818948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818948 prefixEnd_1818948 := by exact prefixLift 1818948
  have htrace : WordTrace (prefixWord ++ tailWord_1818948) baseStart_1818948 baseEnd_1818948 := by
    simpa [prefixWord, tailWord_1818948, baseEnd_1818948] using wordTrace_append hprefix tailTrace_1818948
  have hstable : (prefixWord ++ tailWord_1818948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818948).length < 2 ^ (prefixWord ++ tailWord_1818948).sum := by decide
  have hdescent : baseEnd_1818948 < baseStart_1818948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818967 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 3, 4, 2]
def baseStart_1818967 : Nat := 118140960795 + 1818967 * 2 ^ 59
def prefixEnd_1818967 : Nat := 4983230072969 + 3 ^ 40 * 1818967 * 2
def baseEnd_1818967 : Nat := 934004365666890016947229

theorem tailTrace_1818967 : CollatzResearch.WordTrace tailWord_1818967 prefixEnd_1818967 934004365666890016947229 := by
  unfold tailWord_1818967
  simp only [CollatzResearch.WordTrace]
  refine ⟨66343176801200688676215155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44228784534133792450810103 66343176801200688676215155)
  ·
    refine ⟨99514765201801033014322733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66343176801200688676215155 99514765201801033014322733)
    ·
      refine ⟨37318036950675387380371025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99514765201801033014322733 37318036950675387380371025)
      ·
        refine ⟨27988527713006540535278269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37318036950675387380371025 27988527713006540535278269)
        ·
          refine ⟨10495697892377452700729351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27988527713006540535278269 10495697892377452700729351)
          ·
            refine ⟨15743546838566179051094027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10495697892377452700729351 15743546838566179051094027)
            ·
              refine ⟨23615320257849268576641041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15743546838566179051094027 23615320257849268576641041)
              ·
                refine ⟨17711490193386951432480781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23615320257849268576641041 17711490193386951432480781)
                ·
                  refine ⟨6641808822520106787180293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17711490193386951432480781 6641808822520106787180293)
                  ·
                    refine ⟨1245339154222520022596305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641808822520106787180293 1245339154222520022596305)
                    ·
                      refine ⟨934004365666890016947229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245339154222520022596305 934004365666890016947229)
                      ·
                        rfl

theorem cell23_1818967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_1818967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818967 prefixEnd_1818967 := by exact prefixLift 1818967
  have htrace : WordTrace (prefixWord ++ tailWord_1818967) baseStart_1818967 baseEnd_1818967 := by
    simpa [prefixWord, tailWord_1818967, baseEnd_1818967] using wordTrace_append hprefix tailTrace_1818967
  have hstable : (prefixWord ++ tailWord_1818967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818967).length < 2 ^ (prefixWord ++ tailWord_1818967).sum := by decide
  have hdescent : baseEnd_1818967 < baseStart_1818967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818984 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_1818984 : Nat := 118140960795 + 1818984 * 2 ^ 59
def prefixEnd_1818984 : Nat := 4983230072969 + 3 ^ 40 * 1818984 * 2
def baseEnd_1818984 : Nat := 934013094838016450434651

theorem tailTrace_1818984 : CollatzResearch.WordTrace tailWord_1818984 prefixEnd_1818984 934013094838016450434651 := by
  unfold tailWord_1818984
  simp only [CollatzResearch.WordTrace]
  refine ⟨33171898421069550289792003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44229197894759400386389337 33171898421069550289792003)
  ·
    refine ⟨49757847631604325434688005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33171898421069550289792003 49757847631604325434688005)
    ·
      refine ⟨9329596430925811019004001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49757847631604325434688005 9329596430925811019004001)
      ·
        refine ⟨6997197323194358264253001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9329596430925811019004001 6997197323194358264253001)
        ·
          refine ⟨5247897992395768698189751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6997197323194358264253001 5247897992395768698189751)
          ·
            refine ⟨7871846988593653047284627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247897992395768698189751 7871846988593653047284627)
            ·
              refine ⟨11807770482890479570926941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871846988593653047284627 11807770482890479570926941)
              ·
                refine ⟨4427913931083929839097603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11807770482890479570926941 4427913931083929839097603)
                ·
                  refine ⟨6641870896625894758646405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427913931083929839097603 6641870896625894758646405)
                  ·
                    refine ⟨1245350793117355267246201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641870896625894758646405 1245350793117355267246201)
                    ·
                      refine ⟨934013094838016450434651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245350793117355267246201 934013094838016450434651)
                      ·
                        rfl

theorem cell23_1818984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_1818984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1818984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1818984 prefixEnd_1818984 := by exact prefixLift 1818984
  have htrace : WordTrace (prefixWord ++ tailWord_1818984) baseStart_1818984 baseEnd_1818984 := by
    simpa [prefixWord, tailWord_1818984, baseEnd_1818984] using wordTrace_append hprefix tailTrace_1818984
  have hstable : (prefixWord ++ tailWord_1818984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818984).length < 2 ^ (prefixWord ++ tailWord_1818984).sum := by decide
  have hdescent : baseEnd_1818984 < baseStart_1818984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819017 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 3]
def baseStart_1819017 : Nat := 118140960795 + 1819017 * 2 ^ 59
def prefixEnd_1819017 : Nat := 4983230072969 + 3 ^ 40 * 1819017 * 2
def baseEnd_1819017 : Nat := 934030039699614821321999

theorem tailTrace_1819017 : CollatzResearch.WordTrace tailWord_1819017 prefixEnd_1819017 934030039699614821321999 := by
  unfold tailWord_1819017
  simp only [CollatzResearch.WordTrace]
  refine ⟨66345000451019547215535305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44230000300679698143690203 66345000451019547215535305)
  ·
    refine ⟨49758750338264660411651479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66345000451019547215535305 49758750338264660411651479)
    ·
      refine ⟨74638125507396990617477219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49758750338264660411651479 74638125507396990617477219)
      ·
        refine ⟨111957188261095485926215829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74638125507396990617477219 111957188261095485926215829)
        ·
          refine ⟨5247993199738850902791367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111957188261095485926215829 5247993199738850902791367)
          ·
            refine ⟨7871989799608276354187051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247993199738850902791367 7871989799608276354187051)
            ·
              refine ⟨11807984699412414531280577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871989799608276354187051 11807984699412414531280577)
              ·
                refine ⟨8855988524559310898460433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11807984699412414531280577 8855988524559310898460433)
                ·
                  refine ⟨6641991393419483173845325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8855988524559310898460433 6641991393419483173845325)
                  ·
                    refine ⟨2490746772532306190191997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6641991393419483173845325 2490746772532306190191997)
                    ·
                      refine ⟨934030039699614821321999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2490746772532306190191997 934030039699614821321999)
                      ·
                        rfl

theorem cell23_1819017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_1819017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819017 prefixEnd_1819017 := by exact prefixLift 1819017
  have htrace : WordTrace (prefixWord ++ tailWord_1819017) baseStart_1819017 baseEnd_1819017 := by
    simpa [prefixWord, tailWord_1819017, baseEnd_1819017] using wordTrace_append hprefix tailTrace_1819017
  have hstable : (prefixWord ++ tailWord_1819017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819017).length < 2 ^ (prefixWord ++ tailWord_1819017).sum := by decide
  have hdescent : baseEnd_1819017 < baseStart_1819017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819018 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_1819018 : Nat := 118140960795 + 1819018 * 2 ^ 59
def prefixEnd_1819018 : Nat := 4983230072969 + 3 ^ 40 * 1819018 * 2
def baseEnd_1819018 : Nat := 934030553180269317409495

theorem tailTrace_1819018 : CollatzResearch.WordTrace tailWord_1819018 prefixEnd_1819018 934030553180269317409495 := by
  unfold tailWord_1819018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16586259231003981096580427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44230024616010616257547805 16586259231003981096580427)
  ·
    refine ⟨24879388846505971644870641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16586259231003981096580427 24879388846505971644870641)
    ·
      refine ⟨18659541634879478733652981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24879388846505971644870641 18659541634879478733652981)
      ·
        refine ⟨1749332028269951131279967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18659541634879478733652981 1749332028269951131279967)
        ·
          refine ⟨2623998042404926696919951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749332028269951131279967 2623998042404926696919951)
          ·
            refine ⟨3935997063607390045379927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623998042404926696919951 3935997063607390045379927)
            ·
              refine ⟨5903995595411085068069891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3935997063607390045379927 5903995595411085068069891)
              ·
                refine ⟨8855993393116627602104837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903995595411085068069891 8855993393116627602104837)
                ·
                  refine ⟨1660498761209367675394657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8855993393116627602104837 1660498761209367675394657)
                  ·
                    refine ⟨1245374070907025756545993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1660498761209367675394657 1245374070907025756545993)
                    ·
                      refine ⟨934030553180269317409495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245374070907025756545993 934030553180269317409495)
                      ·
                        rfl

theorem cell23_1819018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_1819018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819018 prefixEnd_1819018 := by exact prefixLift 1819018
  have htrace : WordTrace (prefixWord ++ tailWord_1819018) baseStart_1819018 baseEnd_1819018 := by
    simpa [prefixWord, tailWord_1819018, baseEnd_1819018] using wordTrace_append hprefix tailTrace_1819018
  have hstable : (prefixWord ++ tailWord_1819018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819018).length < 2 ^ (prefixWord ++ tailWord_1819018).sum := by decide
  have hdescent : baseEnd_1819018 < baseStart_1819018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819057 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1819057 : Nat := 118140960795 + 1819057 * 2 ^ 59
def prefixEnd_1819057 : Nat := 4983230072969 + 3 ^ 40 * 1819057 * 2
def baseEnd_1819057 : Nat := 934050578925794664821815

theorem tailTrace_1819057 : CollatzResearch.WordTrace tailWord_1819057 prefixEnd_1819057 934050578925794664821815 := by
  unfold tailWord_1819057
  simp only [CollatzResearch.WordTrace]
  refine ⟨66346459370874634046991425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44230972913916422697994283 66346459370874634046991425)
  ·
    refine ⟨49759844528155975535243569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66346459370874634046991425 49759844528155975535243569)
    ·
      refine ⟨37319883396116981651432677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49759844528155975535243569 37319883396116981651432677)
      ·
        refine ⟨6997478136771934059643627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37319883396116981651432677 6997478136771934059643627)
        ·
          refine ⟨10496217205157901089465441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6997478136771934059643627 10496217205157901089465441)
          ·
            refine ⟨7872162903868425817099081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10496217205157901089465441 7872162903868425817099081)
            ·
              refine ⟨5904122177901319362824311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7872162903868425817099081 5904122177901319362824311)
              ·
                refine ⟨8856183266851979044236467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904122177901319362824311 8856183266851979044236467)
                ·
                  refine ⟨13284274900277968566354701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8856183266851979044236467 13284274900277968566354701)
                  ·
                    refine ⟨4981603087604238212383013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13284274900277968566354701 4981603087604238212383013)
                    ·
                      refine ⟨934050578925794664821815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4981603087604238212383013 934050578925794664821815)
                      ·
                        rfl

theorem cell23_1819057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1819057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819057 prefixEnd_1819057 := by exact prefixLift 1819057
  have htrace : WordTrace (prefixWord ++ tailWord_1819057) baseStart_1819057 baseEnd_1819057 := by
    simpa [prefixWord, tailWord_1819057, baseEnd_1819057] using wordTrace_append hprefix tailTrace_1819057
  have hstable : (prefixWord ++ tailWord_1819057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819057).length < 2 ^ (prefixWord ++ tailWord_1819057).sum := by decide
  have hdescent : baseEnd_1819057 < baseStart_1819057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819097 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 6]
def baseStart_1819097 : Nat := 118140960795 + 1819097 * 2 ^ 59
def prefixEnd_1819097 : Nat := 4983230072969 + 3 ^ 40 * 1819097 * 2
def baseEnd_1819097 : Nat := 103785679794663834257959

theorem tailTrace_1819097 : CollatzResearch.WordTrace tailWord_1819097 prefixEnd_1819097 103785679794663834257959 := by
  unfold tailWord_1819097
  simp only [CollatzResearch.WordTrace]
  refine ⟨66347918290729720878447545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44231945527153147252298363 66347918290729720878447545)
  ·
    refine ⟨49760938718047290658835659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66347918290729720878447545 49760938718047290658835659)
    ·
      refine ⟨74641408077070935988253489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49760938718047290658835659 74641408077070935988253489)
      ·
        refine ⟨55981056057803201991190117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74641408077070935988253489 55981056057803201991190117)
        ·
          refine ⟨10496448010838100373348147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55981056057803201991190117 10496448010838100373348147)
          ·
            refine ⟨15744672016257150560022221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10496448010838100373348147 15744672016257150560022221)
            ·
              refine ⟨5904252006096431460008333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15744672016257150560022221 5904252006096431460008333)
              ·
                refine ⟨2214094502286161797503125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5904252006096431460008333 2214094502286161797503125)
                ·
                  refine ⟨103785679794663834257959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2214094502286161797503125 103785679794663834257959)
                  ·
                    rfl

theorem cell23_1819097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 6].length) (baseStart_1819097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819097 prefixEnd_1819097 := by exact prefixLift 1819097
  have htrace : WordTrace (prefixWord ++ tailWord_1819097) baseStart_1819097 baseEnd_1819097 := by
    simpa [prefixWord, tailWord_1819097, baseEnd_1819097] using wordTrace_append hprefix tailTrace_1819097
  have hstable : (prefixWord ++ tailWord_1819097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819097).length < 2 ^ (prefixWord ++ tailWord_1819097).sum := by decide
  have hdescent : baseEnd_1819097 < baseStart_1819097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819164 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1819164 : Nat := 118140960795 + 1819164 * 2 ^ 59
def prefixEnd_1819164 : Nat := 4983230072969 + 3 ^ 40 * 1819164 * 2
def baseEnd_1819164 : Nat := 934105521355825746183823

theorem tailTrace_1819164 : CollatzResearch.WordTrace tailWord_1819164 prefixEnd_1819164 934105521355825746183823 := by
  unfold tailWord_1819164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33175180990743495660568273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44233574654324660880757697 33175180990743495660568273)
  ·
    refine ⟨24881385743057621745426205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33175180990743495660568273 24881385743057621745426205)
    ·
      refine ⟨9330519653646608154534827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24881385743057621745426205 9330519653646608154534827)
      ·
        refine ⟨13995779480469912231802241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9330519653646608154534827 13995779480469912231802241)
        ·
          refine ⟨10496834610352434173851681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13995779480469912231802241 10496834610352434173851681)
          ·
            refine ⟨7872625957764325630388761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10496834610352434173851681 7872625957764325630388761)
            ·
              refine ⟨5904469468323244222791571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7872625957764325630388761 5904469468323244222791571)
              ·
                refine ⟨8856704202484866334187357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904469468323244222791571 8856704202484866334187357)
                ·
                  refine ⟨3321264075931824875320259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8856704202484866334187357 3321264075931824875320259)
                  ·
                    refine ⟨4981896113897737312980389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3321264075931824875320259 4981896113897737312980389)
                    ·
                      refine ⟨934105521355825746183823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4981896113897737312980389 934105521355825746183823)
                      ·
                        rfl

theorem cell23_1819164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1819164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819164 prefixEnd_1819164 := by exact prefixLift 1819164
  have htrace : WordTrace (prefixWord ++ tailWord_1819164) baseStart_1819164 baseEnd_1819164 := by
    simpa [prefixWord, tailWord_1819164, baseEnd_1819164] using wordTrace_append hprefix tailTrace_1819164
  have hstable : (prefixWord ++ tailWord_1819164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819164).length < 2 ^ (prefixWord ++ tailWord_1819164).sum := by decide
  have hdescent : baseEnd_1819164 < baseStart_1819164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819178 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1819178 : Nat := 118140960795 + 1819178 * 2 ^ 59
def prefixEnd_1819178 : Nat := 4983230072969 + 3 ^ 40 * 1819178 * 2
def baseEnd_1819178 : Nat := 311370903361662897136253

theorem tailTrace_1819178 : CollatzResearch.WordTrace tailWord_1819178 prefixEnd_1819178 311370903361662897136253 := by
  unfold tailWord_1819178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16587718150859067928036547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44233915068957514474764125 16587718150859067928036547)
  ·
    refine ⟨24881577226288601892054821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16587718150859067928036547 24881577226288601892054821)
    ·
      refine ⟨4665295729929112854760279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24881577226288601892054821 4665295729929112854760279)
      ·
        refine ⟨6997943594893669282140419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665295729929112854760279 6997943594893669282140419)
        ·
          refine ⟨10496915392340503923210629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6997943594893669282140419 10496915392340503923210629)
          ·
            refine ⟨1968171636063844485601993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10496915392340503923210629 1968171636063844485601993)
            ·
              refine ⟨1476128727047883364201495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968171636063844485601993 1476128727047883364201495)
              ·
                refine ⟨2214193090571825046302243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476128727047883364201495 2214193090571825046302243)
                ·
                  refine ⟨3321289635857737569453365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214193090571825046302243 3321289635857737569453365)
                  ·
                    refine ⟨311370903361662897136253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3321289635857737569453365 311370903361662897136253)
                    ·
                      rfl

theorem cell23_1819178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1819178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819178 prefixEnd_1819178 := by exact prefixLift 1819178
  have htrace : WordTrace (prefixWord ++ tailWord_1819178) baseStart_1819178 baseEnd_1819178 := by
    simpa [prefixWord, tailWord_1819178, baseEnd_1819178] using wordTrace_append hprefix tailTrace_1819178
  have hstable : (prefixWord ++ tailWord_1819178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819178).length < 2 ^ (prefixWord ++ tailWord_1819178).sum := by decide
  have hdescent : baseEnd_1819178 < baseStart_1819178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819247 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 4, 6]
def baseStart_1819247 : Nat := 118140960795 + 1819247 * 2 ^ 59
def prefixEnd_1819247 : Nat := 4983230072969 + 3 ^ 40 * 1819247 * 2
def baseEnd_1819247 : Nat := 311382713416716307148647

theorem tailTrace_1819247 : CollatzResearch.WordTrace tailWord_1819247 prefixEnd_1819247 311382713416716307148647 := by
  unfold tailWord_1819247
  simp only [CollatzResearch.WordTrace]
  refine ⟨66353389240186296496407995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44235592826790864330938663 66353389240186296496407995)
  ·
    refine ⟨99530083860279444744611993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66353389240186296496407995 99530083860279444744611993)
    ·
      refine ⟨74647562895209583558458995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99530083860279444744611993 74647562895209583558458995)
      ·
        refine ⟨111971344342814375337688493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74647562895209583558458995 111971344342814375337688493)
        ·
          refine ⟨41989254128555390751633185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111971344342814375337688493 41989254128555390751633185)
          ·
            refine ⟨31491940596416543063724889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41989254128555390751633185 31491940596416543063724889)
            ·
              refine ⟨23618955447312407297793667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31491940596416543063724889 23618955447312407297793667)
              ·
                refine ⟨35428433170968610946690501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23618955447312407297793667 35428433170968610946690501)
                ·
                  refine ⟨6642831219556614552504469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35428433170968610946690501 6642831219556614552504469)
                  ·
                    refine ⟨311382713416716307148647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6642831219556614552504469 311382713416716307148647)
                    ·
                      rfl

theorem cell23_1819247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_1819247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819247 prefixEnd_1819247 := by exact prefixLift 1819247
  have htrace : WordTrace (prefixWord ++ tailWord_1819247) baseStart_1819247 baseEnd_1819247 := by
    simpa [prefixWord, tailWord_1819247, baseEnd_1819247] using wordTrace_append hprefix tailTrace_1819247
  have hstable : (prefixWord ++ tailWord_1819247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819247).length < 2 ^ (prefixWord ++ tailWord_1819247).sum := by decide
  have hdescent : baseEnd_1819247 < baseStart_1819247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819271 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_1819271 : Nat := 118140960795 + 1819271 * 2 ^ 59
def prefixEnd_1819271 : Nat := 4983230072969 + 3 ^ 40 * 1819271 * 2
def baseEnd_1819271 : Nat := 934160463785856827545831

theorem tailTrace_1819271 : CollatzResearch.WordTrace tailWord_1819271 prefixEnd_1819271 934160463785856827545831 := by
  unfold tailWord_1819271
  simp only [CollatzResearch.WordTrace]
  refine ⟨66354264592099348595281667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44236176394732899063521111 66354264592099348595281667)
  ·
    refine ⟨99531396888149022892922501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66354264592099348595281667 99531396888149022892922501)
    ·
      refine ⟨18662136916527941792422969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99531396888149022892922501 18662136916527941792422969)
      ·
        refine ⟨13996602687395956344317227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18662136916527941792422969 13996602687395956344317227)
        ·
          refine ⟨20994904031093934516475841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13996602687395956344317227 20994904031093934516475841)
          ·
            refine ⟨15746178023320450887356881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20994904031093934516475841 15746178023320450887356881)
            ·
              refine ⟨11809633517490338165517661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15746178023320450887356881 11809633517490338165517661)
              ·
                refine ⟨4428612569058876812069123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11809633517490338165517661 4428612569058876812069123)
                ·
                  refine ⟨6642918853588315218103685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428612569058876812069123 6642918853588315218103685)
                  ·
                    refine ⟨1245547285047809103394441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6642918853588315218103685 1245547285047809103394441)
                    ·
                      refine ⟨934160463785856827545831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245547285047809103394441 934160463785856827545831)
                      ·
                        rfl

theorem cell23_1819271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_1819271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819271 prefixEnd_1819271 := by exact prefixLift 1819271
  have htrace : WordTrace (prefixWord ++ tailWord_1819271) baseStart_1819271 baseEnd_1819271 := by
    simpa [prefixWord, tailWord_1819271, baseEnd_1819271] using wordTrace_append hprefix tailTrace_1819271
  have hstable : (prefixWord ++ tailWord_1819271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819271).length < 2 ^ (prefixWord ++ tailWord_1819271).sum := by decide
  have hdescent : baseEnd_1819271 < baseStart_1819271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819311 : List Nat := [1, 1, 2, 1, 2, 6, 1, 4, 5]
def baseStart_1819311 : Nat := 118140960795 + 1819311 * 2 ^ 59
def prefixEnd_1819311 : Nat := 4983230072969 + 3 ^ 40 * 1819311 * 2
def baseEnd_1819311 : Nat := 103797889223559630116183

theorem tailTrace_1819311 : CollatzResearch.WordTrace tailWord_1819311 prefixEnd_1819311 103797889223559630116183 := by
  unfold tailWord_1819311
  simp only [CollatzResearch.WordTrace]
  refine ⟨66355723511954435426737787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44237149007969623617825191 66355723511954435426737787)
  ·
    refine ⟨99533585267931653140106681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66355723511954435426737787 99533585267931653140106681)
    ·
      refine ⟨74650188950948739855080011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99533585267931653140106681 74650188950948739855080011)
      ·
        refine ⟨111975283426423109782620017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74650188950948739855080011 111975283426423109782620017)
        ·
          refine ⟨83981462569817332336965013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111975283426423109782620017 83981462569817332336965013)
          ·
            refine ⟨3936631057960187453295235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83981462569817332336965013 3936631057960187453295235)
            ·
              refine ⟨5904946586940281179942853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936631057960187453295235 5904946586940281179942853)
              ·
                refine ⟨1107177485051302721239285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5904946586940281179942853 1107177485051302721239285)
                ·
                  refine ⟨103797889223559630116183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1107177485051302721239285 103797889223559630116183)
                  ·
                    rfl

theorem cell23_1819311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 5].length) (baseStart_1819311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819311 prefixEnd_1819311 := by exact prefixLift 1819311
  have htrace : WordTrace (prefixWord ++ tailWord_1819311) baseStart_1819311 baseEnd_1819311 := by
    simpa [prefixWord, tailWord_1819311, baseEnd_1819311] using wordTrace_append hprefix tailTrace_1819311
  have hstable : (prefixWord ++ tailWord_1819311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819311).length < 2 ^ (prefixWord ++ tailWord_1819311).sum := by decide
  have hdescent : baseEnd_1819311 < baseStart_1819311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819324 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_1819324 : Nat := 118140960795 + 1819324 * 2 ^ 59
def prefixEnd_1819324 : Nat := 4983230072969 + 3 ^ 40 * 1819324 * 2
def baseEnd_1819324 : Nat := 311395892753515040061029

theorem tailTrace_1819324 : CollatzResearch.WordTrace tailWord_1819324 prefixEnd_1819324 311395892753515040061029 := by
  unfold tailWord_1819324
  simp only [CollatzResearch.WordTrace]
  refine ⟨33178098830453669323480513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44237465107271559097974017 33178098830453669323480513)
  ·
    refine ⟨24883574122840251992610385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33178098830453669323480513 24883574122840251992610385)
    ·
      refine ⟨18662680592130188994457789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24883574122840251992610385 18662680592130188994457789)
      ·
        refine ⟨6998505222048820872921671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18662680592130188994457789 6998505222048820872921671)
        ·
          refine ⟨10497757833073231309382507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998505222048820872921671 10497757833073231309382507)
          ·
            refine ⟨15746636749609846964073761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497757833073231309382507 15746636749609846964073761)
            ·
              refine ⟨11809977562207385223055321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15746636749609846964073761 11809977562207385223055321)
              ·
                refine ⟨8857483171655538917291491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11809977562207385223055321 8857483171655538917291491)
                ·
                  refine ⟨13286224757483308375937237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857483171655538917291491 13286224757483308375937237)
                  ·
                    refine ⟨311395892753515040061029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13286224757483308375937237 311395892753515040061029)
                    ·
                      rfl

theorem cell23_1819324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_1819324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819324 prefixEnd_1819324 := by exact prefixLift 1819324
  have htrace : WordTrace (prefixWord ++ tailWord_1819324) baseStart_1819324 baseEnd_1819324 := by
    simpa [prefixWord, tailWord_1819324, baseEnd_1819324] using wordTrace_append hprefix tailTrace_1819324
  have hstable : (prefixWord ++ tailWord_1819324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819324).length < 2 ^ (prefixWord ++ tailWord_1819324).sum := by decide
  have hdescent : baseEnd_1819324 < baseStart_1819324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819378 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_1819378 : Nat := 118140960795 + 1819378 * 2 ^ 59
def prefixEnd_1819378 : Nat := 4983230072969 + 3 ^ 40 * 1819378 * 2
def baseEnd_1819378 : Nat := 934215406215887908907839

theorem tailTrace_1819378 : CollatzResearch.WordTrace tailWord_1819378 prefixEnd_1819378 934215406215887908907839 := by
  unfold tailWord_1819378
  simp only [CollatzResearch.WordTrace]
  refine ⟨16589541800677926467356697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44238778135141137246284525 16589541800677926467356697)
  ·
    refine ⟨12442156350508444850517523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16589541800677926467356697 12442156350508444850517523)
    ·
      refine ⟨18663234525762667275776285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12442156350508444850517523 18663234525762667275776285)
      ·
        refine ⟨6998712947161000228416107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18663234525762667275776285 6998712947161000228416107)
        ·
          refine ⟨10498069420741500342624161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998712947161000228416107 10498069420741500342624161)
          ·
            refine ⟨7873552065556125256968121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10498069420741500342624161 7873552065556125256968121)
            ·
              refine ⟨5905164049167093942726091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7873552065556125256968121 5905164049167093942726091)
              ·
                refine ⟨8857746073750640914089137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905164049167093942726091 8857746073750640914089137)
                ·
                  refine ⟨6643309555312980685566853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8857746073750640914089137 6643309555312980685566853)
                  ·
                    refine ⟨1245620541621183878543785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643309555312980685566853 1245620541621183878543785)
                    ·
                      refine ⟨934215406215887908907839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245620541621183878543785 934215406215887908907839)
                      ·
                        rfl

theorem cell23_1819378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_1819378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819378 prefixEnd_1819378 := by exact prefixLift 1819378
  have htrace : WordTrace (prefixWord ++ tailWord_1819378) baseStart_1819378 baseEnd_1819378 := by
    simpa [prefixWord, tailWord_1819378, baseEnd_1819378] using wordTrace_append hprefix tailTrace_1819378
  have hstable : (prefixWord ++ tailWord_1819378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819378).length < 2 ^ (prefixWord ++ tailWord_1819378).sum := by decide
  have hdescent : baseEnd_1819378 < baseStart_1819378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819455 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 2, 3, 2]
def baseStart_1819455 : Nat := 118140960795 + 1819455 * 2 ^ 59
def prefixEnd_1819455 : Nat := 4983230072969 + 3 ^ 40 * 1819455 * 2
def baseEnd_1819455 : Nat := 934254944226284107644985

theorem tailTrace_1819455 : CollatzResearch.WordTrace tailWord_1819455 prefixEnd_1819455 934254944226284107644985 := by
  unfold tailWord_1819455
  simp only [CollatzResearch.WordTrace]
  refine ⟨66360975623432748019979819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44240650415621832013319879 66360975623432748019979819)
  ·
    refine ⟨99541463435149122029969729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66360975623432748019979819 99541463435149122029969729)
    ·
      refine ⟨74656097576361841522477297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99541463435149122029969729 74656097576361841522477297)
      ·
        refine ⟨55992073182271381141857973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74656097576361841522477297 55992073182271381141857973)
        ·
          refine ⟨5249256860837941982049185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55992073182271381141857973 5249256860837941982049185)
          ·
            refine ⟨3936942645628456486536889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5249256860837941982049185 3936942645628456486536889)
            ·
              refine ⟨2952706984221342364902667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3936942645628456486536889 2952706984221342364902667)
              ·
                refine ⟨4429060476332013547354001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952706984221342364902667 4429060476332013547354001)
                ·
                  refine ⟨3321795357249010160515501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4429060476332013547354001 3321795357249010160515501)
                  ·
                    refine ⟨1245673258968378810193313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3321795357249010160515501 1245673258968378810193313)
                    ·
                      refine ⟨934254944226284107644985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245673258968378810193313 934254944226284107644985)
                      ·
                        rfl

theorem cell23_1819455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_1819455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819455 prefixEnd_1819455 := by exact prefixLift 1819455
  have htrace : WordTrace (prefixWord ++ tailWord_1819455) baseStart_1819455 baseEnd_1819455 := by
    simpa [prefixWord, tailWord_1819455, baseEnd_1819455] using wordTrace_append hprefix tailTrace_1819455
  have hstable : (prefixWord ++ tailWord_1819455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819455).length < 2 ^ (prefixWord ++ tailWord_1819455).sum := by decide
  have hdescent : baseEnd_1819455 < baseStart_1819455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819461 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_1819461 : Nat := 118140960795 + 1819461 * 2 ^ 59
def prefixEnd_1819461 : Nat := 4983230072969 + 3 ^ 40 * 1819461 * 2
def baseEnd_1819461 : Nat := 311419341703403694723319

theorem tailTrace_1819461 : CollatzResearch.WordTrace tailWord_1819461 prefixEnd_1819461 311419341703403694723319 := by
  unfold tailWord_1819461
  simp only [CollatzResearch.WordTrace]
  refine ⟨66361194461411011044698237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44240796307607340696465491 66361194461411011044698237)
  ·
    refine ⟨24885447923029129141761839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66361194461411011044698237 24885447923029129141761839)
    ·
      refine ⟨37328171884543693712642759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24885447923029129141761839 37328171884543693712642759)
      ·
        refine ⟨55992257826815540568964139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37328171884543693712642759 55992257826815540568964139)
        ·
          refine ⟨83988386740223310853446209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55992257826815540568964139 83988386740223310853446209)
          ·
            refine ⟨62991290055167483140084657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83988386740223310853446209 62991290055167483140084657)
            ·
              refine ⟨47243467541375612355063493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62991290055167483140084657 47243467541375612355063493)
              ·
                refine ⟨8858150164007927316574405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47243467541375612355063493 8858150164007927316574405)
                ·
                  refine ⟨1660903155751486371857701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8858150164007927316574405 1660903155751486371857701)
                  ·
                    refine ⟨311419341703403694723319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1660903155751486371857701 311419341703403694723319)
                    ·
                      rfl

theorem cell23_1819461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_1819461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819461 prefixEnd_1819461 := by exact prefixLift 1819461
  have htrace : WordTrace (prefixWord ++ tailWord_1819461) baseStart_1819461 baseEnd_1819461 := by
    simpa [prefixWord, tailWord_1819461, baseEnd_1819461] using wordTrace_append hprefix tailTrace_1819461
  have hstable : (prefixWord ++ tailWord_1819461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819461).length < 2 ^ (prefixWord ++ tailWord_1819461).sum := by decide
  have hdescent : baseEnd_1819461 < baseStart_1819461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819479 : List Nat := [1, 1, 3, 2, 4, 3, 2, 2, 1, 1, 3]
def baseStart_1819479 : Nat := 118140960795 + 1819479 * 2 ^ 59
def prefixEnd_1819479 : Nat := 4983230072969 + 3 ^ 40 * 1819479 * 2
def baseEnd_1819479 : Nat := 934267267761992013744875

theorem tailTrace_1819479 : CollatzResearch.WordTrace tailWord_1819479 prefixEnd_1819479 934267267761992013744875 := by
  unfold tailWord_1819479
  simp only [CollatzResearch.WordTrace]
  refine ⟨66361850975345800118853491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44241233983563866745902327 66361850975345800118853491)
  ·
    refine ⟨99542776463018700178280237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66361850975345800118853491 99542776463018700178280237)
    ·
      refine ⟨37328541173632012566855089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99542776463018700178280237 37328541173632012566855089)
      ·
        refine ⟨27996405880224009425141317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37328541173632012566855089 27996405880224009425141317)
        ·
          refine ⟨5249326102542001767213997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27996405880224009425141317 5249326102542001767213997)
          ·
            refine ⟨1968497288453250662705249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5249326102542001767213997 1968497288453250662705249)
            ·
              refine ⟨1476372966339937997028937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968497288453250662705249 1476372966339937997028937)
              ·
                refine ⟨1107279724754953497771703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476372966339937997028937 1107279724754953497771703)
                ·
                  refine ⟨1660919587132430246657555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107279724754953497771703 1660919587132430246657555)
                  ·
                    refine ⟨2491379380698645369986333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1660919587132430246657555 2491379380698645369986333)
                    ·
                      refine ⟨934267267761992013744875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2491379380698645369986333 934267267761992013744875)
                      ·
                        rfl

theorem cell23_1819479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_1819479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819479 prefixEnd_1819479 := by exact prefixLift 1819479
  have htrace : WordTrace (prefixWord ++ tailWord_1819479) baseStart_1819479 baseEnd_1819479 := by
    simpa [prefixWord, tailWord_1819479, baseEnd_1819479] using wordTrace_append hprefix tailTrace_1819479
  have hstable : (prefixWord ++ tailWord_1819479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819479).length < 2 ^ (prefixWord ++ tailWord_1819479).sum := by decide
  have hdescent : baseEnd_1819479 < baseStart_1819479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819491 : List Nat := [1, 1, 1, 5, 3, 1, 3, 8]
def baseStart_1819491 : Nat := 118140960795 + 1819491 * 2 ^ 59
def prefixEnd_1819491 : Nat := 4983230072969 + 3 ^ 40 * 1819491 * 2
def baseEnd_1819491 : Nat := 34602719612216517288697

theorem tailTrace_1819491 : CollatzResearch.WordTrace tailWord_1819491 prefixEnd_1819491 34602719612216517288697 := by
  unfold tailWord_1819491
  simp only [CollatzResearch.WordTrace]
  refine ⟨66362288651302326168290327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44241525767534884112193551 66362288651302326168290327)
  ·
    refine ⟨99543432976953489252435491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66362288651302326168290327 99543432976953489252435491)
    ·
      refine ⟨149315149465430233878653237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99543432976953489252435491 149315149465430233878653237)
      ·
        refine ⟨13998295262384084426123741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149315149465430233878653237 13998295262384084426123741)
        ·
          refine ⟨5249360723394031659796403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13998295262384084426123741 5249360723394031659796403)
          ·
            refine ⟨7874041085091047489694605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249360723394031659796403 7874041085091047489694605)
            ·
              refine ⟨2952765406909142808635477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7874041085091047489694605 2952765406909142808635477)
              ·
                refine ⟨34602719612216517288697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2952765406909142808635477 34602719612216517288697)
                ·
                  rfl

theorem cell23_1819491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 8].length) (baseStart_1819491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819491 prefixEnd_1819491 := by exact prefixLift 1819491
  have htrace : WordTrace (prefixWord ++ tailWord_1819491) baseStart_1819491 baseEnd_1819491 := by
    simpa [prefixWord, tailWord_1819491, baseEnd_1819491] using wordTrace_append hprefix tailTrace_1819491
  have hstable : (prefixWord ++ tailWord_1819491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819491).length < 2 ^ (prefixWord ++ tailWord_1819491).sum := by decide
  have hdescent : baseEnd_1819491 < baseStart_1819491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819561 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_1819561 : Nat := 118140960795 + 1819561 * 2 ^ 59
def prefixEnd_1819561 : Nat := 4983230072969 + 3 ^ 40 * 1819561 * 2
def baseEnd_1819561 : Nat := 934309373175660692919497

theorem tailTrace_1819561 : CollatzResearch.WordTrace tailWord_1819561 prefixEnd_1819561 934309373175660692919497 := by
  unfold tailWord_1819561
  simp only [CollatzResearch.WordTrace]
  refine ⟨66364841761048728123338537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44243227840699152082225691 66364841761048728123338537)
  ·
    refine ⟨49773631320786546092503903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66364841761048728123338537 49773631320786546092503903)
    ·
      refine ⟨74660446981179819138755855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49773631320786546092503903 74660446981179819138755855)
      ·
        refine ⟨111990670471769728708133783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74660446981179819138755855 111990670471769728708133783)
        ·
          refine ⟨167986005707654593062200675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111990670471769728708133783 167986005707654593062200675)
          ·
            refine ⟨251979008561481889593301013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167986005707654593062200675 251979008561481889593301013)
            ·
              refine ⟨11811516026319463574685985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 251979008561481889593301013 11811516026319463574685985)
              ·
                refine ⟨8858637019739597681014489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11811516026319463574685985 8858637019739597681014489)
                ·
                  refine ⟨6643977764804698260760867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8858637019739597681014489 6643977764804698260760867)
                  ·
                    refine ⟨9965966647207047391141301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6643977764804698260760867 9965966647207047391141301)
                    ·
                      refine ⟨934309373175660692919497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9965966647207047391141301 934309373175660692919497)
                      ·
                        rfl

theorem cell23_1819561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_1819561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819561 prefixEnd_1819561 := by exact prefixLift 1819561
  have htrace : WordTrace (prefixWord ++ tailWord_1819561) baseStart_1819561 baseEnd_1819561 := by
    simpa [prefixWord, tailWord_1819561, baseEnd_1819561] using wordTrace_append hprefix tailTrace_1819561
  have hstable : (prefixWord ++ tailWord_1819561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819561).length < 2 ^ (prefixWord ++ tailWord_1819561).sum := by decide
  have hdescent : baseEnd_1819561 < baseStart_1819561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819571 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 4]
def baseStart_1819571 : Nat := 118140960795 + 1819571 * 2 ^ 59
def prefixEnd_1819571 : Nat := 4983230072969 + 3 ^ 40 * 1819571 * 2
def baseEnd_1819571 : Nat := 934314507982205653794451

theorem tailTrace_1819571 : CollatzResearch.WordTrace tailWord_1819571 prefixEnd_1819571 934314507982205653794451 := by
  unfold tailWord_1819571
  simp only [CollatzResearch.WordTrace]
  refine ⟨66365206491012499831202567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44243470994008333220801711 66365206491012499831202567)
  ·
    refine ⟨99547809736518749746803851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66365206491012499831202567 99547809736518749746803851)
    ·
      refine ⟨149321714604778124620205777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99547809736518749746803851 149321714604778124620205777)
      ·
        refine ⟨111991285953583593465154333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149321714604778124620205777 111991285953583593465154333)
        ·
          refine ⟨41996732232593847549432875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111991285953583593465154333 41996732232593847549432875)
          ·
            refine ⟨62995098348890771324149313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41996732232593847549432875 62995098348890771324149313)
            ·
              refine ⟨47246323761668078493111985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62995098348890771324149313 47246323761668078493111985)
              ·
                refine ⟨35434742821251058869833989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47246323761668078493111985 35434742821251058869833989)
                ·
                  refine ⟨6644014278984573538093873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35434742821251058869833989 6644014278984573538093873)
                  ·
                    refine ⟨4983010709238430153570405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6644014278984573538093873 4983010709238430153570405)
                    ·
                      refine ⟨934314507982205653794451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4983010709238430153570405 934314507982205653794451)
                      ·
                        rfl

theorem cell23_1819571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_1819571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819571 prefixEnd_1819571 := by exact prefixLift 1819571
  have htrace : WordTrace (prefixWord ++ tailWord_1819571) baseStart_1819571 baseEnd_1819571 := by
    simpa [prefixWord, tailWord_1819571, baseEnd_1819571] using wordTrace_append hprefix tailTrace_1819571
  have hstable : (prefixWord ++ tailWord_1819571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819571).length < 2 ^ (prefixWord ++ tailWord_1819571).sum := by decide
  have hdescent : baseEnd_1819571 < baseStart_1819571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819575 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 4, 2, 2]
def baseStart_1819575 : Nat := 118140960795 + 1819575 * 2 ^ 59
def prefixEnd_1819575 : Nat := 4983230072969 + 3 ^ 40 * 1819575 * 2
def baseEnd_1819575 : Nat := 934316561904823638144433

theorem tailTrace_1819575 : CollatzResearch.WordTrace tailWord_1819575 prefixEnd_1819575 934316561904823638144433 := by
  unfold tailWord_1819575
  simp only [CollatzResearch.WordTrace]
  refine ⟨66365352382998008514348179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44243568255332005676232119 66365352382998008514348179)
  ·
    refine ⟨99548028574497012771522269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66365352382998008514348179 99548028574497012771522269)
    ·
      refine ⟨37330510715436379789320851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99548028574497012771522269 37330510715436379789320851)
      ·
        refine ⟨55995766073154569683981277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37330510715436379789320851 55995766073154569683981277)
        ·
          refine ⟨20998412277432963631492979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55995766073154569683981277 20998412277432963631492979)
          ·
            refine ⟨31497618416149445447239469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20998412277432963631492979 31497618416149445447239469)
            ·
              refine ⟨11811606906056042042714801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31497618416149445447239469 11811606906056042042714801)
              ·
                refine ⟨8858705179542031532036101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11811606906056042042714801 8858705179542031532036101)
                ·
                  refine ⟨1661007221164130912256769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8858705179542031532036101 1661007221164130912256769)
                  ·
                    refine ⟨1245755415873098184192577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1661007221164130912256769 1245755415873098184192577)
                    ·
                      refine ⟨934316561904823638144433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245755415873098184192577 934316561904823638144433)
                      ·
                        rfl

theorem cell23_1819575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_1819575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819575 prefixEnd_1819575 := by exact prefixLift 1819575
  have htrace : WordTrace (prefixWord ++ tailWord_1819575) baseStart_1819575 baseEnd_1819575 := by
    simpa [prefixWord, tailWord_1819575, baseEnd_1819575] using wordTrace_append hprefix tailTrace_1819575
  have hstable : (prefixWord ++ tailWord_1819575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819575).length < 2 ^ (prefixWord ++ tailWord_1819575).sum := by decide
  have hdescent : baseEnd_1819575 < baseStart_1819575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819598 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_1819598 : Nat := 118140960795 + 1819598 * 2 ^ 59
def prefixEnd_1819598 : Nat := 4983230072969 + 3 ^ 40 * 1819598 * 2
def baseEnd_1819598 : Nat := 103814263551097449795203

theorem tailTrace_1819598 : CollatzResearch.WordTrace tailWord_1819598 prefixEnd_1819598 103814263551097449795203 := by
  unfold tailWord_1819598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295773907739335430304431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44244127507943122294956965 8295773907739335430304431)
  ·
    refine ⟨12443660861609003145456647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8295773907739335430304431 12443660861609003145456647)
    ·
      refine ⟨18665491292413504718184971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12443660861609003145456647 18665491292413504718184971)
      ·
        refine ⟨27998236938620257077277457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18665491292413504718184971 27998236938620257077277457)
        ·
          refine ⟨20998677703965192807958093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27998236938620257077277457 20998677703965192807958093)
          ·
            refine ⟨7874504138986947302984285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20998677703965192807958093 7874504138986947302984285)
            ·
              refine ⟨2952939052120105238619107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7874504138986947302984285 2952939052120105238619107)
              ·
                refine ⟨4429408578180157857928661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952939052120105238619107 4429408578180157857928661)
                ·
                  refine ⟨103814263551097449795203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4429408578180157857928661 103814263551097449795203)
                  ·
                    rfl

theorem cell23_1819598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_1819598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819598 prefixEnd_1819598 := by exact prefixLift 1819598
  have htrace : WordTrace (prefixWord ++ tailWord_1819598) baseStart_1819598 baseEnd_1819598 := by
    simpa [prefixWord, tailWord_1819598, baseEnd_1819598] using wordTrace_append hprefix tailTrace_1819598
  have hstable : (prefixWord ++ tailWord_1819598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819598).length < 2 ^ (prefixWord ++ tailWord_1819598).sum := by decide
  have hdescent : baseEnd_1819598 < baseStart_1819598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819609 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 2, 2, 2]
def baseStart_1819609 : Nat := 118140960795 + 1819609 * 2 ^ 59
def prefixEnd_1819609 : Nat := 4983230072969 + 3 ^ 40 * 1819609 * 2
def baseEnd_1819609 : Nat := 934334020247076505119277

theorem tailTrace_1819609 : CollatzResearch.WordTrace tailWord_1819609 prefixEnd_1819609 934334020247076505119277 := by
  unfold tailWord_1819609
  simp only [CollatzResearch.WordTrace]
  refine ⟨66366592464874832321085881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44244394976583221547390587 66366592464874832321085881)
  ·
    refine ⟨49774944348656124240814411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66366592464874832321085881 49774944348656124240814411)
    ·
      refine ⟨74662416522984186361221617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49774944348656124240814411 74662416522984186361221617)
      ·
        refine ⟨55996812392238139770916213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74662416522984186361221617 55996812392238139770916213)
        ·
          refine ⟨5249701161772325603523395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55996812392238139770916213 5249701161772325603523395)
          ·
            refine ⟨7874551742658488405285093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249701161772325603523395 7874551742658488405285093)
            ·
              refine ⟨1476478451748466575990955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7874551742658488405285093 1476478451748466575990955)
              ·
                refine ⟨2214717677622699863986433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476478451748466575990955 2214717677622699863986433)
                ·
                  refine ⟨1661038258217024897989825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2214717677622699863986433 1661038258217024897989825)
                  ·
                    refine ⟨1245778693662768673492369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1661038258217024897989825 1245778693662768673492369)
                    ·
                      refine ⟨934334020247076505119277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1245778693662768673492369 934334020247076505119277)
                      ·
                        rfl

theorem cell23_1819609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_1819609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819609 prefixEnd_1819609 := by exact prefixLift 1819609
  have htrace : WordTrace (prefixWord ++ tailWord_1819609) baseStart_1819609 baseEnd_1819609 := by
    simpa [prefixWord, tailWord_1819609, baseEnd_1819609] using wordTrace_append hprefix tailTrace_1819609
  have hstable : (prefixWord ++ tailWord_1819609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819609).length < 2 ^ (prefixWord ++ tailWord_1819609).sum := by decide
  have hdescent : baseEnd_1819609 < baseStart_1819609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819682 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_1819682 : Nat := 118140960795 + 1819682 * 2 ^ 59
def prefixEnd_1819682 : Nat := 4983230072969 + 3 ^ 40 * 1819682 * 2
def baseEnd_1819682 : Nat := 934371504334854719506441

theorem tailTrace_1819682 : CollatzResearch.WordTrace tailWord_1819682 prefixEnd_1819682 934371504334854719506441 := by
  unfold tailWord_1819682
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592313748402591447123325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44246169995740243858995533 16592313748402591447123325)
  ·
    refine ⟨6222117655650971792671247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16592313748402591447123325 6222117655650971792671247)
    ·
      refine ⟨9333176483476457689006871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6222117655650971792671247 9333176483476457689006871)
      ·
        refine ⟨13999764725214686533510307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9333176483476457689006871 13999764725214686533510307)
        ·
          refine ⟨20999647087822029800265461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13999764725214686533510307 20999647087822029800265461)
          ·
            refine ⟨1968716914483315293774887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20999647087822029800265461 1968716914483315293774887)
            ·
              refine ⟨2953075371724972940662331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968716914483315293774887 2953075371724972940662331)
              ·
                refine ⟨4429613057587459410993497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953075371724972940662331 4429613057587459410993497)
                ·
                  refine ⟨3322209793190594558245123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4429613057587459410993497 3322209793190594558245123)
                  ·
                    refine ⟨4983314689785891837367685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3322209793190594558245123 4983314689785891837367685)
                    ·
                      refine ⟨934371504334854719506441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4983314689785891837367685 934371504334854719506441)
                      ·
                        rfl

theorem cell23_1819682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_1819682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819682 prefixEnd_1819682 := by exact prefixLift 1819682
  have htrace : WordTrace (prefixWord ++ tailWord_1819682) baseStart_1819682 baseEnd_1819682 := by
    simpa [prefixWord, tailWord_1819682, baseEnd_1819682] using wordTrace_append hprefix tailTrace_1819682
  have hstable : (prefixWord ++ tailWord_1819682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819682).length < 2 ^ (prefixWord ++ tailWord_1819682).sum := by decide
  have hdescent : baseEnd_1819682 < baseStart_1819682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819692 : List Nat := [2, 2, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_1819692 : Nat := 118140960795 + 1819692 * 2 ^ 59
def prefixEnd_1819692 : Nat := 4983230072969 + 3 ^ 40 * 1819692 * 2
def baseEnd_1819692 : Nat := 311458879713799893460465

theorem tailTrace_1819692 : CollatzResearch.WordTrace tailWord_1819692 prefixEnd_1819692 311458879713799893460465 := by
  unfold tailWord_1819692
  simp only [CollatzResearch.WordTrace]
  refine ⟨33184809861787068748178665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44246413149049424997571553 33184809861787068748178665)
  ·
    refine ⟨24888607396340301561133999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33184809861787068748178665 24888607396340301561133999)
    ·
      refine ⟨37332911094510452341700999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24888607396340301561133999 37332911094510452341700999)
      ·
        refine ⟨55999366641765678512551499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37332911094510452341700999 55999366641765678512551499)
        ·
          refine ⟨83999049962648517768827249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55999366641765678512551499 83999049962648517768827249)
          ·
            refine ⟨62999287471986388326620437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83999049962648517768827249 62999287471986388326620437)
            ·
              refine ⟨2953091600249361952810333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62999287471986388326620437 2953091600249361952810333)
              ·
                refine ⟨1107409350093510732303875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2953091600249361952810333 1107409350093510732303875)
                ·
                  refine ⟨1661114025140266098455813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107409350093510732303875 1661114025140266098455813)
                  ·
                    refine ⟨311458879713799893460465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1661114025140266098455813 311458879713799893460465)
                    ·
                      rfl

theorem cell23_1819692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_1819692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819692 prefixEnd_1819692 := by exact prefixLift 1819692
  have htrace : WordTrace (prefixWord ++ tailWord_1819692) baseStart_1819692 baseEnd_1819692 := by
    simpa [prefixWord, tailWord_1819692, baseEnd_1819692] using wordTrace_append hprefix tailTrace_1819692
  have hstable : (prefixWord ++ tailWord_1819692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819692).length < 2 ^ (prefixWord ++ tailWord_1819692).sum := by decide
  have hdescent : baseEnd_1819692 < baseStart_1819692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819705 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 6]
def baseStart_1819705 : Nat := 118140960795 + 1819705 * 2 ^ 59
def prefixEnd_1819705 : Nat := 4983230072969 + 3 ^ 40 * 1819705 * 2
def baseEnd_1819705 : Nat := 103820368265545347724315

theorem tailTrace_1819705 : CollatzResearch.WordTrace tailWord_1819705 prefixEnd_1819705 103820368265545347724315 := by
  unfold tailWord_1819705
  simp only [CollatzResearch.WordTrace]
  refine ⟨66370093872527040716580569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44246729248351360477720379 66370093872527040716580569)
  ·
    refine ⟨49777570404395280537435427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66370093872527040716580569 49777570404395280537435427)
    ·
      refine ⟨74666355606592920806153141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49777570404395280537435427 74666355606592920806153141)
      ·
        refine ⟨6999970838118086325576857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74666355606592920806153141 6999970838118086325576857)
        ·
          refine ⟨5249978128588564744182643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6999970838118086325576857 5249978128588564744182643)
          ·
            refine ⟨7874967192882847116273965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249978128588564744182643 7874967192882847116273965)
            ·
              refine ⟨2953112697331067668602737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7874967192882847116273965 2953112697331067668602737)
              ·
                refine ⟨2214834522998300751452053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953112697331067668602737 2214834522998300751452053)
                ·
                  refine ⟨103820368265545347724315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2214834522998300751452053 103820368265545347724315)
                  ·
                    rfl

theorem cell23_1819705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 6].length) (baseStart_1819705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819705 prefixEnd_1819705 := by exact prefixLift 1819705
  have htrace : WordTrace (prefixWord ++ tailWord_1819705) baseStart_1819705 baseEnd_1819705 := by
    simpa [prefixWord, tailWord_1819705, baseEnd_1819705] using wordTrace_append hprefix tailTrace_1819705
  have hstable : (prefixWord ++ tailWord_1819705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819705).length < 2 ^ (prefixWord ++ tailWord_1819705).sum := by decide
  have hdescent : baseEnd_1819705 < baseStart_1819705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819708 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1819708 : Nat := 118140960795 + 1819708 * 2 ^ 59
def prefixEnd_1819708 : Nat := 4983230072969 + 3 ^ 40 * 1819708 * 2
def baseEnd_1819708 : Nat := 934384854831871617781321

theorem tailTrace_1819708 : CollatzResearch.WordTrace tailWord_1819708 prefixEnd_1819708 934384854831871617781321 := by
  unfold tailWord_1819708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33185101645758086114469889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44246802194344114819293185 33185101645758086114469889)
  ·
    refine ⟨24888826234318564585852417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33185101645758086114469889 24888826234318564585852417)
    ·
      refine ⟨18666619675738923439389313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24888826234318564585852417 18666619675738923439389313)
      ·
        refine ⟨13999964756804192579541985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18666619675738923439389313 13999964756804192579541985)
        ·
          refine ⟨10499973567603144434656489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13999964756804192579541985 10499973567603144434656489)
          ·
            refine ⟨7874980175702358325992367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10499973567603144434656489 7874980175702358325992367)
            ·
              refine ⟨11812470263553537488988551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7874980175702358325992367 11812470263553537488988551)
              ·
                refine ⟨17718705395330306233482827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812470263553537488988551 17718705395330306233482827)
                ·
                  refine ⟨26578058092995459350224241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17718705395330306233482827 26578058092995459350224241)
                  ·
                    refine ⟨19933543569746594512668181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26578058092995459350224241 19933543569746594512668181)
                    ·
                      refine ⟨934384854831871617781321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19933543569746594512668181 934384854831871617781321)
                      ·
                        rfl

theorem cell23_1819708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1819708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819708 prefixEnd_1819708 := by exact prefixLift 1819708
  have htrace : WordTrace (prefixWord ++ tailWord_1819708) baseStart_1819708 baseEnd_1819708 := by
    simpa [prefixWord, tailWord_1819708, baseEnd_1819708] using wordTrace_append hprefix tailTrace_1819708
  have hstable : (prefixWord ++ tailWord_1819708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819708).length < 2 ^ (prefixWord ++ tailWord_1819708).sum := by decide
  have hdescent : baseEnd_1819708 < baseStart_1819708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819732 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_1819732 : Nat := 118140960795 + 1819732 * 2 ^ 59
def prefixEnd_1819732 : Nat := 4983230072969 + 3 ^ 40 * 1819732 * 2
def baseEnd_1819732 : Nat := 934397178367579523881211

theorem tailTrace_1819732 : CollatzResearch.WordTrace tailWord_1819732 prefixEnd_1819732 934397178367579523881211 := by
  unfold tailWord_1819732
  simp only [CollatzResearch.WordTrace]
  refine ⟨33185539321714612163906725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44247385762286149551875633 33185539321714612163906725)
  ·
    refine ⟨6222288622821489780732511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33185539321714612163906725 6222288622821489780732511)
    ·
      refine ⟨9333432934232234671098767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6222288622821489780732511 9333432934232234671098767)
      ·
        refine ⟨14000149401348352006648151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9333432934232234671098767 14000149401348352006648151)
        ·
          refine ⟨21000224102022528009972227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14000149401348352006648151 21000224102022528009972227)
          ·
            refine ⟨31500336153033792014958341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21000224102022528009972227 31500336153033792014958341)
            ·
              refine ⟨5906313028693836002804689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31500336153033792014958341 5906313028693836002804689)
              ·
                refine ⟨4429734771520377002103517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5906313028693836002804689 4429734771520377002103517)
                ·
                  refine ⟨1661150539320141375788819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4429734771520377002103517 1661150539320141375788819)
                  ·
                    refine ⟨2491725808980212063683229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1661150539320141375788819 2491725808980212063683229)
                    ·
                      refine ⟨934397178367579523881211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2491725808980212063683229 934397178367579523881211)
                      ·
                        rfl

theorem cell23_1819732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_1819732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819732 prefixEnd_1819732 := by exact prefixLift 1819732
  have htrace : WordTrace (prefixWord ++ tailWord_1819732) baseStart_1819732 baseEnd_1819732 := by
    simpa [prefixWord, tailWord_1819732, baseEnd_1819732] using wordTrace_append hprefix tailTrace_1819732
  have hstable : (prefixWord ++ tailWord_1819732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819732).length < 2 ^ (prefixWord ++ tailWord_1819732).sum := by decide
  have hdescent : baseEnd_1819732 < baseStart_1819732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819748 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_1819748 : Nat := 118140960795 + 1819748 * 2 ^ 59
def prefixEnd_1819748 : Nat := 4983230072969 + 3 ^ 40 * 1819748 * 2
def baseEnd_1819748 : Nat := 311468464686017153760379

theorem tailTrace_1819748 : CollatzResearch.WordTrace tailWord_1819748 prefixEnd_1819748 311468464686017153760379 := by
  unfold tailWord_1819748
  simp only [CollatzResearch.WordTrace]
  refine ⟨33185831105685629530197949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44247774807580839373597265 33185831105685629530197949)
  ·
    refine ⟨12444686664632111073824231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33185831105685629530197949 12444686664632111073824231)
    ·
      refine ⟨18667029996948166610736347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12444686664632111073824231 18667029996948166610736347)
      ·
        refine ⟨28000544995422249916104521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18667029996948166610736347 28000544995422249916104521)
        ·
          refine ⟨21000408746566687437078391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28000544995422249916104521 21000408746566687437078391)
          ·
            refine ⟨31500613119850031155617587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21000408746566687437078391 31500613119850031155617587)
            ·
              refine ⟨47250919679775046733426381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31500613119850031155617587 47250919679775046733426381)
              ·
                refine ⟨17719094879915642525034893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47250919679775046733426381 17719094879915642525034893)
                ·
                  refine ⟨6644660579968365946888085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17719094879915642525034893 6644660579968365946888085)
                  ·
                    refine ⟨311468464686017153760379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6644660579968365946888085 311468464686017153760379)
                    ·
                      rfl

theorem cell23_1819748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_1819748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819748 prefixEnd_1819748 := by exact prefixLift 1819748
  have htrace : WordTrace (prefixWord ++ tailWord_1819748) baseStart_1819748 baseEnd_1819748 := by
    simpa [prefixWord, tailWord_1819748, baseEnd_1819748] using wordTrace_append hprefix tailTrace_1819748
  have hstable : (prefixWord ++ tailWord_1819748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819748).length < 2 ^ (prefixWord ++ tailWord_1819748).sum := by decide
  have hdescent : baseEnd_1819748 < baseStart_1819748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819768 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1819768 : Nat := 118140960795 + 1819768 * 2 ^ 59
def prefixEnd_1819768 : Nat := 4983230072969 + 3 ^ 40 * 1819768 * 2
def baseEnd_1819768 : Nat := 934415663671141383031045

theorem tailTrace_1819768 : CollatzResearch.WordTrace tailWord_1819768 prefixEnd_1819768 934415663671141383031045 := by
  unfold tailWord_1819768
  simp only [CollatzResearch.WordTrace]
  refine ⟨33186195835649401238061979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44248261114199201650749305 33186195835649401238061979)
  ·
    refine ⟨49779293753474101857092969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33186195835649401238061979 49779293753474101857092969)
    ·
      refine ⟨37334470315105576392819727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49779293753474101857092969 37334470315105576392819727)
      ·
        refine ⟨56001705472658364589229591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37334470315105576392819727 56001705472658364589229591)
        ·
          refine ⟨84002558208987546883844387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56001705472658364589229591 84002558208987546883844387)
          ·
            refine ⟨126003837313481320325766581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84002558208987546883844387 126003837313481320325766581)
            ·
              refine ⟨11812859748138873780540617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126003837313481320325766581 11812859748138873780540617)
              ·
                refine ⟨8859644811104155335405463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11812859748138873780540617 8859644811104155335405463)
                ·
                  refine ⟨13289467216656233003108195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8859644811104155335405463 13289467216656233003108195)
                  ·
                    refine ⟨19934200824984349504662293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13289467216656233003108195 19934200824984349504662293)
                    ·
                      refine ⟨934415663671141383031045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19934200824984349504662293 934415663671141383031045)
                      ·
                        rfl

theorem cell23_1819768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1819768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819768 prefixEnd_1819768 := by exact prefixLift 1819768
  have htrace : WordTrace (prefixWord ++ tailWord_1819768) baseStart_1819768 baseEnd_1819768 := by
    simpa [prefixWord, tailWord_1819768, baseEnd_1819768] using wordTrace_append hprefix tailTrace_1819768
  have hstable : (prefixWord ++ tailWord_1819768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819768).length < 2 ^ (prefixWord ++ tailWord_1819768).sum := by decide
  have hdescent : baseEnd_1819768 < baseStart_1819768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819802 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1819802 : Nat := 118140960795 + 1819802 * 2 ^ 59
def prefixEnd_1819802 : Nat := 4983230072969 + 3 ^ 40 * 1819802 * 2
def baseEnd_1819802 : Nat := 934433122013394250005889

theorem tailTrace_1819802 : CollatzResearch.WordTrace tailWord_1819802 prefixEnd_1819802 934433122013394250005889 := by
  unfold tailWord_1819802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16593407938293906570715415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44249087835450417521907773 16593407938293906570715415)
  ·
    refine ⟨24890111907440859856073123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16593407938293906570715415 24890111907440859856073123)
    ·
      refine ⟨37335167861161289784109685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24890111907440859856073123 37335167861161289784109685)
      ·
        refine ⟨3500171986983870917260283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37335167861161289784109685 3500171986983870917260283)
        ·
          refine ⟨5250257980475806375890425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500171986983870917260283 5250257980475806375890425)
          ·
            refine ⟨3937693485356854781917819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5250257980475806375890425 3937693485356854781917819)
            ·
              refine ⟨5906540228035282172876729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937693485356854781917819 5906540228035282172876729)
              ·
                refine ⟨4429905171026461629657547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5906540228035282172876729 4429905171026461629657547)
                ·
                  refine ⟨6644857756539692444486321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429905171026461629657547 6644857756539692444486321)
                  ·
                    refine ⟨4983643317404769333364741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6644857756539692444486321 4983643317404769333364741)
                    ·
                      refine ⟨934433122013394250005889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4983643317404769333364741 934433122013394250005889)
                      ·
                        rfl

theorem cell23_1819802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1819802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819802 prefixEnd_1819802 := by exact prefixLift 1819802
  have htrace : WordTrace (prefixWord ++ tailWord_1819802) baseStart_1819802 baseEnd_1819802 := by
    simpa [prefixWord, tailWord_1819802, baseEnd_1819802] using wordTrace_append hprefix tailTrace_1819802
  have hstable : (prefixWord ++ tailWord_1819802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819802).length < 2 ^ (prefixWord ++ tailWord_1819802).sum := by decide
  have hdescent : baseEnd_1819802 < baseStart_1819802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819806 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_1819806 : Nat := 118140960795 + 1819806 * 2 ^ 59
def prefixEnd_1819806 : Nat := 4983230072969 + 3 ^ 40 * 1819806 * 2
def baseEnd_1819806 : Nat := 934435175936012234355871

theorem tailTrace_1819806 : CollatzResearch.WordTrace tailWord_1819806 prefixEnd_1819806 934435175936012234355871 := by
  unfold tailWord_1819806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296722205645141870750909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44249185096774089977338181 8296722205645141870750909)
  ·
    refine ⟨3111270827116928201531591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8296722205645141870750909 3111270827116928201531591)
    ·
      refine ⟨4666906240675392302297387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3111270827116928201531591 4666906240675392302297387)
      ·
        refine ⟨7000359361013088453446081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4666906240675392302297387 7000359361013088453446081)
        ·
          refine ⟨5250269520759816340084561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7000359361013088453446081 5250269520759816340084561)
          ·
            refine ⟨3937702140569862255063421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5250269520759816340084561 3937702140569862255063421)
            ·
              refine ⟨1476638302713698345648783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3937702140569862255063421 1476638302713698345648783)
              ·
                refine ⟨2214957454070547518473175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476638302713698345648783 2214957454070547518473175)
                ·
                  refine ⟨3322436181105821277709763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214957454070547518473175 3322436181105821277709763)
                  ·
                    refine ⟨4983654271658731916564645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3322436181105821277709763 4983654271658731916564645)
                    ·
                      refine ⟨934435175936012234355871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4983654271658731916564645 934435175936012234355871)
                      ·
                        rfl

theorem cell23_1819806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_1819806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819806 prefixEnd_1819806 := by exact prefixLift 1819806
  have htrace : WordTrace (prefixWord ++ tailWord_1819806) baseStart_1819806 baseEnd_1819806 := by
    simpa [prefixWord, tailWord_1819806, baseEnd_1819806] using wordTrace_append hprefix tailTrace_1819806
  have hstable : (prefixWord ++ tailWord_1819806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819806).length < 2 ^ (prefixWord ++ tailWord_1819806).sum := by decide
  have hdescent : baseEnd_1819806 < baseStart_1819806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819809 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_1819809 : Nat := 118140960795 + 1819809 * 2 ^ 59
def prefixEnd_1819809 : Nat := 4983230072969 + 3 ^ 40 * 1819809 * 2
def baseEnd_1819809 : Nat := 934436716377975722618357

theorem tailTrace_1819809 : CollatzResearch.WordTrace tailWord_1819809 prefixEnd_1819809 934436716377975722618357 := by
  unfold tailWord_1819809
  simp only [CollatzResearch.WordTrace]
  refine ⟨66373887064150266478366481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44249258042766844318910987 66373887064150266478366481)
  ·
    refine ⟨49780415298112699858774861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66373887064150266478366481 49780415298112699858774861)
    ·
      refine ⟨18667655736792262447040573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49780415298112699858774861 18667655736792262447040573)
      ·
        refine ⟨7000370901297098417640215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18667655736792262447040573 7000370901297098417640215)
        ·
          refine ⟨10500556351945647626460323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7000370901297098417640215 10500556351945647626460323)
          ·
            refine ⟨15750834527918471439690485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10500556351945647626460323 15750834527918471439690485)
            ·
              refine ⟨1476640736992356697470983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15750834527918471439690485 1476640736992356697470983)
              ·
                refine ⟨2214961105488535046206475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476640736992356697470983 2214961105488535046206475)
                ·
                  refine ⟨3322441658232802569309713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214961105488535046206475 3322441658232802569309713)
                  ·
                    refine ⟨2491831243674601926982285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3322441658232802569309713 2491831243674601926982285)
                    ·
                      refine ⟨934436716377975722618357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2491831243674601926982285 934436716377975722618357)
                      ·
                        rfl

theorem cell23_1819809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_1819809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819809 prefixEnd_1819809 := by exact prefixLift 1819809
  have htrace : WordTrace (prefixWord ++ tailWord_1819809) baseStart_1819809 baseEnd_1819809 := by
    simpa [prefixWord, tailWord_1819809, baseEnd_1819809] using wordTrace_append hprefix tailTrace_1819809
  have hstable : (prefixWord ++ tailWord_1819809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819809).length < 2 ^ (prefixWord ++ tailWord_1819809).sum := by decide
  have hdescent : baseEnd_1819809 < baseStart_1819809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819825 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 2, 7]
def baseStart_1819825 : Nat := 118140960795 + 1819825 * 2 ^ 59
def prefixEnd_1819825 : Nat := 4983230072969 + 3 ^ 40 * 1819825 * 2
def baseEnd_1819825 : Nat := 311481644022815886672761

theorem tailTrace_1819825 : CollatzResearch.WordTrace tailWord_1819825 prefixEnd_1819825 311481644022815886672761 := by
  unfold tailWord_1819825
  simp only [CollatzResearch.WordTrace]
  refine ⟨66374470632092301210948929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44249647088061534140632619 66374470632092301210948929)
  ·
    refine ⟨49780852974069225908211697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66374470632092301210948929 49780852974069225908211697)
    ·
      refine ⟨37335639730551919431158773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49780852974069225908211697 37335639730551919431158773)
      ·
        refine ⟨3500216224739242446671135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37335639730551919431158773 3500216224739242446671135)
        ·
          refine ⟨5250324337108863670006703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500216224739242446671135 5250324337108863670006703)
          ·
            refine ⟨7875486505663295505010055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250324337108863670006703 7875486505663295505010055)
            ·
              refine ⟨11813229758494943257515083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7875486505663295505010055 11813229758494943257515083)
              ·
                refine ⟨17719844637742414886272625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11813229758494943257515083 17719844637742414886272625)
                ·
                  refine ⟨13289883478306811164704469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17719844637742414886272625 13289883478306811164704469)
                  ·
                    refine ⟨311481644022815886672761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13289883478306811164704469 311481644022815886672761)
                    ·
                      rfl

theorem cell23_1819825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_1819825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819825 prefixEnd_1819825 := by exact prefixLift 1819825
  have htrace : WordTrace (prefixWord ++ tailWord_1819825) baseStart_1819825 baseEnd_1819825 := by
    simpa [prefixWord, tailWord_1819825, baseEnd_1819825] using wordTrace_append hprefix tailTrace_1819825
  have hstable : (prefixWord ++ tailWord_1819825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819825).length < 2 ^ (prefixWord ++ tailWord_1819825).sum := by decide
  have hdescent : baseEnd_1819825 < baseStart_1819825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819860 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1819860 : Nat := 118140960795 + 1819860 * 2 ^ 59
def prefixEnd_1819860 : Nat := 4983230072969 + 3 ^ 40 * 1819860 * 2
def baseEnd_1819860 : Nat := 934462903891355023080623

theorem tailTrace_1819860 : CollatzResearch.WordTrace tailWord_1819860 prefixEnd_1819860 934462903891355023080623 := by
  unfold tailWord_1819860
  simp only [CollatzResearch.WordTrace]
  refine ⟨33187873593482751094236517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44250498124643668125648689 33187873593482751094236517)
  ·
    refine ⟨6222726298778015830169347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33187873593482751094236517 6222726298778015830169347)
    ·
      refine ⟨9334089448167023745254021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6222726298778015830169347 9334089448167023745254021)
      ·
        refine ⟨1750141771531316952235129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9334089448167023745254021 1750141771531316952235129)
        ·
          refine ⟨1312606328648487714176347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1750141771531316952235129 1312606328648487714176347)
          ·
            refine ⟨1968909492972731571264521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312606328648487714176347 1968909492972731571264521)
            ·
              refine ⟨1476682119729548678448391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968909492972731571264521 1476682119729548678448391)
              ·
                refine ⟨2215023179594323017672587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476682119729548678448391 2215023179594323017672587)
                ·
                  refine ⟨3322534769391484526508881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215023179594323017672587 3322534769391484526508881)
                  ·
                    refine ⟨2491901077043613394881661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3322534769391484526508881 2491901077043613394881661)
                    ·
                      refine ⟨934462903891355023080623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2491901077043613394881661 934462903891355023080623)
                      ·
                        rfl

theorem cell23_1819860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1819860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819860 prefixEnd_1819860 := by exact prefixLift 1819860
  have htrace : WordTrace (prefixWord ++ tailWord_1819860) baseStart_1819860 baseEnd_1819860 := by
    simpa [prefixWord, tailWord_1819860, baseEnd_1819860] using wordTrace_append hprefix tailTrace_1819860
  have hstable : (prefixWord ++ tailWord_1819860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819860).length < 2 ^ (prefixWord ++ tailWord_1819860).sum := by decide
  have hdescent : baseEnd_1819860 < baseStart_1819860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819902 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_1819902 : Nat := 118140960795 + 1819902 * 2 ^ 59
def prefixEnd_1819902 : Nat := 4983230072969 + 3 ^ 40 * 1819902 * 2
def baseEnd_1819902 : Nat := 103831607786538206528381

theorem tailTrace_1819902 : CollatzResearch.WordTrace tailWord_1819902 prefixEnd_1819902 103831607786538206528381 := by
  unfold tailWord_1819902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297159881601667920187745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44251519368542228907667973 8297159881601667920187745)
  ·
    refine ⟨6222869911201250940140809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8297159881601667920187745 6222869911201250940140809)
    ·
      refine ⟨4667152433400938205105607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6222869911201250940140809 4667152433400938205105607)
      ·
        refine ⟨7000728650101407307658411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4667152433400938205105607 7000728650101407307658411)
        ·
          refine ⟨10501092975152110961487617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7000728650101407307658411 10501092975152110961487617)
          ·
            refine ⟨7875819731364083221115713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10501092975152110961487617 7875819731364083221115713)
            ·
              refine ⟨5906864798523062415836785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7875819731364083221115713 5906864798523062415836785)
              ·
                refine ⟨4430148598892296811877589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5906864798523062415836785 4430148598892296811877589)
                ·
                  refine ⟨103831607786538206528381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4430148598892296811877589 103831607786538206528381)
                  ·
                    rfl

theorem cell23_1819902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_1819902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819902 prefixEnd_1819902 := by exact prefixLift 1819902
  have htrace : WordTrace (prefixWord ++ tailWord_1819902) baseStart_1819902 baseEnd_1819902 := by
    simpa [prefixWord, tailWord_1819902, baseEnd_1819902] using wordTrace_append hprefix tailTrace_1819902
  have hstable : (prefixWord ++ tailWord_1819902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819902).length < 2 ^ (prefixWord ++ tailWord_1819902).sum := by decide
  have hdescent : baseEnd_1819902 < baseStart_1819902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819915 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 1, 7]
def baseStart_1819915 : Nat := 118140960795 + 1819915 * 2 ^ 59
def prefixEnd_1819915 : Nat := 4983230072969 + 3 ^ 40 * 1819915 * 2
def baseEnd_1819915 : Nat := 311497048442450769297623

theorem tailTrace_1819915 : CollatzResearch.WordTrace tailWord_1819915 prefixEnd_1819915 311497048442450769297623 := by
  unfold tailWord_1819915
  simp only [CollatzResearch.WordTrace]
  refine ⟨66377753201766246581725199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44251835467844164387816799 66377753201766246581725199)
  ·
    refine ⟨99566629802649369872587799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66377753201766246581725199 99566629802649369872587799)
    ·
      refine ⟨149349944703974054808881699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99566629802649369872587799 149349944703974054808881699)
      ·
        refine ⟨224024917055961082213322549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149349944703974054808881699 224024917055961082213322549)
        ·
          refine ⟨21002335973996351457498989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224024917055961082213322549 21002335973996351457498989)
          ·
            refine ⟨7875875990248631796562121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21002335973996351457498989 7875875990248631796562121)
            ·
              refine ⟨5906906992686473847421591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7875875990248631796562121 5906906992686473847421591)
              ·
                refine ⟨8860360489029710771132387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906906992686473847421591 8860360489029710771132387)
                ·
                  refine ⟨13290540733544566156698581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8860360489029710771132387 13290540733544566156698581)
                  ·
                    refine ⟨311497048442450769297623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13290540733544566156698581 311497048442450769297623)
                    ·
                      rfl

theorem cell23_1819915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 7].length) (baseStart_1819915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819915 prefixEnd_1819915 := by exact prefixLift 1819915
  have htrace : WordTrace (prefixWord ++ tailWord_1819915) baseStart_1819915 baseEnd_1819915 := by
    simpa [prefixWord, tailWord_1819915, baseEnd_1819915] using wordTrace_append hprefix tailTrace_1819915
  have hstable : (prefixWord ++ tailWord_1819915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819915).length < 2 ^ (prefixWord ++ tailWord_1819915).sum := by decide
  have hdescent : baseEnd_1819915 < baseStart_1819915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819925 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1819925 : Nat := 118140960795 + 1819925 * 2 ^ 59
def prefixEnd_1819925 : Nat := 4983230072969 + 3 ^ 40 * 1819925 * 2
def baseEnd_1819925 : Nat := 934496280133897268767823

theorem tailTrace_1819925 : CollatzResearch.WordTrace tailWord_1819925 prefixEnd_1819925 934496280133897268767823 := by
  unfold tailWord_1819925
  simp only [CollatzResearch.WordTrace]
  refine ⟨66378117931730018289589229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44252078621153345526392819 66378117931730018289589229)
  ·
    refine ⟨24891794224398756858595961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66378117931730018289589229 24891794224398756858595961)
    ·
      refine ⟨18668845668299067643946971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24891794224398756858595961 18668845668299067643946971)
      ·
        refine ⟨28003268502448601465920457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18668845668299067643946971 28003268502448601465920457)
        ·
          refine ⟨21002451376836451099440343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28003268502448601465920457 21002451376836451099440343)
          ·
            refine ⟨31503677065254676649160515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21002451376836451099440343 31503677065254676649160515)
            ·
              refine ⟨47255515597882014973740773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31503677065254676649160515 47255515597882014973740773)
              ·
                refine ⟨8860409174602877807576395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47255515597882014973740773 8860409174602877807576395)
                ·
                  refine ⟨13290613761904316711364593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8860409174602877807576395 13290613761904316711364593)
                  ·
                    refine ⟨9967960321428237533523445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13290613761904316711364593 9967960321428237533523445)
                    ·
                      refine ⟨934496280133897268767823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9967960321428237533523445 934496280133897268767823)
                      ·
                        rfl

theorem cell23_1819925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1819925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819925 prefixEnd_1819925 := by exact prefixLift 1819925
  have htrace : WordTrace (prefixWord ++ tailWord_1819925) baseStart_1819925 baseEnd_1819925 := by
    simpa [prefixWord, tailWord_1819925, baseEnd_1819925] using wordTrace_append hprefix tailTrace_1819925
  have hstable : (prefixWord ++ tailWord_1819925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819925).length < 2 ^ (prefixWord ++ tailWord_1819925).sum := by decide
  have hdescent : baseEnd_1819925 < baseStart_1819925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819936 : List Nat := [2, 1, 1, 5, 3, 1, 3, 2, 5]
def baseStart_1819936 : Nat := 118140960795 + 1819936 * 2 ^ 59
def prefixEnd_1819936 : Nat := 4983230072969 + 3 ^ 40 * 1819936 * 2
def baseEnd_1819936 : Nat := 103833547602344080636697

theorem tailTrace_1819936 : CollatzResearch.WordTrace tailWord_1819936 prefixEnd_1819936 103833547602344080636697 := by
  unfold tailWord_1819936
  simp only [CollatzResearch.WordTrace]
  refine ⟨33189259567345083584119831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44252346089793444778826441 33189259567345083584119831)
  ·
    refine ⟨49783889351017625376179747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33189259567345083584119831 49783889351017625376179747)
    ·
      refine ⟨74675834026526438064269621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49783889351017625376179747 74675834026526438064269621)
      ·
        refine ⟨7000859439986853568525277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74675834026526438064269621 7000859439986853568525277)
        ·
          refine ⟨2625322289995070088196979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7000859439986853568525277 2625322289995070088196979)
          ·
            refine ⟨3937983434992605132295469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625322289995070088196979 3937983434992605132295469)
            ·
              refine ⟨1476743788122226924610801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3937983434992605132295469 1476743788122226924610801)
              ·
                refine ⟨1107557841091670193458101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476743788122226924610801 1107557841091670193458101)
                ·
                  refine ⟨103833547602344080636697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1107557841091670193458101 103833547602344080636697)
                  ·
                    rfl

theorem cell23_1819936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 5].length) (baseStart_1819936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819936 prefixEnd_1819936 := by exact prefixLift 1819936
  have htrace : WordTrace (prefixWord ++ tailWord_1819936) baseStart_1819936 baseEnd_1819936 := by
    simpa [prefixWord, tailWord_1819936, baseEnd_1819936] using wordTrace_append hprefix tailTrace_1819936
  have hstable : (prefixWord ++ tailWord_1819936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819936).length < 2 ^ (prefixWord ++ tailWord_1819936).sum := by decide
  have hdescent : baseEnd_1819936 < baseStart_1819936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819952 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 1, 6, 2]
def baseStart_1819952 : Nat := 118140960795 + 1819952 * 2 ^ 59
def prefixEnd_1819952 : Nat := 4983230072969 + 3 ^ 40 * 1819952 * 2
def baseEnd_1819952 : Nat := 934510144111568663130199

theorem tailTrace_1819952 : CollatzResearch.WordTrace tailWord_1819952 prefixEnd_1819952 934510144111568663130199 := by
  unfold tailWord_1819952
  simp only [CollatzResearch.WordTrace]
  refine ⟨33189551351316100950411055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44252735135088134600548073 33189551351316100950411055)
  ·
    refine ⟨49784327026974151425616583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33189551351316100950411055 49784327026974151425616583)
    ·
      refine ⟨74676490540461227138424875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49784327026974151425616583 74676490540461227138424875)
      ·
        refine ⟨112014735810691840707637313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74676490540461227138424875 112014735810691840707637313)
        ·
          refine ⟨84011051858018880530727985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112014735810691840707637313 84011051858018880530727985)
          ·
            refine ⟨63008288893514160398045989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84011051858018880530727985 63008288893514160398045989)
            ·
              refine ⟨11814054167533905074633623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63008288893514160398045989 11814054167533905074633623)
              ·
                refine ⟨17721081251300857611950435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11814054167533905074633623 17721081251300857611950435)
                ·
                  refine ⟨26581621876951286417925653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17721081251300857611950435 26581621876951286417925653)
                  ·
                    refine ⟨1246013525482091550840265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26581621876951286417925653 1246013525482091550840265)
                    ·
                      refine ⟨934510144111568663130199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246013525482091550840265 934510144111568663130199)
                      ·
                        rfl

theorem cell23_1819952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 6, 2].length) (baseStart_1819952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819952 prefixEnd_1819952 := by exact prefixLift 1819952
  have htrace : WordTrace (prefixWord ++ tailWord_1819952) baseStart_1819952 baseEnd_1819952 := by
    simpa [prefixWord, tailWord_1819952, baseEnd_1819952] using wordTrace_append hprefix tailTrace_1819952
  have hstable : (prefixWord ++ tailWord_1819952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819952).length < 2 ^ (prefixWord ++ tailWord_1819952).sum := by decide
  have hdescent : baseEnd_1819952 < baseStart_1819952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819962 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_1819962 : Nat := 118140960795 + 1819962 * 2 ^ 59
def prefixEnd_1819962 : Nat := 4983230072969 + 3 ^ 40 * 1819962 * 2
def baseEnd_1819962 : Nat := 311505092972704541335051

theorem tailTrace_1819962 : CollatzResearch.WordTrace tailWord_1819962 prefixEnd_1819962 311505092972704541335051 := by
  unfold tailWord_1819962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16594866858148993402171535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44252978288397315739124093 16594866858148993402171535)
  ·
    refine ⟨24892300287223490103257303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16594866858148993402171535 24892300287223490103257303)
    ·
      refine ⟨37338450430835235154885955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24892300287223490103257303 37338450430835235154885955)
      ·
        refine ⟨56007675646252852732328933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37338450430835235154885955 56007675646252852732328933)
        ·
          refine ⟨10501439183672409887311675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56007675646252852732328933 10501439183672409887311675)
          ·
            refine ⟨15752158775508614830967513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10501439183672409887311675 15752158775508614830967513)
            ·
              refine ⟨11814119081631461123225635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15752158775508614830967513 11814119081631461123225635)
              ·
                refine ⟨17721178622447191684838453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11814119081631461123225635 17721178622447191684838453)
                ·
                  refine ⟨1661360495854424220453605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17721178622447191684838453 1661360495854424220453605)
                  ·
                    refine ⟨311505092972704541335051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1661360495854424220453605 311505092972704541335051)
                    ·
                      rfl

theorem cell23_1819962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_1819962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819962 prefixEnd_1819962 := by exact prefixLift 1819962
  have htrace : WordTrace (prefixWord ++ tailWord_1819962) baseStart_1819962 baseEnd_1819962 := by
    simpa [prefixWord, tailWord_1819962, baseEnd_1819962] using wordTrace_append hprefix tailTrace_1819962
  have hstable : (prefixWord ++ tailWord_1819962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819962).length < 2 ^ (prefixWord ++ tailWord_1819962).sum := by decide
  have hdescent : baseEnd_1819962 < baseStart_1819962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819969 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1819969 : Nat := 118140960795 + 1819969 * 2 ^ 59
def prefixEnd_1819969 : Nat := 4983230072969 + 3 ^ 40 * 1819969 * 2
def baseEnd_1819969 : Nat := 934518873282695096617621

theorem tailTrace_1819969 : CollatzResearch.WordTrace tailWord_1819969 prefixEnd_1819969 934518873282695096617621 := by
  unfold tailWord_1819969
  simp only [CollatzResearch.WordTrace]
  refine ⟨66379722743570613804190961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44253148495713742536127307 66379722743570613804190961)
  ·
    refine ⟨49784792057677960353143221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66379722743570613804190961 49784792057677960353143221)
    ·
      refine ⟨4667324255407308783107177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49784792057677960353143221 4667324255407308783107177)
      ·
        refine ⟨3500493191555481587330383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4667324255407308783107177 3500493191555481587330383)
        ·
          refine ⟨5250739787333222380995575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500493191555481587330383 5250739787333222380995575)
          ·
            refine ⟨7876109680999833571493363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250739787333222380995575 7876109680999833571493363)
            ·
              refine ⟨11814164521499750357240045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7876109680999833571493363 11814164521499750357240045)
              ·
                refine ⟨4430311695562406383965017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11814164521499750357240045 4430311695562406383965017)
                ·
                  refine ⟨3322733771671804787973763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4430311695562406383965017 3322733771671804787973763)
                  ·
                    refine ⟨4984100657507707181960645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3322733771671804787973763 4984100657507707181960645)
                    ·
                      refine ⟨934518873282695096617621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4984100657507707181960645 934518873282695096617621)
                      ·
                        rfl

theorem cell23_1819969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1819969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819969 prefixEnd_1819969 := by exact prefixLift 1819969
  have htrace : WordTrace (prefixWord ++ tailWord_1819969) baseStart_1819969 baseEnd_1819969 := by
    simpa [prefixWord, tailWord_1819969, baseEnd_1819969] using wordTrace_append hprefix tailTrace_1819969
  have hstable : (prefixWord ++ tailWord_1819969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819969).length < 2 ^ (prefixWord ++ tailWord_1819969).sum := by decide
  have hdescent : baseEnd_1819969 < baseStart_1819969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819989 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1819989 : Nat := 118140960795 + 1819989 * 2 ^ 59
def prefixEnd_1819989 : Nat := 4983230072969 + 3 ^ 40 * 1819989 * 2
def baseEnd_1819989 : Nat := 934529142895785018367529

theorem tailTrace_1819989 : CollatzResearch.WordTrace tailWord_1819989 prefixEnd_1819989 934529142895785018367529 := by
  unfold tailWord_1819989
  simp only [CollatzResearch.WordTrace]
  refine ⟨66380452203498157219919021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44253634802332104813279347 66380452203498157219919021)
  ·
    refine ⟨24892669576311808957469633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66380452203498157219919021 24892669576311808957469633)
    ·
      refine ⟨18669502182233856718102225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24892669576311808957469633 18669502182233856718102225)
      ·
        refine ⟨14002126636675392538576669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18669502182233856718102225 14002126636675392538576669)
        ·
          refine ⟨5250797488753272201966251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14002126636675392538576669 5250797488753272201966251)
          ·
            refine ⟨7876196233129908302949377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250797488753272201966251 7876196233129908302949377)
            ·
              refine ⟨5907147174847431227212033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7876196233129908302949377 5907147174847431227212033)
              ·
                refine ⟨4430360381135573420409025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5907147174847431227212033 4430360381135573420409025)
                ·
                  refine ⟨3322770285851680065306769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4430360381135573420409025 3322770285851680065306769)
                  ·
                    refine ⟨2492077714388760048980077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3322770285851680065306769 2492077714388760048980077)
                    ·
                      refine ⟨934529142895785018367529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2492077714388760048980077 934529142895785018367529)
                      ·
                        rfl

theorem cell23_1819989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1819989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819989 prefixEnd_1819989 := by exact prefixLift 1819989
  have htrace : WordTrace (prefixWord ++ tailWord_1819989) baseStart_1819989 baseEnd_1819989 := by
    simpa [prefixWord, tailWord_1819989, baseEnd_1819989] using wordTrace_append hprefix tailTrace_1819989
  have hstable : (prefixWord ++ tailWord_1819989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819989).length < 2 ^ (prefixWord ++ tailWord_1819989).sum := by decide
  have hdescent : baseEnd_1819989 < baseStart_1819989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819992 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 6]
def baseStart_1819992 : Nat := 118140960795 + 1819992 * 2 ^ 59
def prefixEnd_1819992 : Nat := 4983230072969 + 3 ^ 40 * 1819992 * 2
def baseEnd_1819992 : Nat := 103836742593083167403335

theorem tailTrace_1819992 : CollatzResearch.WordTrace tailWord_1819992 prefixEnd_1819992 103836742593083167403335 := by
  unfold tailWord_1819992
  simp only [CollatzResearch.WordTrace]
  refine ⟨33190280811243644366139115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44253707748324859154852153 33190280811243644366139115)
  ·
    refine ⟨49785421216865466549208673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33190280811243644366139115 49785421216865466549208673)
    ·
      refine ⟨37339065912649099911906505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49785421216865466549208673 37339065912649099911906505)
      ·
        refine ⟨28004299434486824933929879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37339065912649099911906505 28004299434486824933929879)
        ·
          refine ⟨42006449151730237400894819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28004299434486824933929879 42006449151730237400894819)
          ·
            refine ⟨63009673727595356101342229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42006449151730237400894819 63009673727595356101342229)
            ·
              refine ⟨2953578455981032317250417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63009673727595356101342229 2953578455981032317250417)
              ·
                refine ⟨2215183841985774237937813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953578455981032317250417 2215183841985774237937813)
                ·
                  refine ⟨103836742593083167403335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2215183841985774237937813 103836742593083167403335)
                  ·
                    rfl

theorem cell23_1819992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 6].length) (baseStart_1819992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1819992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1819992 prefixEnd_1819992 := by exact prefixLift 1819992
  have htrace : WordTrace (prefixWord ++ tailWord_1819992) baseStart_1819992 baseEnd_1819992 := by
    simpa [prefixWord, tailWord_1819992, baseEnd_1819992] using wordTrace_append hprefix tailTrace_1819992
  have hstable : (prefixWord ++ tailWord_1819992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819992).length < 2 ^ (prefixWord ++ tailWord_1819992).sum := by decide
  have hdescent : baseEnd_1819992 < baseStart_1819992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820015 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_1820015 : Nat := 118140960795 + 1820015 * 2 ^ 59
def prefixEnd_1820015 : Nat := 4983230072969 + 3 ^ 40 * 1820015 * 2
def baseEnd_1820015 : Nat := 934542493392801916642409

theorem tailTrace_1820015 : CollatzResearch.WordTrace tailWord_1820015 prefixEnd_1820015 934542493392801916642409 := by
  unfold tailWord_1820015
  simp only [CollatzResearch.WordTrace]
  refine ⟨66381400501403963660365499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44254267000935975773576999 66381400501403963660365499)
  ·
    refine ⟨99572100752105945490548249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66381400501403963660365499 99572100752105945490548249)
    ·
      refine ⟨74679075564079459117911187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99572100752105945490548249 74679075564079459117911187)
      ·
        refine ⟨112018613346119188676866781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74679075564079459117911187 112018613346119188676866781)
        ·
          refine ⟨42006980004794695753825043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112018613346119188676866781 42006980004794695753825043)
          ·
            refine ⟨63010470007192043630737565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42006980004794695753825043 63010470007192043630737565)
            ·
              refine ⟨23628926252697016361526587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63010470007192043630737565 23628926252697016361526587)
              ·
                refine ⟨35443389379045524542289881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23628926252697016361526587 35443389379045524542289881)
                ·
                  refine ⟨26582542034284143406717411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35443389379045524542289881 26582542034284143406717411)
                  ·
                    refine ⟨39873813051426215110076117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26582542034284143406717411 39873813051426215110076117)
                    ·
                      refine ⟨934542493392801916642409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39873813051426215110076117 934542493392801916642409)
                      ·
                        rfl

theorem cell23_1820015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_1820015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820015 prefixEnd_1820015 := by exact prefixLift 1820015
  have htrace : WordTrace (prefixWord ++ tailWord_1820015) baseStart_1820015 baseEnd_1820015 := by
    simpa [prefixWord, tailWord_1820015, baseEnd_1820015] using wordTrace_append hprefix tailTrace_1820015
  have hstable : (prefixWord ++ tailWord_1820015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820015).length < 2 ^ (prefixWord ++ tailWord_1820015).sum := by decide
  have hdescent : baseEnd_1820015 < baseStart_1820015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820029 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_1820029 : Nat := 118140960795 + 1820029 * 2 ^ 59
def prefixEnd_1820029 : Nat := 4983230072969 + 3 ^ 40 * 1820029 * 2
def baseEnd_1820029 : Nat := 934549682121964861867345

theorem tailTrace_1820029 : CollatzResearch.WordTrace tailWord_1820029 prefixEnd_1820029 934549682121964861867345 := by
  unfold tailWord_1820029
  simp only [CollatzResearch.WordTrace]
  refine ⟨66381911123353244051375141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44254607415568829367583427 66381911123353244051375141)
  ·
    refine ⟨12446608335628733259632839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66381911123353244051375141 12446608335628733259632839)
    ·
      refine ⟨18669912503443099889449259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12446608335628733259632839 18669912503443099889449259)
      ·
        refine ⟨28004868755164649834173889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18669912503443099889449259 28004868755164649834173889)
        ·
          refine ⟨21003651566373487375630417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28004868755164649834173889 21003651566373487375630417)
          ·
            refine ⟨15752738674780115531722813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21003651566373487375630417 15752738674780115531722813)
            ·
              refine ⟨5907277003042543324396055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15752738674780115531722813 5907277003042543324396055)
              ·
                refine ⟨8860915504563814986594083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907277003042543324396055 8860915504563814986594083)
                ·
                  refine ⟨13291373256845722479891125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8860915504563814986594083 13291373256845722479891125)
                  ·
                    refine ⟨1246066242829286482489793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13291373256845722479891125 1246066242829286482489793)
                    ·
                      refine ⟨934549682121964861867345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246066242829286482489793 934549682121964861867345)
                      ·
                        rfl

theorem cell23_1820029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_1820029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820029 prefixEnd_1820029 := by exact prefixLift 1820029
  have htrace : WordTrace (prefixWord ++ tailWord_1820029) baseStart_1820029 baseEnd_1820029 := by
    simpa [prefixWord, tailWord_1820029, baseEnd_1820029] using wordTrace_append hprefix tailTrace_1820029
  have hstable : (prefixWord ++ tailWord_1820029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820029).length < 2 ^ (prefixWord ++ tailWord_1820029).sum := by decide
  have hdescent : baseEnd_1820029 < baseStart_1820029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820039 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 1, 5]
def baseStart_1820039 : Nat := 118140960795 + 1820039 * 2 ^ 59
def prefixEnd_1820039 : Nat := 4983230072969 + 3 ^ 40 * 1820039 * 2
def baseEnd_1820039 : Nat := 311518272309503274247433

theorem tailTrace_1820039 : CollatzResearch.WordTrace tailWord_1820039 prefixEnd_1820039 311518272309503274247433 := by
  unfold tailWord_1820039
  simp only [CollatzResearch.WordTrace]
  refine ⟨66382275853317015759239171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44254850568878010506159447 66382275853317015759239171)
  ·
    refine ⟨99573413779975523638858757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66382275853317015759239171 99573413779975523638858757)
    ·
      refine ⟨18670015083745410682286017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99573413779975523638858757 18670015083745410682286017)
      ·
        refine ⟨14002511312809058011714513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18670015083745410682286017 14002511312809058011714513)
        ·
          refine ⟨10501883484606793508785885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14002511312809058011714513 10501883484606793508785885)
          ·
            refine ⟨3938206306727547565794707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10501883484606793508785885 3938206306727547565794707)
            ·
              refine ⟨5907309460091321348692061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938206306727547565794707 5907309460091321348692061)
              ·
                refine ⟨2215241047534245505759523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5907309460091321348692061 2215241047534245505759523)
                ·
                  refine ⟨3322861571301368258639285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215241047534245505759523 3322861571301368258639285)
                  ·
                    refine ⟨311518272309503274247433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3322861571301368258639285 311518272309503274247433)
                    ·
                      rfl

theorem cell23_1820039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_1820039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820039 prefixEnd_1820039 := by exact prefixLift 1820039
  have htrace : WordTrace (prefixWord ++ tailWord_1820039) baseStart_1820039 baseEnd_1820039 := by
    simpa [prefixWord, tailWord_1820039, baseEnd_1820039] using wordTrace_append hprefix tailTrace_1820039
  have hstable : (prefixWord ++ tailWord_1820039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820039).length < 2 ^ (prefixWord ++ tailWord_1820039).sum := by decide
  have hdescent : baseEnd_1820039 < baseStart_1820039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820076 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 3, 2, 2]
def baseStart_1820076 : Nat := 118140960795 + 1820076 * 2 ^ 59
def prefixEnd_1820076 : Nat := 4983230072969 + 3 ^ 40 * 1820076 * 2
def baseEnd_1820076 : Nat := 934573815712726177979629

theorem tailTrace_1820076 : CollatzResearch.WordTrace tailWord_1820076 prefixEnd_1820076 934573815712726177979629 := by
  unfold tailWord_1820076
  simp only [CollatzResearch.WordTrace]
  refine ⟨33191812677091485539168041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44255750236121980718890721 33191812677091485539168041)
  ·
    refine ⟨24893859507818614154376031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33191812677091485539168041 24893859507818614154376031)
    ·
      refine ⟨37340789261727921231564047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24893859507818614154376031 37340789261727921231564047)
      ·
        refine ⟨56011183892591881847346071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37340789261727921231564047 56011183892591881847346071)
        ·
          refine ⟨84016775838887822771019107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56011183892591881847346071 84016775838887822771019107)
          ·
            refine ⟨126025163758331734156528661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84016775838887822771019107 126025163758331734156528661)
            ·
              refine ⟨5907429551171800038587281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126025163758331734156528661 5907429551171800038587281)
              ·
                refine ⟨4430572163378850028940461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5907429551171800038587281 4430572163378850028940461)
                ·
                  refine ⟨1661464561267068760852673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4430572163378850028940461 1661464561267068760852673)
                  ·
                    refine ⟨1246098420950301570639505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1661464561267068760852673 1246098420950301570639505)
                    ·
                      refine ⟨934573815712726177979629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246098420950301570639505 934573815712726177979629)
                      ·
                        rfl

theorem cell23_1820076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_1820076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820076 prefixEnd_1820076 := by exact prefixLift 1820076
  have htrace : WordTrace (prefixWord ++ tailWord_1820076) baseStart_1820076 baseEnd_1820076 := by
    simpa [prefixWord, tailWord_1820076, baseEnd_1820076] using wordTrace_append hprefix tailTrace_1820076
  have hstable : (prefixWord ++ tailWord_1820076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820076).length < 2 ^ (prefixWord ++ tailWord_1820076).sum := by decide
  have hdescent : baseEnd_1820076 < baseStart_1820076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820136 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_1820136 : Nat := 118140960795 + 1820136 * 2 ^ 59
def prefixEnd_1820136 : Nat := 4983230072969 + 3 ^ 40 * 1820136 * 2
def baseEnd_1820136 : Nat := 934604624551995943229353

theorem tailTrace_1820136 : CollatzResearch.WordTrace tailWord_1820136 prefixEnd_1820136 934604624551995943229353 := by
  unfold tailWord_1820136
  simp only [CollatzResearch.WordTrace]
  refine ⟨33192906866982800662760131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44257209155977067550346841 33192906866982800662760131)
  ·
    refine ⟨49789360300474200994140197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33192906866982800662760131 49789360300474200994140197)
    ·
      refine ⟨9335505056338912686401287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49789360300474200994140197 9335505056338912686401287)
      ·
        refine ⟨14003257584508369029601931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335505056338912686401287 14003257584508369029601931)
        ·
          refine ⟨21004886376762553544402897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14003257584508369029601931 21004886376762553544402897)
          ·
            refine ⟨15753664782571915158302173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21004886376762553544402897 15753664782571915158302173)
            ·
              refine ⟨5907624293464468184363315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15753664782571915158302173 5907624293464468184363315)
              ·
                refine ⟨8861436440196702276544973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907624293464468184363315 8861436440196702276544973)
                ·
                  refine ⟨3323038665073763353704365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8861436440196702276544973 3323038665073763353704365)
                  ·
                    refine ⟨1246139499402661257639137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323038665073763353704365 1246139499402661257639137)
                    ·
                      refine ⟨934604624551995943229353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246139499402661257639137 934604624551995943229353)
                      ·
                        rfl

theorem cell23_1820136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_1820136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820136 prefixEnd_1820136 := by exact prefixLift 1820136
  have htrace : WordTrace (prefixWord ++ tailWord_1820136) baseStart_1820136 baseEnd_1820136 := by
    simpa [prefixWord, tailWord_1820136, baseEnd_1820136] using wordTrace_append hprefix tailTrace_1820136
  have hstable : (prefixWord ++ tailWord_1820136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820136).length < 2 ^ (prefixWord ++ tailWord_1820136).sum := by decide
  have hdescent : baseEnd_1820136 < baseStart_1820136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820179 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 4]
def baseStart_1820179 : Nat := 118140960795 + 1820179 * 2 ^ 59
def prefixEnd_1820179 : Nat := 4983230072969 + 3 ^ 40 * 1820179 * 2
def baseEnd_1820179 : Nat := 934626704220139274991655

theorem tailTrace_1820179 : CollatzResearch.WordTrace tailWord_1820179 prefixEnd_1820179 934626704220139274991655 := by
  unfold tailWord_1820179
  simp only [CollatzResearch.WordTrace]
  refine ⟨66387382072809819669335591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44258254715206546446223727 66387382072809819669335591)
  ·
    refine ⟨99581073109214729504003387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66387382072809819669335591 99581073109214729504003387)
    ·
      refine ⟨149371609663822094256005081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99581073109214729504003387 149371609663822094256005081)
      ·
        refine ⟨112028707247866570692003811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149371609663822094256005081 112028707247866570692003811)
        ·
          refine ⟨168043060871799856038005717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112028707247866570692003811 168043060871799856038005717)
          ·
            refine ⟨3938509239182809125890759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168043060871799856038005717 3938509239182809125890759)
            ·
              refine ⟨5907763858774213688836139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938509239182809125890759 5907763858774213688836139)
              ·
                refine ⟨8861645788161320533254209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907763858774213688836139 8861645788161320533254209)
                ·
                  refine ⟨6646234341120990399940657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861645788161320533254209 6646234341120990399940657)
                  ·
                    refine ⟨4984675755840742799955493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6646234341120990399940657 4984675755840742799955493)
                    ·
                      refine ⟨934626704220139274991655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4984675755840742799955493 934626704220139274991655)
                      ·
                        rfl

theorem cell23_1820179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_1820179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820179 prefixEnd_1820179 := by exact prefixLift 1820179
  have htrace : WordTrace (prefixWord ++ tailWord_1820179) baseStart_1820179 baseEnd_1820179 := by
    simpa [prefixWord, tailWord_1820179, baseEnd_1820179] using wordTrace_append hprefix tailTrace_1820179
  have hstable : (prefixWord ++ tailWord_1820179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820179).length < 2 ^ (prefixWord ++ tailWord_1820179).sum := by decide
  have hdescent : baseEnd_1820179 < baseStart_1820179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820189 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 7]
def baseStart_1820189 : Nat := 118140960795 + 1820189 * 2 ^ 59
def prefixEnd_1820189 : Nat := 4983230072969 + 3 ^ 40 * 1820189 * 2
def baseEnd_1820189 : Nat := 103847982114076026207401

theorem tailTrace_1820189 : CollatzResearch.WordTrace tailWord_1820189 prefixEnd_1820189 103847982114076026207401 := by
  unfold tailWord_1820189
  simp only [CollatzResearch.WordTrace]
  refine ⟨66387746802773591377199621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44258497868515727584799747 66387746802773591377199621)
  ·
    refine ⟨12447702525520048383224929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66387746802773591377199621 12447702525520048383224929)
    ·
      refine ⟨9335776894140036287418697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12447702525520048383224929 9335776894140036287418697)
      ·
        refine ⟨7001832670605027215564023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9335776894140036287418697 7001832670605027215564023)
        ·
          refine ⟨10502749005907540823346035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7001832670605027215564023 10502749005907540823346035)
          ·
            refine ⟨15754123508861311235019053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502749005907540823346035 15754123508861311235019053)
            ·
              refine ⟨5907796315822991713132145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15754123508861311235019053 5907796315822991713132145)
              ·
                refine ⟨4430847236867243784849109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5907796315822991713132145 4430847236867243784849109)
                ·
                  refine ⟨103847982114076026207401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4430847236867243784849109 103847982114076026207401)
                  ·
                    rfl

theorem cell23_1820189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_1820189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820189 prefixEnd_1820189 := by exact prefixLift 1820189
  have htrace : WordTrace (prefixWord ++ tailWord_1820189) baseStart_1820189 baseEnd_1820189 := by
    simpa [prefixWord, tailWord_1820189, baseEnd_1820189] using wordTrace_append hprefix tailTrace_1820189
  have hstable : (prefixWord ++ tailWord_1820189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820189).length < 2 ^ (prefixWord ++ tailWord_1820189).sum := by decide
  have hdescent : baseEnd_1820189 < baseStart_1820189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820279 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 6]
def baseStart_1820279 : Nat := 118140960795 + 1820279 * 2 ^ 59
def prefixEnd_1820279 : Nat := 4983230072969 + 3 ^ 40 * 1820279 * 2
def baseEnd_1820279 : Nat := 103853116920620987082355

theorem tailTrace_1820279 : CollatzResearch.WordTrace tailWord_1820279 prefixEnd_1820279 103853116920620987082355 := by
  unfold tailWord_1820279
  simp only [CollatzResearch.WordTrace]
  refine ⟨66391029372447536747975891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44260686248298357831983927 66391029372447536747975891)
  ·
    refine ⟨99586544058671305121963837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66391029372447536747975891 99586544058671305121963837)
    ·
      refine ⟨37344954022001739420736439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99586544058671305121963837 37344954022001739420736439)
      ·
        refine ⟨56017431033002609131104659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37344954022001739420736439 56017431033002609131104659)
        ·
          refine ⟨84026146549503913696656989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56017431033002609131104659 84026146549503913696656989)
          ·
            refine ⟨31509804956063967636246371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84026146549503913696656989 31509804956063967636246371)
            ·
              refine ⟨47264707434095951454369557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31509804956063967636246371 47264707434095951454369557)
              ·
                refine ⟨2215533160973247724423573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47264707434095951454369557 2215533160973247724423573)
                ·
                  refine ⟨103853116920620987082355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2215533160973247724423573 103853116920620987082355)
                  ·
                    rfl

theorem cell23_1820279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 6].length) (baseStart_1820279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820279 prefixEnd_1820279 := by exact prefixLift 1820279
  have htrace : WordTrace (prefixWord ++ tailWord_1820279) baseStart_1820279 baseEnd_1820279 := by
    simpa [prefixWord, tailWord_1820279, baseEnd_1820279] using wordTrace_append hprefix tailTrace_1820279
  have hstable : (prefixWord ++ tailWord_1820279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820279).length < 2 ^ (prefixWord ++ tailWord_1820279).sum := by decide
  have hdescent : baseEnd_1820279 < baseStart_1820279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820339 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 3, 6]
def baseStart_1820339 : Nat := 118140960795 + 1820339 * 2 ^ 59
def prefixEnd_1820339 : Nat := 4983230072969 + 3 ^ 40 * 1820339 * 2
def baseEnd_1820339 : Nat := 311569620374952882996973

theorem tailTrace_1820339 : CollatzResearch.WordTrace tailWord_1820339 prefixEnd_1820339 311569620374952882996973 := by
  unfold tailWord_1820339
  simp only [CollatzResearch.WordTrace]
  refine ⟨66393217752230166995160071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44262145168153444663440047 66393217752230166995160071)
  ·
    refine ⟨99589826628345250492740107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66393217752230166995160071 99589826628345250492740107)
    ·
      refine ⟨149384739942517875739110161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99589826628345250492740107 149384739942517875739110161)
      ·
        refine ⟨112038554956888406804332621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149384739942517875739110161 112038554956888406804332621)
        ·
          refine ⟨42014458108833152551624733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112038554956888406804332621 42014458108833152551624733)
          ·
            refine ⟨15755421790812432206859275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42014458108833152551624733 15755421790812432206859275)
            ·
              refine ⟨23633132686218648310288913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15755421790812432206859275 23633132686218648310288913)
              ·
                refine ⟨17724849514663986232716685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23633132686218648310288913 17724849514663986232716685)
                ·
                  refine ⟨6646818567998994837268757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17724849514663986232716685 6646818567998994837268757)
                  ·
                    refine ⟨311569620374952882996973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6646818567998994837268757 311569620374952882996973)
                    ·
                      rfl

theorem cell23_1820339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 6].length) (baseStart_1820339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820339 prefixEnd_1820339 := by exact prefixLift 1820339
  have htrace : WordTrace (prefixWord ++ tailWord_1820339) baseStart_1820339 baseEnd_1820339 := by
    simpa [prefixWord, tailWord_1820339, baseEnd_1820339] using wordTrace_append hprefix tailTrace_1820339
  have hstable : (prefixWord ++ tailWord_1820339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820339).length < 2 ^ (prefixWord ++ tailWord_1820339).sum := by decide
  have hdescent : baseEnd_1820339 < baseStart_1820339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820346 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_1820346 : Nat := 118140960795 + 1820346 * 2 ^ 59
def prefixEnd_1820346 : Nat := 4983230072969 + 3 ^ 40 * 1820346 * 2
def baseEnd_1820346 : Nat := 934712455489440121603387

theorem tailTrace_1820346 : CollatzResearch.WordTrace tailWord_1820346 prefixEnd_1820346 934712455489440121603387 := by
  unfold tailWord_1820346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16598368265801201797666223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44262315375469871460443261 16598368265801201797666223)
  ·
    refine ⟨24897552398701802696499335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16598368265801201797666223 24897552398701802696499335)
    ·
      refine ⟨37346328598052704044749003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24897552398701802696499335 37346328598052704044749003)
      ·
        refine ⟨56019492897079056067123505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37346328598052704044749003 56019492897079056067123505)
        ·
          refine ⟨42014619672809292050342629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56019492897079056067123505 42014619672809292050342629)
          ·
            refine ⟨7877741188651742259439243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42014619672809292050342629 7877741188651742259439243)
            ·
              refine ⟨11816611782977613389158865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877741188651742259439243 11816611782977613389158865)
              ·
                refine ⟨8862458837233210041869149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11816611782977613389158865 8862458837233210041869149)
                ·
                  refine ⟨3323422063962453765700931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8862458837233210041869149 3323422063962453765700931)
                  ·
                    refine ⟨4985133095943680648551397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3323422063962453765700931 4985133095943680648551397)
                    ·
                      refine ⟨934712455489440121603387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4985133095943680648551397 934712455489440121603387)
                      ·
                        rfl

theorem cell23_1820346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_1820346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820346 prefixEnd_1820346 := by exact prefixLift 1820346
  have htrace : WordTrace (prefixWord ++ tailWord_1820346) baseStart_1820346 baseEnd_1820346 := by
    simpa [prefixWord, tailWord_1820346, baseEnd_1820346] using wordTrace_append hprefix tailTrace_1820346
  have hstable : (prefixWord ++ tailWord_1820346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820346).length < 2 ^ (prefixWord ++ tailWord_1820346).sum := by decide
  have hdescent : baseEnd_1820346 < baseStart_1820346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820376 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1820376 : Nat := 118140960795 + 1820376 * 2 ^ 59
def prefixEnd_1820376 : Nat := 4983230072969 + 3 ^ 40 * 1820376 * 2
def baseEnd_1820376 : Nat := 934727859909075004228249

theorem tailTrace_1820376 : CollatzResearch.WordTrace tailWord_1820376 prefixEnd_1820376 934727859909075004228249 := by
  unfold tailWord_1820376
  simp only [CollatzResearch.WordTrace]
  refine ⟨33197283626548061157128491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44263044835397414876171321 33197283626548061157128491)
  ·
    refine ⟨49795925439822091735692737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33197283626548061157128491 49795925439822091735692737)
    ·
      refine ⟨37346944079866568801769553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49795925439822091735692737 37346944079866568801769553)
      ·
        refine ⟨28010208059899926601327165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37346944079866568801769553 28010208059899926601327165)
        ·
          refine ⟨10503828022462472475497687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28010208059899926601327165 10503828022462472475497687)
          ·
            refine ⟨15755742033693708713246531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10503828022462472475497687 15755742033693708713246531)
            ·
              refine ⟨23633613050540563069869797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15755742033693708713246531 23633613050540563069869797)
              ·
                refine ⟨4431302446976355575600587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23633613050540563069869797 4431302446976355575600587)
                ·
                  refine ⟨6646953670464533363400881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431302446976355575600587 6646953670464533363400881)
                  ·
                    refine ⟨4985215252848400022550661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6646953670464533363400881 4985215252848400022550661)
                    ·
                      refine ⟨934727859909075004228249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4985215252848400022550661 934727859909075004228249)
                      ·
                        rfl

theorem cell23_1820376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1820376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820376 prefixEnd_1820376 := by exact prefixLift 1820376
  have htrace : WordTrace (prefixWord ++ tailWord_1820376) baseStart_1820376 baseEnd_1820376 := by
    simpa [prefixWord, tailWord_1820376, baseEnd_1820376] using wordTrace_append hprefix tailTrace_1820376
  have hstable : (prefixWord ++ tailWord_1820376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820376).length < 2 ^ (prefixWord ++ tailWord_1820376).sum := by decide
  have hdescent : baseEnd_1820376 < baseStart_1820376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820383 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 3]
def baseStart_1820383 : Nat := 118140960795 + 1820383 * 2 ^ 59
def prefixEnd_1820383 : Nat := 4983230072969 + 3 ^ 40 * 1820383 * 2
def baseEnd_1820383 : Nat := 934731454273656476840717

theorem tailTrace_1820383 : CollatzResearch.WordTrace tailWord_1820383 prefixEnd_1820383 934731454273656476840717 := by
  unfold tailWord_1820383
  simp only [CollatzResearch.WordTrace]
  refine ⟨66394822564070762509761803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44263215042713841673174535 66394822564070762509761803)
  ·
    refine ⟨99592233846106143764642705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66394822564070762509761803 99592233846106143764642705)
    ·
      refine ⟨74694175384579607823482029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99592233846106143764642705 74694175384579607823482029)
      ·
        refine ⟨28010315769217352933805761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74694175384579607823482029 28010315769217352933805761)
        ·
          refine ⟨21007736826913014700354321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28010315769217352933805761 21007736826913014700354321)
          ·
            refine ⟨15755802620184761025265741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21007736826913014700354321 15755802620184761025265741)
            ·
              refine ⟨5908425982569285384474653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15755802620184761025265741 5908425982569285384474653)
              ·
                refine ⟨2215659743463482019177995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5908425982569285384474653 2215659743463482019177995)
                ·
                  refine ⟨3323489615195223028766993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215659743463482019177995 3323489615195223028766993)
                  ·
                    refine ⟨2492617211396417271575245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3323489615195223028766993 2492617211396417271575245)
                    ·
                      refine ⟨934731454273656476840717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2492617211396417271575245 934731454273656476840717)
                      ·
                        rfl

theorem cell23_1820383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_1820383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820383 prefixEnd_1820383 := by exact prefixLift 1820383
  have htrace : WordTrace (prefixWord ++ tailWord_1820383) baseStart_1820383 baseEnd_1820383 := by
    simpa [prefixWord, tailWord_1820383, baseEnd_1820383] using wordTrace_append hprefix tailTrace_1820383
  have hstable : (prefixWord ++ tailWord_1820383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820383).length < 2 ^ (prefixWord ++ tailWord_1820383).sum := by decide
  have hdescent : baseEnd_1820383 < baseStart_1820383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820396 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_1820396 : Nat := 118140960795 + 1820396 * 2 ^ 59
def prefixEnd_1820396 : Nat := 4983230072969 + 3 ^ 40 * 1820396 * 2
def baseEnd_1820396 : Nat := 934738129522164925978157

theorem tailTrace_1820396 : CollatzResearch.WordTrace tailWord_1820396 prefixEnd_1820396 934738129522164925978157 := by
  unfold tailWord_1820396
  simp only [CollatzResearch.WordTrace]
  refine ⟨33197648356511832864992521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44263531142015777153323361 33197648356511832864992521)
  ·
    refine ⟨24898236267383874648744391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33197648356511832864992521 24898236267383874648744391)
    ·
      refine ⟨37347354401075811973116587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24898236267383874648744391 37347354401075811973116587)
      ·
        refine ⟨56021031601613717959674881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37347354401075811973116587 56021031601613717959674881)
        ·
          refine ⟨42015773701210288469756161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56021031601613717959674881 42015773701210288469756161)
          ·
            refine ⟨31511830275907716352317121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42015773701210288469756161 31511830275907716352317121)
            ·
              refine ⟨23633872706930787264237841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31511830275907716352317121 23633872706930787264237841)
              ·
                refine ⟨17725404530198090448178381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23633872706930787264237841 17725404530198090448178381)
                ·
                  refine ⟨6647026698824283918066893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17725404530198090448178381 6647026698824283918066893)
                  ·
                    refine ⟨2492635012059106469275085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6647026698824283918066893 2492635012059106469275085)
                    ·
                      refine ⟨934738129522164925978157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2492635012059106469275085 934738129522164925978157)
                      ·
                        rfl

theorem cell23_1820396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_1820396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820396 prefixEnd_1820396 := by exact prefixLift 1820396
  have htrace : WordTrace (prefixWord ++ tailWord_1820396) baseStart_1820396 baseEnd_1820396 := by
    simpa [prefixWord, tailWord_1820396, baseEnd_1820396] using wordTrace_append hprefix tailTrace_1820396
  have hstable : (prefixWord ++ tailWord_1820396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820396).length < 2 ^ (prefixWord ++ tailWord_1820396).sum := by decide
  have hdescent : baseEnd_1820396 < baseStart_1820396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820397 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_1820397 : Nat := 118140960795 + 1820397 * 2 ^ 59
def prefixEnd_1820397 : Nat := 4983230072969 + 3 ^ 40 * 1820397 * 2
def baseEnd_1820397 : Nat := 934738643002819422065653

theorem tailTrace_1820397 : CollatzResearch.WordTrace tailWord_1820397 prefixEnd_1820397 934738643002819422065653 := by
  unfold tailWord_1820397
  simp only [CollatzResearch.WordTrace]
  refine ⟨66395333186020042900771445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44263555457346695267180963 66395333186020042900771445)
  ·
    refine ⟨6224562486189379021947323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66395333186020042900771445 6224562486189379021947323)
    ·
      refine ⟨9336843729284068532920985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6224562486189379021947323 9336843729284068532920985)
      ·
        refine ⟨7002632796963051399690739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9336843729284068532920985 7002632796963051399690739)
        ·
          refine ⟨10503949195444577099536109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7002632796963051399690739 10503949195444577099536109)
          ·
            refine ⟨3938980948291716412326041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10503949195444577099536109 3938980948291716412326041)
            ·
              refine ⟨2954235711218787309244531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3938980948291716412326041 2954235711218787309244531)
              ·
                refine ⟨4431353566828180963866797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954235711218787309244531 4431353566828180963866797)
                ·
                  refine ⟨1661757587560567861450049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4431353566828180963866797 1661757587560567861450049)
                  ·
                    refine ⟨1246318190670425896087537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1661757587560567861450049 1246318190670425896087537)
                    ·
                      refine ⟨934738643002819422065653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246318190670425896087537 934738643002819422065653)
                      ·
                        rfl

theorem cell23_1820397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_1820397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820397 prefixEnd_1820397 := by exact prefixLift 1820397
  have htrace : WordTrace (prefixWord ++ tailWord_1820397) baseStart_1820397 baseEnd_1820397 := by
    simpa [prefixWord, tailWord_1820397, baseEnd_1820397] using wordTrace_append hprefix tailTrace_1820397
  have hstable : (prefixWord ++ tailWord_1820397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820397).length < 2 ^ (prefixWord ++ tailWord_1820397).sum := by decide
  have hdescent : baseEnd_1820397 < baseStart_1820397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820426 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1820426 : Nat := 118140960795 + 1820426 * 2 ^ 59
def prefixEnd_1820426 : Nat := 4983230072969 + 3 ^ 40 * 1820426 * 2
def baseEnd_1820426 : Nat := 934753533941799808603019

theorem tailTrace_1820426 : CollatzResearch.WordTrace tailWord_1820426 prefixEnd_1820426 934753533941799808603019 := by
  unfold tailWord_1820426
  simp only [CollatzResearch.WordTrace]
  refine ⟨16599097725728745213394283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44264260601943320569051421 16599097725728745213394283)
  ·
    refine ⟨24898646588593117820091425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16599097725728745213394283 24898646588593117820091425)
    ·
      refine ⟨18673984941444838365068569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24898646588593117820091425 18673984941444838365068569)
      ·
        refine ⟨14005488706083628773801427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18673984941444838365068569 14005488706083628773801427)
        ·
          refine ⟨21008233059125443160702141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005488706083628773801427 21008233059125443160702141)
          ·
            refine ⟨7878087397172041185263303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21008233059125443160702141 7878087397172041185263303)
            ·
              refine ⟨11817131095758061777894955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7878087397172041185263303 11817131095758061777894955)
              ·
                refine ⟨17725696643637092666842433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11817131095758061777894955 17725696643637092666842433)
                ·
                  refine ⟨13294272482727819500131825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17725696643637092666842433 13294272482727819500131825)
                  ·
                    refine ⟨9970704362045864625098869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13294272482727819500131825 9970704362045864625098869)
                    ·
                      refine ⟨934753533941799808603019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9970704362045864625098869 934753533941799808603019)
                      ·
                        rfl

theorem cell23_1820426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1820426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820426 prefixEnd_1820426 := by exact prefixLift 1820426
  have htrace : WordTrace (prefixWord ++ tailWord_1820426) baseStart_1820426 baseEnd_1820426 := by
    simpa [prefixWord, tailWord_1820426, baseEnd_1820426] using wordTrace_append hprefix tailTrace_1820426
  have hstable : (prefixWord ++ tailWord_1820426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820426).length < 2 ^ (prefixWord ++ tailWord_1820426).sum := by decide
  have hdescent : baseEnd_1820426 < baseStart_1820426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820440 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 1, 3, 2]
def baseStart_1820440 : Nat := 118140960795 + 1820440 * 2 ^ 59
def prefixEnd_1820440 : Nat := 4983230072969 + 3 ^ 40 * 1820440 * 2
def baseEnd_1820440 : Nat := 934760722670962753827955

theorem tailTrace_1820440 : CollatzResearch.WordTrace tailWord_1820440 prefixEnd_1820440 934760722670962753827955 := by
  unfold tailWord_1820440
  simp only [CollatzResearch.WordTrace]
  refine ⟨33198450762432130622293387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44264601016576174163057849 33198450762432130622293387)
  ·
    refine ⟨49797676143648195933440081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33198450762432130622293387 49797676143648195933440081)
    ·
      refine ⟨37348257107736146950080061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49797676143648195933440081 37348257107736146950080061)
      ·
        refine ⟨14005596415401055106280023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37348257107736146950080061 14005596415401055106280023)
        ·
          refine ⟨21008394623101582659420035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005596415401055106280023 21008394623101582659420035)
          ·
            refine ⟨31512591934652373989130053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21008394623101582659420035 31512591934652373989130053)
            ·
              refine ⟨5908610987747320122961885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31512591934652373989130053 5908610987747320122961885)
              ·
                refine ⟨2215729120405245046110707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5908610987747320122961885 2215729120405245046110707)
                ·
                  refine ⟨3323593680607867569166061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215729120405245046110707 3323593680607867569166061)
                  ·
                    refine ⟨1246347630227950338437273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323593680607867569166061 1246347630227950338437273)
                    ·
                      refine ⟨934760722670962753827955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246347630227950338437273 934760722670962753827955)
                      ·
                        rfl

theorem cell23_1820440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_1820440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820440 prefixEnd_1820440 := by exact prefixLift 1820440
  have htrace : WordTrace (prefixWord ++ tailWord_1820440) baseStart_1820440 baseEnd_1820440 := by
    simpa [prefixWord, tailWord_1820440, baseEnd_1820440] using wordTrace_append hprefix tailTrace_1820440
  have hstable : (prefixWord ++ tailWord_1820440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820440).length < 2 ^ (prefixWord ++ tailWord_1820440).sum := by decide
  have hdescent : baseEnd_1820440 < baseStart_1820440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820476 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 7]
def baseStart_1820476 : Nat := 118140960795 + 1820476 * 2 ^ 59
def prefixEnd_1820476 : Nat := 4983230072969 + 3 ^ 40 * 1820476 * 2
def baseEnd_1820476 : Nat := 103864356441613845886421

theorem tailTrace_1820476 : CollatzResearch.WordTrace tailWord_1820476 prefixEnd_1820476 103864356441613845886421 := by
  unfold tailWord_1820476
  simp only [CollatzResearch.WordTrace]
  refine ⟨33199107276366919696448641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44265476368489226261931521 33199107276366919696448641)
  ·
    refine ⟨24899330457275189772336481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33199107276366919696448641 24899330457275189772336481)
    ·
      refine ⟨18674497842956392329252361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24899330457275189772336481 18674497842956392329252361)
      ·
        refine ⟨14005873382217294246939271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18674497842956392329252361 14005873382217294246939271)
        ·
          refine ⟨21008810073325941370408907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005873382217294246939271 21008810073325941370408907)
          ·
            refine ⟨31513215109988912055613361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21008810073325941370408907 31513215109988912055613361)
            ·
              refine ⟨23634911332491684041710021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31513215109988912055613361 23634911332491684041710021)
              ·
                refine ⟨4431545874842190757820629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23634911332491684041710021 4431545874842190757820629)
                ·
                  refine ⟨103864356441613845886421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4431545874842190757820629 103864356441613845886421)
                  ·
                    rfl

theorem cell23_1820476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_1820476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820476 prefixEnd_1820476 := by exact prefixLift 1820476
  have htrace : WordTrace (prefixWord ++ tailWord_1820476) baseStart_1820476 baseEnd_1820476 := by
    simpa [prefixWord, tailWord_1820476, baseEnd_1820476] using wordTrace_append hprefix tailTrace_1820476
  have hstable : (prefixWord ++ tailWord_1820476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820476).length < 2 ^ (prefixWord ++ tailWord_1820476).sum := by decide
  have hdescent : baseEnd_1820476 < baseStart_1820476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820513 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_1820513 : Nat := 118140960795 + 1820513 * 2 ^ 59
def prefixEnd_1820513 : Nat := 4983230072969 + 3 ^ 40 * 1820513 * 2
def baseEnd_1820513 : Nat := 934798206758740968215119

theorem tailTrace_1820513 : CollatzResearch.WordTrace tailWord_1820513 prefixEnd_1820513 934798206758740968215119 := by
  unfold tailWord_1820513
  simp only [CollatzResearch.WordTrace]
  refine ⟨66399564053599794711994193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44266376035733196474662795 66399564053599794711994193)
  ·
    refine ⟨49799673040199846033995645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66399564053599794711994193 49799673040199846033995645)
    ·
      refine ⟨18674877390074942262748367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49799673040199846033995645 18674877390074942262748367)
      ·
        refine ⟨28012316085112413394122551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18674877390074942262748367 28012316085112413394122551)
        ·
          refine ⟨42018474127668620091183827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28012316085112413394122551 42018474127668620091183827)
          ·
            refine ⟨63027711191502930136775741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42018474127668620091183827 63027711191502930136775741)
            ·
              refine ⟨23635391696813598801290903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63027711191502930136775741 23635391696813598801290903)
              ·
                refine ⟨35453087545220398201936355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23635391696813598801290903 35453087545220398201936355)
                ·
                  refine ⟨53179631317830597302904533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35453087545220398201936355 53179631317830597302904533)
                  ·
                    refine ⟨1246397609011654624286825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53179631317830597302904533 1246397609011654624286825)
                    ·
                      refine ⟨934798206758740968215119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246397609011654624286825 934798206758740968215119)
                      ·
                        rfl

theorem cell23_1820513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_1820513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820513 prefixEnd_1820513 := by exact prefixLift 1820513
  have htrace : WordTrace (prefixWord ++ tailWord_1820513) baseStart_1820513 baseEnd_1820513 := by
    simpa [prefixWord, tailWord_1820513, baseEnd_1820513] using wordTrace_append hprefix tailTrace_1820513
  have hstable : (prefixWord ++ tailWord_1820513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820513).length < 2 ^ (prefixWord ++ tailWord_1820513).sum := by decide
  have hdescent : baseEnd_1820513 < baseStart_1820513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820543 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 3, 6, 2]
def baseStart_1820543 : Nat := 118140960795 + 1820543 * 2 ^ 59
def prefixEnd_1820543 : Nat := 4983230072969 + 3 ^ 40 * 1820543 * 2
def baseEnd_1820543 : Nat := 934813611178375850839981

theorem tailTrace_1820543 : CollatzResearch.WordTrace tailWord_1820543 prefixEnd_1820543 934813611178375850839981 := by
  unfold tailWord_1820543
  simp only [CollatzResearch.WordTrace]
  refine ⟨66400658243491109835586283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44267105495660739890390855 66400658243491109835586283)
  ·
    refine ⟨99600987365236664753379425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66400658243491109835586283 99600987365236664753379425)
    ·
      refine ⟨74700740523927498565034569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99600987365236664753379425 74700740523927498565034569)
      ·
        refine ⟨56025555392945623923775927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74700740523927498565034569 56025555392945623923775927)
        ·
          refine ⟨84038333089418435885663891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56025555392945623923775927 84038333089418435885663891)
          ·
            refine ⟨126057499634127653828495837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84038333089418435885663891 126057499634127653828495837)
            ·
              refine ⟨47271562362797870185685939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126057499634127653828495837 47271562362797870185685939)
              ·
                refine ⟨70907343544196805278528909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47271562362797870185685939 70907343544196805278528909)
                ·
                  refine ⟨26590253829073801979448341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70907343544196805278528909 26590253829073801979448341)
                  ·
                    refine ⟨1246418148237834467786641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26590253829073801979448341 1246418148237834467786641)
                    ·
                      refine ⟨934813611178375850839981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246418148237834467786641 934813611178375850839981)
                      ·
                        rfl

theorem cell23_1820543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_1820543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820543 prefixEnd_1820543 := by exact prefixLift 1820543
  have htrace : WordTrace (prefixWord ++ tailWord_1820543) baseStart_1820543 baseEnd_1820543 := by
    simpa [prefixWord, tailWord_1820543, baseEnd_1820543] using wordTrace_append hprefix tailTrace_1820543
  have hstable : (prefixWord ++ tailWord_1820543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820543).length < 2 ^ (prefixWord ++ tailWord_1820543).sum := by decide
  have hdescent : baseEnd_1820543 < baseStart_1820543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820553 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 5, 4]
def baseStart_1820553 : Nat := 118140960795 + 1820553 * 2 ^ 59
def prefixEnd_1820553 : Nat := 4983230072969 + 3 ^ 40 * 1820553 * 2
def baseEnd_1820553 : Nat := 311606248661640270571645

theorem tailTrace_1820553 : CollatzResearch.WordTrace tailWord_1820553 prefixEnd_1820553 311606248661640270571645 := by
  unfold tailWord_1820553
  simp only [CollatzResearch.WordTrace]
  refine ⟨66401022973454881543450313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44267348648969921028966875 66401022973454881543450313)
  ·
    refine ⟨49800767230091161157587735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66401022973454881543450313 49800767230091161157587735)
    ·
      refine ⟨74701150845136741736381603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49800767230091161157587735 74701150845136741736381603)
      ·
        refine ⟨112051726267705112604572405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74701150845136741736381603 112051726267705112604572405)
        ·
          refine ⟨10504849337597354306678663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112051726267705112604572405 10504849337597354306678663)
          ·
            refine ⟨15757274006396031460017995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10504849337597354306678663 15757274006396031460017995)
            ·
              refine ⟨23635911009594047190026993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15757274006396031460017995 23635911009594047190026993)
              ·
                refine ⟨17726933257195535392520245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23635911009594047190026993 17726933257195535392520245)
                ·
                  refine ⟨1661899992862081443048773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17726933257195535392520245 1661899992862081443048773)
                  ·
                    refine ⟨311606248661640270571645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1661899992862081443048773 311606248661640270571645)
                    ·
                      rfl

theorem cell23_1820553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 4].length) (baseStart_1820553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820553 prefixEnd_1820553 := by exact prefixLift 1820553
  have htrace : WordTrace (prefixWord ++ tailWord_1820553) baseStart_1820553 baseEnd_1820553 := by
    simpa [prefixWord, tailWord_1820553, baseEnd_1820553] using wordTrace_append hprefix tailTrace_1820553
  have hstable : (prefixWord ++ tailWord_1820553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820553).length < 2 ^ (prefixWord ++ tailWord_1820553).sum := by decide
  have hdescent : baseEnd_1820553 < baseStart_1820553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820570 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_1820570 : Nat := 118140960795 + 1820570 * 2 ^ 59
def prefixEnd_1820570 : Nat := 4983230072969 + 3 ^ 40 * 1820570 * 2
def baseEnd_1820570 : Nat := 311609158385349081734119

theorem tailTrace_1820570 : CollatzResearch.WordTrace tailWord_1820570 prefixEnd_1820570 311609158385349081734119 := by
  unfold tailWord_1820570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16600410753598323361704791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44267762009595528964546109 16600410753598323361704791)
  ·
    refine ⟨24900616130397485042557187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16600410753598323361704791 24900616130397485042557187)
    ·
      refine ⟨37350924195596227563835781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24900616130397485042557187 37350924195596227563835781)
      ·
        refine ⟨7003298286674292668219209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37350924195596227563835781 7003298286674292668219209)
        ·
          refine ⟨5252473715005719501164407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7003298286674292668219209 5252473715005719501164407)
          ·
            refine ⟨7878710572508579251746611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5252473715005719501164407 7878710572508579251746611)
            ·
              refine ⟨11818065858762868877619917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7878710572508579251746611 11818065858762868877619917)
              ·
                refine ⟨4431774697036075829107469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11818065858762868877619917 4431774697036075829107469)
                ·
                  refine ⟨1661915511388528435915301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4431774697036075829107469 1661915511388528435915301)
                  ·
                    refine ⟨311609158385349081734119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1661915511388528435915301 311609158385349081734119)
                    ·
                      rfl

theorem cell23_1820570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_1820570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820570 prefixEnd_1820570 := by exact prefixLift 1820570
  have htrace : WordTrace (prefixWord ++ tailWord_1820570) baseStart_1820570 baseEnd_1820570 := by
    simpa [prefixWord, tailWord_1820570, baseEnd_1820570] using wordTrace_append hprefix tailTrace_1820570
  have hstable : (prefixWord ++ tailWord_1820570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820570).length < 2 ^ (prefixWord ++ tailWord_1820570).sum := by decide
  have hdescent : baseEnd_1820570 < baseStart_1820570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820634 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 6]
def baseStart_1820634 : Nat := 118140960795 + 1820634 * 2 ^ 59
def prefixEnd_1820634 : Nat := 4983230072969 + 3 ^ 40 * 1820634 * 2
def baseEnd_1820634 : Nat := 103873370879770554978007

theorem tailTrace_1820634 : CollatzResearch.WordTrace tailWord_1820634 prefixEnd_1820634 103873370879770554978007 := by
  unfold tailWord_1820634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16600994321540358094287239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44269318190774288251432637 16600994321540358094287239)
  ·
    refine ⟨24901491482310537141430859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16600994321540358094287239 24901491482310537141430859)
    ·
      refine ⟨37352237223465805712146289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24901491482310537141430859 37352237223465805712146289)
      ·
        refine ⟨28014177917599354284109717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37352237223465805712146289 28014177917599354284109717)
        ·
          refine ⟨1313164589887469732067643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28014177917599354284109717 1313164589887469732067643)
          ·
            refine ⟨1969746884831204598101465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313164589887469732067643 1969746884831204598101465)
            ·
              refine ⟨1477310163623403448576099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1969746884831204598101465 1477310163623403448576099)
              ·
                refine ⟨2215965245435105172864149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477310163623403448576099 2215965245435105172864149)
                ·
                  refine ⟨103873370879770554978007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2215965245435105172864149 103873370879770554978007)
                  ·
                    rfl

theorem cell23_1820634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_1820634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820634 prefixEnd_1820634 := by exact prefixLift 1820634
  have htrace : WordTrace (prefixWord ++ tailWord_1820634) baseStart_1820634 baseEnd_1820634 := by
    simpa [prefixWord, tailWord_1820634, baseEnd_1820634] using wordTrace_append hprefix tailTrace_1820634
  have hstable : (prefixWord ++ tailWord_1820634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820634).length < 2 ^ (prefixWord ++ tailWord_1820634).sum := by decide
  have hdescent : baseEnd_1820634 < baseStart_1820634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820650 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1820650 : Nat := 118140960795 + 1820650 * 2 ^ 59
def prefixEnd_1820650 : Nat := 4983230072969 + 3 ^ 40 * 1820650 * 2
def baseEnd_1820650 : Nat := 934868553608406932201989

theorem tailTrace_1820650 : CollatzResearch.WordTrace tailWord_1820650 prefixEnd_1820650 934868553608406932201989 := by
  unfold tailWord_1820650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16601140213525866777432851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44269707236068978073154269 16601140213525866777432851)
  ·
    refine ⟨24901710320288800166149277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16601140213525866777432851 24901710320288800166149277)
    ·
      refine ⟨9338141370108300062305979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24901710320288800166149277 9338141370108300062305979)
      ·
        refine ⟨14007212055162450093458969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9338141370108300062305979 14007212055162450093458969)
        ·
          refine ⟨10505409041371837570094227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14007212055162450093458969 10505409041371837570094227)
          ·
            refine ⟨15758113562057756355141341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10505409041371837570094227 15758113562057756355141341)
            ·
              refine ⟨5909292585771658633178003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15758113562057756355141341 5909292585771658633178003)
              ·
                refine ⟨8863938878657487949767005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909292585771658633178003 8863938878657487949767005)
                ·
                  refine ⟨3323977079496557981162627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8863938878657487949767005 3323977079496557981162627)
                  ·
                    refine ⟨4985965619244836971743941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3323977079496557981162627 4985965619244836971743941)
                    ·
                      refine ⟨934868553608406932201989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4985965619244836971743941 934868553608406932201989)
                      ·
                        rfl

theorem cell23_1820650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1820650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820650 prefixEnd_1820650 := by exact prefixLift 1820650
  have htrace : WordTrace (prefixWord ++ tailWord_1820650) baseStart_1820650 baseEnd_1820650 := by
    simpa [prefixWord, tailWord_1820650, baseEnd_1820650] using wordTrace_append hprefix tailTrace_1820650
  have hstable : (prefixWord ++ tailWord_1820650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820650).length < 2 ^ (prefixWord ++ tailWord_1820650).sum := by decide
  have hdescent : baseEnd_1820650 < baseStart_1820650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820654 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_1820654 : Nat := 118140960795 + 1820654 * 2 ^ 59
def prefixEnd_1820654 : Nat := 4983230072969 + 3 ^ 40 * 1820654 * 2
def baseEnd_1820654 : Nat := 934870607531024916551971

theorem tailTrace_1820654 : CollatzResearch.WordTrace tailWord_1820654 prefixEnd_1820654 934870607531024916551971 := by
  unfold tailWord_1820654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300588343261121974109627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44269804497392650528584677 8300588343261121974109627)
  ·
    refine ⟨12450882514891682961164441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8300588343261121974109627 12450882514891682961164441)
    ·
      refine ⟨9338161886168762220873331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12450882514891682961164441 9338161886168762220873331)
      ·
        refine ⟨14007242829253143331309997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9338161886168762220873331 14007242829253143331309997)
        ·
          refine ⟨5252716060969928749241249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14007242829253143331309997 5252716060969928749241249)
          ·
            refine ⟨3939537045727446561930937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5252716060969928749241249 3939537045727446561930937)
            ·
              refine ⟨2954652784295584921448203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3939537045727446561930937 2954652784295584921448203)
              ·
                refine ⟨4431979176443377382172305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954652784295584921448203 4431979176443377382172305)
                ·
                  refine ⟨3323984382332533036629229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4431979176443377382172305 3323984382332533036629229)
                  ·
                    refine ⟨1246494143374699888735961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323984382332533036629229 1246494143374699888735961)
                    ·
                      refine ⟨934870607531024916551971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246494143374699888735961 934870607531024916551971)
                      ·
                        rfl

theorem cell23_1820654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_1820654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820654 prefixEnd_1820654 := by exact prefixLift 1820654
  have htrace : WordTrace (prefixWord ++ tailWord_1820654) baseStart_1820654 baseEnd_1820654 := by
    simpa [prefixWord, tailWord_1820654, baseEnd_1820654] using wordTrace_append hprefix tailTrace_1820654
  have hstable : (prefixWord ++ tailWord_1820654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820654).length < 2 ^ (prefixWord ++ tailWord_1820654).sum := by decide
  have hdescent : baseEnd_1820654 < baseStart_1820654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820677 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_1820677 : Nat := 118140960795 + 1820677 * 2 ^ 59
def prefixEnd_1820677 : Nat := 4983230072969 + 3 ^ 40 * 1820677 * 2
def baseEnd_1820677 : Nat := 311627472528692775521455

theorem tailTrace_1820677 : CollatzResearch.WordTrace tailWord_1820677 prefixEnd_1820677 311627472528692775521455 := by
  unfold tailWord_1820677
  simp only [CollatzResearch.WordTrace]
  refine ⟨66405545625005650720964285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44270363750003767147309523 66405545625005650720964285)
  ·
    refine ⟨24902079609377119020361607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66405545625005650720964285 24902079609377119020361607)
    ·
      refine ⟨37353119414065678530542411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24902079609377119020361607 37353119414065678530542411)
      ·
        refine ⟨56029679121098517795813617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37353119414065678530542411 56029679121098517795813617)
        ·
          refine ⟨42022259340823888346860213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56029679121098517795813617 42022259340823888346860213)
          ·
            refine ⟨3939586813202239532518145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42022259340823888346860213 3939586813202239532518145)
            ·
              refine ⟨2954690109901679649388609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3939586813202239532518145 2954690109901679649388609)
              ·
                refine ⟨2216017582426259737041457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954690109901679649388609 2216017582426259737041457)
                ·
                  refine ⟨1662013186819694802781093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2216017582426259737041457 1662013186819694802781093)
                  ·
                    refine ⟨311627472528692775521455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1662013186819694802781093 311627472528692775521455)
                    ·
                      rfl

theorem cell23_1820677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_1820677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820677 prefixEnd_1820677 := by exact prefixLift 1820677
  have htrace : WordTrace (prefixWord ++ tailWord_1820677) baseStart_1820677 baseEnd_1820677 := by
    simpa [prefixWord, tailWord_1820677, baseEnd_1820677] using wordTrace_append hprefix tailTrace_1820677
  have hstable : (prefixWord ++ tailWord_1820677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820677).length < 2 ^ (prefixWord ++ tailWord_1820677).sum := by decide
  have hdescent : baseEnd_1820677 < baseStart_1820677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820703 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 2, 7]
def baseStart_1820703 : Nat := 118140960795 + 1820703 * 2 ^ 59
def prefixEnd_1820703 : Nat := 4983230072969 + 3 ^ 40 * 1820703 * 2
def baseEnd_1820703 : Nat := 311631922694365074946415

theorem tailTrace_1820703 : CollatzResearch.WordTrace tailWord_1820703 prefixEnd_1820703 311631922694365074946415 := by
  unfold tailWord_1820703
  simp only [CollatzResearch.WordTrace]
  refine ⟨66406493922911457161410763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44270995948607638107607175 66406493922911457161410763)
  ·
    refine ⟨99609740884367185742116145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66406493922911457161410763 99609740884367185742116145)
    ·
      refine ⟨74707305663275389306587109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99609740884367185742116145 74707305663275389306587109)
      ·
        refine ⟨14007619811864135494985083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74707305663275389306587109 14007619811864135494985083)
        ·
          refine ⟨21011429717796203242477625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14007619811864135494985083 21011429717796203242477625)
          ·
            refine ⟨15758572288347152431858219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21011429717796203242477625 15758572288347152431858219)
            ·
              refine ⟨23637858432520728647787329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15758572288347152431858219 23637858432520728647787329)
              ·
                refine ⟨17728393824390546485840497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23637858432520728647787329 17728393824390546485840497)
                ·
                  refine ⟨13296295368292909864380373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17728393824390546485840497 13296295368292909864380373)
                  ·
                    refine ⟨311631922694365074946415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13296295368292909864380373 311631922694365074946415)
                    ·
                      rfl

theorem cell23_1820703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_1820703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820703 prefixEnd_1820703 := by exact prefixLift 1820703
  have htrace : WordTrace (prefixWord ++ tailWord_1820703) baseStart_1820703 baseEnd_1820703 := by
    simpa [prefixWord, tailWord_1820703, baseEnd_1820703] using wordTrace_append hprefix tailTrace_1820703
  have hstable : (prefixWord ++ tailWord_1820703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820703).length < 2 ^ (prefixWord ++ tailWord_1820703).sum := by decide
  have hdescent : baseEnd_1820703 < baseStart_1820703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820718 : List Nat := [4, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_1820718 : Nat := 118140960795 + 1820718 * 2 ^ 59
def prefixEnd_1820718 : Nat := 4983230072969 + 3 ^ 40 * 1820718 * 2
def baseEnd_1820718 : Nat := 934903470292912666151677

theorem tailTrace_1820718 : CollatzResearch.WordTrace tailWord_1820718 prefixEnd_1820718 934903470292912666151677 := by
  unfold tailWord_1820718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300880127232139340400851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44271360678571409815471205 8300880127232139340400851)
  ·
    refine ⟨12451320190848209010601277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8300880127232139340400851 12451320190848209010601277)
    ·
      refine ⟨4669245071568078378975479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12451320190848209010601277 4669245071568078378975479)
      ·
        refine ⟨7003867607352117568463219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4669245071568078378975479 7003867607352117568463219)
        ·
          refine ⟨10505801411028176352694829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7003867607352117568463219 10505801411028176352694829)
          ·
            refine ⟨3939675529135566132260561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10505801411028176352694829 3939675529135566132260561)
            ·
              refine ⟨2954756646851674599195421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3939675529135566132260561 2954756646851674599195421)
              ·
                refine ⟨1108033742569377974698283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2954756646851674599195421 1108033742569377974698283)
                ·
                  refine ⟨1662050613854066962047425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108033742569377974698283 1662050613854066962047425)
                  ·
                    refine ⟨1246537960390550221535569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662050613854066962047425 1246537960390550221535569)
                    ·
                      refine ⟨934903470292912666151677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246537960390550221535569 934903470292912666151677)
                      ·
                        rfl

theorem cell23_1820718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_1820718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820718 prefixEnd_1820718 := by exact prefixLift 1820718
  have htrace : WordTrace (prefixWord ++ tailWord_1820718) baseStart_1820718 baseEnd_1820718 := by
    simpa [prefixWord, tailWord_1820718, baseEnd_1820718] using wordTrace_append hprefix tailTrace_1820718
  have hstable : (prefixWord ++ tailWord_1820718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820718).length < 2 ^ (prefixWord ++ tailWord_1820718).sum := by decide
  have hdescent : baseEnd_1820718 < baseStart_1820718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820750 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_1820750 : Nat := 118140960795 + 1820750 * 2 ^ 59
def prefixEnd_1820750 : Nat := 4983230072969 + 3 ^ 40 * 1820750 * 2
def baseEnd_1820750 : Nat := 311639967224618846983843

theorem tailTrace_1820750 : CollatzResearch.WordTrace tailWord_1820750 prefixEnd_1820750 311639967224618846983843 := by
  unfold tailWord_1820750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301026019217648023546463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44272138769160789458914469 8301026019217648023546463)
  ·
    refine ⟨12451539028826472035319695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8301026019217648023546463 12451539028826472035319695)
    ·
      refine ⟨18677308543239708052979543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12451539028826472035319695 18677308543239708052979543)
      ·
        refine ⟨28015962814859562079469315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18677308543239708052979543 28015962814859562079469315)
        ·
          refine ⟨42023944222289343119203973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28015962814859562079469315 42023944222289343119203973)
          ·
            refine ⟨7879489541679251834850745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42023944222289343119203973 7879489541679251834850745)
            ·
              refine ⟨5909617156259438876138059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7879489541679251834850745 5909617156259438876138059)
              ·
                refine ⟨8864425734389158314207089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909617156259438876138059 8864425734389158314207089)
                ·
                  refine ⟨6648319300791868735655317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8864425734389158314207089 6648319300791868735655317)
                  ·
                    refine ⟨311639967224618846983843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6648319300791868735655317 311639967224618846983843)
                    ·
                      rfl

theorem cell23_1820750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_1820750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820750 prefixEnd_1820750 := by exact prefixLift 1820750
  have htrace : WordTrace (prefixWord ++ tailWord_1820750) baseStart_1820750 baseEnd_1820750 := by
    simpa [prefixWord, tailWord_1820750, baseEnd_1820750] using wordTrace_append hprefix tailTrace_1820750
  have hstable : (prefixWord ++ tailWord_1820750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820750).length < 2 ^ (prefixWord ++ tailWord_1820750).sum := by decide
  have hdescent : baseEnd_1820750 < baseStart_1820750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820797 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 7]
def baseStart_1820797 : Nat := 118140960795 + 1820797 * 2 ^ 59
def prefixEnd_1820797 : Nat := 4983230072969 + 3 ^ 40 * 1820797 * 2
def baseEnd_1820797 : Nat := 103882670584957539673757

theorem tailTrace_1820797 : CollatzResearch.WordTrace tailWord_1820797 prefixEnd_1820797 103882670584957539673757 := by
  unfold tailWord_1820797
  simp only [CollatzResearch.WordTrace]
  refine ⟨66409922384570911215332645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44273281589713940810221763 66409922384570911215332645)
  ·
    refine ⟨12451860447107045852874871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66409922384570911215332645 12451860447107045852874871)
    ·
      refine ⟨18677790670660568779312307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12451860447107045852874871 18677790670660568779312307)
      ·
        refine ⟨28016686005990853168968461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18677790670660568779312307 28016686005990853168968461)
        ·
          refine ⟨10506257252246569938363173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28016686005990853168968461 10506257252246569938363173)
          ·
            refine ⟨1969923234796231863443095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10506257252246569938363173 1969923234796231863443095)
            ·
              refine ⟨2954884852194347795164643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969923234796231863443095 2954884852194347795164643)
              ·
                refine ⟨4432327278291521692746965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954884852194347795164643 4432327278291521692746965)
                ·
                  refine ⟨103882670584957539673757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4432327278291521692746965 103882670584957539673757)
                  ·
                    rfl

theorem cell23_1820797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_1820797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820797 prefixEnd_1820797 := by exact prefixLift 1820797
  have htrace : WordTrace (prefixWord ++ tailWord_1820797) baseStart_1820797 baseEnd_1820797 := by
    simpa [prefixWord, tailWord_1820797, baseEnd_1820797] using wordTrace_append hprefix tailTrace_1820797
  have hstable : (prefixWord ++ tailWord_1820797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820797).length < 2 ^ (prefixWord ++ tailWord_1820797).sum := by decide
  have hdescent : baseEnd_1820797 < baseStart_1820797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820808 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1820808 : Nat := 118140960795 + 1820808 * 2 ^ 59
def prefixEnd_1820808 : Nat := 4983230072969 + 3 ^ 40 * 1820808 * 2
def baseEnd_1820808 : Nat := 934949683551817314026263

theorem tailTrace_1820808 : CollatzResearch.WordTrace tailWord_1820808 prefixEnd_1820808 934949683551817314026263 := by
  unfold tailWord_1820808
  simp only [CollatzResearch.WordTrace]
  refine ⟨33205161793765530046991539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44273549058354040062655385 33205161793765530046991539)
  ·
    refine ⟨49807742690648295070487309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33205161793765530046991539 49807742690648295070487309)
    ·
      refine ⟨18677903508993110651432741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49807742690648295070487309 18677903508993110651432741)
      ·
        refine ⟨3502106907936208247143639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18677903508993110651432741 3502106907936208247143639)
        ·
          refine ⟨5253160361904312370715459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502106907936208247143639 5253160361904312370715459)
          ·
            refine ⟨7879740542856468556073189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253160361904312370715459 7879740542856468556073189)
            ·
              refine ⟨1477451351785587854263723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7879740542856468556073189 1477451351785587854263723)
              ·
                refine ⟨2216177027678381781395585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477451351785587854263723 2216177027678381781395585)
                ·
                  refine ⟨1662132770758786336046689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2216177027678381781395585 1662132770758786336046689)
                  ·
                    refine ⟨1246599578069089752035017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662132770758786336046689 1246599578069089752035017)
                    ·
                      refine ⟨934949683551817314026263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246599578069089752035017 934949683551817314026263)
                      ·
                        rfl

theorem cell23_1820808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1820808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820808 prefixEnd_1820808 := by exact prefixLift 1820808
  have htrace : WordTrace (prefixWord ++ tailWord_1820808) baseStart_1820808 baseEnd_1820808 := by
    simpa [prefixWord, tailWord_1820808, baseEnd_1820808] using wordTrace_append hprefix tailTrace_1820808
  have hstable : (prefixWord ++ tailWord_1820808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820808).length < 2 ^ (prefixWord ++ tailWord_1820808).sum := by decide
  have hdescent : baseEnd_1820808 < baseStart_1820808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820847 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 2, 4, 2]
def baseStart_1820847 : Nat := 118140960795 + 1820847 * 2 ^ 59
def prefixEnd_1820847 : Nat := 4983230072969 + 3 ^ 40 * 1820847 * 2
def baseEnd_1820847 : Nat := 934969709297342661438583

theorem tailTrace_1820847 : CollatzResearch.WordTrace tailWord_1820847 prefixEnd_1820847 934969709297342661438583 := by
  unfold tailWord_1820847
  simp only [CollatzResearch.WordTrace]
  refine ⟨66411746034389769754652795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44274497356259846503101863 66411746034389769754652795)
  ·
    refine ⟨99617619051584654631979193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66411746034389769754652795 99617619051584654631979193)
    ·
      refine ⟨74713214288688490973984395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99617619051584654631979193 74713214288688490973984395)
      ·
        refine ⟨112069821433032736460976593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74713214288688490973984395 112069821433032736460976593)
        ·
          refine ⟨84052366074774552345732445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112069821433032736460976593 84052366074774552345732445)
          ·
            refine ⟨31519637278040457129649667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84052366074774552345732445 31519637278040457129649667)
            ·
              refine ⟨47279455917060685694474501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31519637278040457129649667 47279455917060685694474501)
              ·
                refine ⟨8864897984448878567713969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47279455917060685694474501 8864897984448878567713969)
                ·
                  refine ⟨6648673488336658925785477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8864897984448878567713969 6648673488336658925785477)
                  ·
                    refine ⟨1246626279063123548584777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6648673488336658925785477 1246626279063123548584777)
                    ·
                      refine ⟨934969709297342661438583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246626279063123548584777 934969709297342661438583)
                      ·
                        rfl

theorem cell23_1820847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 4, 2].length) (baseStart_1820847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820847 prefixEnd_1820847 := by exact prefixLift 1820847
  have htrace : WordTrace (prefixWord ++ tailWord_1820847) baseStart_1820847 baseEnd_1820847 := by
    simpa [prefixWord, tailWord_1820847, baseEnd_1820847] using wordTrace_append hprefix tailTrace_1820847
  have hstable : (prefixWord ++ tailWord_1820847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820847).length < 2 ^ (prefixWord ++ tailWord_1820847).sum := by decide
  have hdescent : baseEnd_1820847 < baseStart_1820847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820850 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1820850 : Nat := 118140960795 + 1820850 * 2 ^ 59
def prefixEnd_1820850 : Nat := 4983230072969 + 3 ^ 40 * 1820850 * 2
def baseEnd_1820850 : Nat := 934971249739306149701069

theorem tailTrace_1820850 : CollatzResearch.WordTrace tailWord_1820850 prefixEnd_1820850 934971249739306149701069 := by
  unfold tailWord_1820850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16602963863344725316753001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44274570302252600844674669 16602963863344725316753001)
  ·
    refine ⟨12452222897508543987564751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16602963863344725316753001 12452222897508543987564751)
    ·
      refine ⟨18678334346262815981347127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12452222897508543987564751 18678334346262815981347127)
      ·
        refine ⟨28017501519394223972020691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18678334346262815981347127 28017501519394223972020691)
        ·
          refine ⟨42026252279091335958031037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28017501519394223972020691 42026252279091335958031037)
          ·
            refine ⟨15759844604659250984261639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42026252279091335958031037 15759844604659250984261639)
            ·
              refine ⟨23639766906988876476392459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15759844604659250984261639 23639766906988876476392459)
              ·
                refine ⟨35459650360483314714588689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23639766906988876476392459 35459650360483314714588689)
                ·
                  refine ⟨26594737770362486035941517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35459650360483314714588689 26594737770362486035941517)
                  ·
                    refine ⟨9973026663885932263478069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26594737770362486035941517 9973026663885932263478069)
                    ·
                      refine ⟨934971249739306149701069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9973026663885932263478069 934971249739306149701069)
                      ·
                        rfl

theorem cell23_1820850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1820850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820850 prefixEnd_1820850 := by exact prefixLift 1820850
  have htrace : WordTrace (prefixWord ++ tailWord_1820850) baseStart_1820850 baseEnd_1820850 := by
    simpa [prefixWord, tailWord_1820850, baseEnd_1820850] using wordTrace_append hprefix tailTrace_1820850
  have hstable : (prefixWord ++ tailWord_1820850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820850).length < 2 ^ (prefixWord ++ tailWord_1820850).sum := by decide
  have hdescent : baseEnd_1820850 < baseStart_1820850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820857 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 3, 4]
def baseStart_1820857 : Nat := 118140960795 + 1820857 * 2 ^ 59
def prefixEnd_1820857 : Nat := 4983230072969 + 3 ^ 40 * 1820857 * 2
def baseEnd_1820857 : Nat := 311658281367962540771179

theorem tailTrace_1820857 : CollatzResearch.WordTrace tailWord_1820857 prefixEnd_1820857 311658281367962540771179 := by
  unfold tailWord_1820857
  simp only [CollatzResearch.WordTrace]
  refine ⟨66412110764353541462516825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44274740509569027641677883 66412110764353541462516825)
  ·
    refine ⟨49809083073265156096887619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66412110764353541462516825 49809083073265156096887619)
    ·
      refine ⟨74713624609897734145331429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49809083073265156096887619 74713624609897734145331429)
      ·
        refine ⟨14008804614355825152249643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74713624609897734145331429 14008804614355825152249643)
        ·
          refine ⟨21013206921533737728374465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14008804614355825152249643 21013206921533737728374465)
          ·
            refine ⟨15759905191150303296280849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21013206921533737728374465 15759905191150303296280849)
            ·
              refine ⟨11819928893362727472210637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15759905191150303296280849 11819928893362727472210637)
              ·
                refine ⟨4432473335011022802078989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11819928893362727472210637 4432473335011022802078989)
                ·
                  refine ⟨1662177500629133550779621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4432473335011022802078989 1662177500629133550779621)
                  ·
                    refine ⟨311658281367962540771179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1662177500629133550779621 311658281367962540771179)
                    ·
                      rfl

theorem cell23_1820857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 4].length) (baseStart_1820857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820857 prefixEnd_1820857 := by exact prefixLift 1820857
  have htrace : WordTrace (prefixWord ++ tailWord_1820857) baseStart_1820857 baseEnd_1820857 := by
    simpa [prefixWord, tailWord_1820857, baseEnd_1820857] using wordTrace_append hprefix tailTrace_1820857
  have hstable : (prefixWord ++ tailWord_1820857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820857).length < 2 ^ (prefixWord ++ tailWord_1820857).sum := by decide
  have hdescent : baseEnd_1820857 < baseStart_1820857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820864 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 2, 4, 2]
def baseStart_1820864 : Nat := 118140960795 + 1820864 * 2 ^ 59
def prefixEnd_1820864 : Nat := 4983230072969 + 3 ^ 40 * 1820864 * 2
def baseEnd_1820864 : Nat := 934978438468469094926005

theorem tailTrace_1820864 : CollatzResearch.WordTrace tailWord_1820864 prefixEnd_1820864 934978438468469094926005 := by
  unfold tailWord_1820864
  simp only [CollatzResearch.WordTrace]
  refine ⟨33206183037664090829010823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44274910716885454438681097 33206183037664090829010823)
  ·
    refine ⟨49809274556496136243516235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33206183037664090829010823 49809274556496136243516235)
    ·
      refine ⟨74713911834744204365274353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49809274556496136243516235 74713911834744204365274353)
      ·
        refine ⟨56035433876058153273955765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74713911834744204365274353 56035433876058153273955765)
        ·
          refine ⟨5253321925880451869433353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56035433876058153273955765 5253321925880451869433353)
          ·
            refine ⟨3939991444410338902075015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5253321925880451869433353 3939991444410338902075015)
            ·
              refine ⟨5909987166615508353112523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939991444410338902075015 5909987166615508353112523)
              ·
                refine ⟨8864980749923262529668785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909987166615508353112523 8864980749923262529668785)
                ·
                  refine ⟨6648735562442446897251589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8864980749923262529668785 6648735562442446897251589)
                  ·
                    refine ⟨1246637917957958793234673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6648735562442446897251589 1246637917957958793234673)
                    ·
                      refine ⟨934978438468469094926005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246637917957958793234673 934978438468469094926005)
                      ·
                        rfl

theorem cell23_1820864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_1820864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820864 prefixEnd_1820864 := by exact prefixLift 1820864
  have htrace : WordTrace (prefixWord ++ tailWord_1820864) baseStart_1820864 baseEnd_1820864 := by
    simpa [prefixWord, tailWord_1820864, baseEnd_1820864] using wordTrace_append hprefix tailTrace_1820864
  have hstable : (prefixWord ++ tailWord_1820864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820864).length < 2 ^ (prefixWord ++ tailWord_1820864).sum := by decide
  have hdescent : baseEnd_1820864 < baseStart_1820864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820904 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 6]
def baseStart_1820904 : Nat := 118140960795 + 1820904 * 2 ^ 59
def prefixEnd_1820904 : Nat := 4983230072969 + 3 ^ 40 * 1820904 * 2
def baseEnd_1820904 : Nat := 103888775299405437602869

theorem tailTrace_1820904 : CollatzResearch.WordTrace tailWord_1820904 prefixEnd_1820904 103888775299405437602869 := by
  unfold tailWord_1820904
  simp only [CollatzResearch.WordTrace]
  refine ⟨33206912497591634244738883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44275883330122178992985177 33206912497591634244738883)
  ·
    refine ⟨49810368746387451367108325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33206912497591634244738883 49810368746387451367108325)
    ·
      refine ⟨9339444139947647131332811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49810368746387451367108325 9339444139947647131332811)
      ·
        refine ⟨14009166209921470696999217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339444139947647131332811 14009166209921470696999217)
        ·
          refine ⟨10506874657441103022749413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14009166209921470696999217 10506874657441103022749413)
          ·
            refine ⟨1970038998270206816765515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10506874657441103022749413 1970038998270206816765515)
            ·
              refine ⟨2955058497405310225148273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970038998270206816765515 2955058497405310225148273)
              ·
                refine ⟨2216293873053982668861205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955058497405310225148273 2216293873053982668861205)
                ·
                  refine ⟨103888775299405437602869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2216293873053982668861205 103888775299405437602869)
                  ·
                    rfl

theorem cell23_1820904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 6].length) (baseStart_1820904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820904 prefixEnd_1820904 := by exact prefixLift 1820904
  have htrace : WordTrace (prefixWord ++ tailWord_1820904) baseStart_1820904 baseEnd_1820904 := by
    simpa [prefixWord, tailWord_1820904, baseEnd_1820904] using wordTrace_append hprefix tailTrace_1820904
  have hstable : (prefixWord ++ tailWord_1820904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820904).length < 2 ^ (prefixWord ++ tailWord_1820904).sum := by decide
  have hdescent : baseEnd_1820904 < baseStart_1820904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820924 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_1820924 : Nat := 118140960795 + 1820924 * 2 ^ 59
def prefixEnd_1820924 : Nat := 4983230072969 + 3 ^ 40 * 1820924 * 2
def baseEnd_1820924 : Nat := 935009247307738860175729

theorem tailTrace_1820924 : CollatzResearch.WordTrace tailWord_1820924 prefixEnd_1820924 935009247307738860175729 := by
  unfold tailWord_1820924
  simp only [CollatzResearch.WordTrace]
  refine ⟨33207277227555405952602913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44276369636740541270137217 33207277227555405952602913)
  ·
    refine ⟨24905457920666554464452185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33207277227555405952602913 24905457920666554464452185)
    ·
      refine ⟨18679093440499915848339139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24905457920666554464452185 18679093440499915848339139)
      ·
        refine ⟨28018640160749873772508709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18679093440499915848339139 28018640160749873772508709)
        ·
          refine ⟨5253495030140601332345383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28018640160749873772508709 5253495030140601332345383)
          ·
            refine ⟨7880242545210901998518075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253495030140601332345383 7880242545210901998518075)
            ·
              refine ⟨11820363817816352997777113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880242545210901998518075 11820363817816352997777113)
              ·
                refine ⟨8865272863362264748332835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11820363817816352997777113 8865272863362264748332835)
                ·
                  refine ⟨13297909295043397122499253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8865272863362264748332835 13297909295043397122499253)
                  ·
                    refine ⟨1246678996410318480234305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13297909295043397122499253 1246678996410318480234305)
                    ·
                      refine ⟨935009247307738860175729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246678996410318480234305 935009247307738860175729)
                      ·
                        rfl

theorem cell23_1820924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_1820924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820924 prefixEnd_1820924 := by exact prefixLift 1820924
  have htrace : WordTrace (prefixWord ++ tailWord_1820924) baseStart_1820924 baseEnd_1820924 := by
    simpa [prefixWord, tailWord_1820924, baseEnd_1820924] using wordTrace_append hprefix tailTrace_1820924
  have hstable : (prefixWord ++ tailWord_1820924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820924).length < 2 ^ (prefixWord ++ tailWord_1820924).sum := by decide
  have hdescent : baseEnd_1820924 < baseStart_1820924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820958 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1820958 : Nat := 118140960795 + 1820958 * 2 ^ 59
def prefixEnd_1820958 : Nat := 4983230072969 + 3 ^ 40 * 1820958 * 2
def baseEnd_1820958 : Nat := 935026705649991727150573

theorem tailTrace_1820958 : CollatzResearch.WordTrace tailWord_1820958 prefixEnd_1820958 935026705649991727150573 := by
  unfold tailWord_1820958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301974317123454463992941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44277196357991757141295685 8301974317123454463992941)
  ·
    refine ⟨3113240368921295423997353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8301974317123454463992941 3113240368921295423997353)
    ·
      refine ⟨2334930276690971567998015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3113240368921295423997353 2334930276690971567998015)
      ·
        refine ⟨3502395415036457351997023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2334930276690971567998015 3502395415036457351997023)
        ·
          refine ⟨5253593122554686027995535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502395415036457351997023 5253593122554686027995535)
          ·
            refine ⟨7880389683832029041993303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253593122554686027995535 7880389683832029041993303)
            ·
              refine ⟨11820584525748043562989955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880389683832029041993303 11820584525748043562989955)
              ·
                refine ⟨17730876788622065344484933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11820584525748043562989955 17730876788622065344484933)
                ·
                  refine ⟨3324539397866637252090925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17730876788622065344484933 3324539397866637252090925)
                  ·
                    refine ⟨1246702274199988969534097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324539397866637252090925 1246702274199988969534097)
                    ·
                      refine ⟨935026705649991727150573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246702274199988969534097 935026705649991727150573)
                      ·
                        rfl

theorem cell23_1820958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1820958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820958 prefixEnd_1820958 := by exact prefixLift 1820958
  have htrace : WordTrace (prefixWord ++ tailWord_1820958) baseStart_1820958 baseEnd_1820958 := by
    simpa [prefixWord, tailWord_1820958, baseEnd_1820958] using wordTrace_append hprefix tailTrace_1820958
  have hstable : (prefixWord ++ tailWord_1820958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820958).length < 2 ^ (prefixWord ++ tailWord_1820958).sum := by decide
  have hdescent : baseEnd_1820958 < baseStart_1820958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820964 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_1820964 : Nat := 118140960795 + 1820964 * 2 ^ 59
def prefixEnd_1820964 : Nat := 4983230072969 + 3 ^ 40 * 1820964 * 2
def baseEnd_1820964 : Nat := 311676595511306234558515

theorem tailTrace_1820964 : CollatzResearch.WordTrace tailWord_1820964 prefixEnd_1820964 311676595511306234558515 := by
  unfold tailWord_1820964
  simp only [CollatzResearch.WordTrace]
  refine ⟨33208006687482949368330973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44277342249977265824441297 33208006687482949368330973)
  ·
    refine ⟨12453002507806106013124115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33208006687482949368330973 12453002507806106013124115)
    ·
      refine ⟨18679503761709159019686173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12453002507806106013124115 18679503761709159019686173)
      ·
        refine ⟨7004813910640934632382315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18679503761709159019686173 7004813910640934632382315)
        ·
          refine ⟨10507220865961401948573473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004813910640934632382315 10507220865961401948573473)
          ·
            refine ⟨7880415649471051461430105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10507220865961401948573473 7880415649471051461430105)
            ·
              refine ⟨5910311737103288596072579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7880415649471051461430105 5910311737103288596072579)
              ·
                refine ⟨8865467605654932894108869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910311737103288596072579 8865467605654932894108869)
                ·
                  refine ⟨1662275176060299917645413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8865467605654932894108869 1662275176060299917645413)
                  ·
                    refine ⟨311676595511306234558515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1662275176060299917645413 311676595511306234558515)
                    ·
                      rfl

theorem cell23_1820964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_1820964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820964 prefixEnd_1820964 := by exact prefixLift 1820964
  have htrace : WordTrace (prefixWord ++ tailWord_1820964) baseStart_1820964 baseEnd_1820964 := by
    simpa [prefixWord, tailWord_1820964, baseEnd_1820964] using wordTrace_append hprefix tailTrace_1820964
  have hstable : (prefixWord ++ tailWord_1820964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820964).length < 2 ^ (prefixWord ++ tailWord_1820964).sum := by decide
  have hdescent : baseEnd_1820964 < baseStart_1820964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820965 : List Nat := [1, 3, 1, 2, 5, 1, 3, 2, 1, 1, 3]
def baseStart_1820965 : Nat := 118140960795 + 1820965 * 2 ^ 59
def prefixEnd_1820965 : Nat := 4983230072969 + 3 ^ 40 * 1820965 * 2
def baseEnd_1820965 : Nat := 935030300014573199763041

theorem tailTrace_1820965 : CollatzResearch.WordTrace tailWord_1820965 prefixEnd_1820965 935030300014573199763041 := by
  unfold tailWord_1820965
  simp only [CollatzResearch.WordTrace]
  refine ⟨66416049847962275907448349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44277366565308183938298899 66416049847962275907448349)
  ·
    refine ⟨24906018692985853465293131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66416049847962275907448349 24906018692985853465293131)
    ·
      refine ⟨37359028039478780197939697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24906018692985853465293131 37359028039478780197939697)
      ·
        refine ⟨28019271029609085148454773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37359028039478780197939697 28019271029609085148454773)
        ·
          refine ⟨2626806659025851732667635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28019271029609085148454773 2626806659025851732667635)
          ·
            refine ⟨3940209988538777599001453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626806659025851732667635 3940209988538777599001453)
            ·
              refine ⟨1477578745702041599625545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3940209988538777599001453 1477578745702041599625545)
              ·
                refine ⟨1108184059276531199719159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477578745702041599625545 1108184059276531199719159)
                ·
                  refine ⟨1662276088914796799578739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108184059276531199719159 1662276088914796799578739)
                  ·
                    refine ⟨2493414133372195199368109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1662276088914796799578739 2493414133372195199368109)
                    ·
                      refine ⟨935030300014573199763041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2493414133372195199368109 935030300014573199763041)
                      ·
                        rfl

theorem cell23_1820965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_1820965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1820965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1820965 prefixEnd_1820965 := by exact prefixLift 1820965
  have htrace : WordTrace (prefixWord ++ tailWord_1820965) baseStart_1820965 baseEnd_1820965 := by
    simpa [prefixWord, tailWord_1820965, baseEnd_1820965] using wordTrace_append hprefix tailTrace_1820965
  have hstable : (prefixWord ++ tailWord_1820965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820965).length < 2 ^ (prefixWord ++ tailWord_1820965).sum := by decide
  have hdescent : baseEnd_1820965 < baseStart_1820965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821004 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1821004 : Nat := 118140960795 + 1821004 * 2 ^ 59
def prefixEnd_1821004 : Nat := 4983230072969 + 3 ^ 40 * 1821004 * 2
def baseEnd_1821004 : Nat := 935050325760098547175361

theorem tailTrace_1821004 : CollatzResearch.WordTrace tailWord_1821004 prefixEnd_1821004 935050325760098547175361 := by
  unfold tailWord_1821004
  simp only [CollatzResearch.WordTrace]
  refine ⟨33208736147410492784059033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44278314863213990378745377 33208736147410492784059033)
  ·
    refine ⟨24906552110557869588044275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33208736147410492784059033 24906552110557869588044275)
    ·
      refine ⟨37359828165836804382066413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24906552110557869588044275 37359828165836804382066413)
      ·
        refine ⟨14009935562188801643274905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37359828165836804382066413 14009935562188801643274905)
        ·
          refine ⟨10507451671641601232456179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14009935562188801643274905 10507451671641601232456179)
          ·
            refine ⟨15761177507462401848684269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507451671641601232456179 15761177507462401848684269)
            ·
              refine ⟨5910441565298400693256601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15761177507462401848684269 5910441565298400693256601)
              ·
                refine ⟨4432831173973800519942451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5910441565298400693256601 4432831173973800519942451)
                ·
                  refine ⟨6649246760960700779913677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432831173973800519942451 6649246760960700779913677)
                  ·
                    refine ⟨2493467535360262792467629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6649246760960700779913677 2493467535360262792467629)
                    ·
                      refine ⟨935050325760098547175361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2493467535360262792467629 935050325760098547175361)
                      ·
                        rfl

theorem cell23_1821004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1821004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821004 prefixEnd_1821004 := by exact prefixLift 1821004
  have htrace : WordTrace (prefixWord ++ tailWord_1821004) baseStart_1821004 baseEnd_1821004 := by
    simpa [prefixWord, tailWord_1821004, baseEnd_1821004] using wordTrace_append hprefix tailTrace_1821004
  have hstable : (prefixWord ++ tailWord_1821004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821004).length < 2 ^ (prefixWord ++ tailWord_1821004).sum := by decide
  have hdescent : baseEnd_1821004 < baseStart_1821004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821027 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1821027 : Nat := 118140960795 + 1821027 * 2 ^ 59
def prefixEnd_1821027 : Nat := 4983230072969 + 3 ^ 40 * 1821027 * 2
def baseEnd_1821027 : Nat := 935062135815151957187755

theorem tailTrace_1821027 : CollatzResearch.WordTrace tailWord_1821027 prefixEnd_1821027 935062135815151957187755 := by
  unfold tailWord_1821027
  simp only [CollatzResearch.WordTrace]
  refine ⟨66418311173737660496205335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44278874115825106997470223 66418311173737660496205335)
  ·
    refine ⟨99627466760606490744308003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66418311173737660496205335 99627466760606490744308003)
    ·
      refine ⟨149441200140909736116462005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99627466760606490744308003 149441200140909736116462005)
      ·
        refine ⟨14010112513210287760918313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149441200140909736116462005 14010112513210287760918313)
        ·
          refine ⟨10507584384907715820688735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14010112513210287760918313 10507584384907715820688735)
          ·
            refine ⟨15761376577361573731033103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507584384907715820688735 15761376577361573731033103)
            ·
              refine ⟨23642064866042360596549655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15761376577361573731033103 23642064866042360596549655)
              ·
                refine ⟨35463097299063540894824483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23642064866042360596549655 35463097299063540894824483)
                ·
                  refine ⟨53194645948595311342236725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35463097299063540894824483 53194645948595311342236725)
                  ·
                    refine ⟨4986998057680810438334693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53194645948595311342236725 4986998057680810438334693)
                    ·
                      refine ⟨935062135815151957187755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4986998057680810438334693 935062135815151957187755)
                      ·
                        rfl

theorem cell23_1821027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1821027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821027 prefixEnd_1821027 := by exact prefixLift 1821027
  have htrace : WordTrace (prefixWord ++ tailWord_1821027) baseStart_1821027 baseEnd_1821027 := by
    simpa [prefixWord, tailWord_1821027, baseEnd_1821027] using wordTrace_append hprefix tailTrace_1821027
  have hstable : (prefixWord ++ tailWord_1821027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821027).length < 2 ^ (prefixWord ++ tailWord_1821027).sum := by decide
  have hdescent : baseEnd_1821027 < baseStart_1821027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821031 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_1821031 : Nat := 118140960795 + 1821031 * 2 ^ 59
def prefixEnd_1821031 : Nat := 4983230072969 + 3 ^ 40 * 1821031 * 2
def baseEnd_1821031 : Nat := 935064189737769941537737

theorem tailTrace_1821031 : CollatzResearch.WordTrace tailWord_1821031 prefixEnd_1821031 935064189737769941537737 := by
  unfold tailWord_1821031
  simp only [CollatzResearch.WordTrace]
  refine ⟨66418457065723169179350947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44278971377148779452900631 66418457065723169179350947)
  ·
    refine ⟨99627685598584753769026421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66418457065723169179350947 99627685598584753769026421)
    ·
      refine ⟨9340095524867320665846227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99627685598584753769026421 9340095524867320665846227)
      ·
        refine ⟨14010143287300980998769341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9340095524867320665846227 14010143287300980998769341)
        ·
          refine ⟨5253803732737867874538503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14010143287300980998769341 5253803732737867874538503)
          ·
            refine ⟨7880705599106801811807755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253803732737867874538503 7880705599106801811807755)
            ·
              refine ⟨11821058398660202717711633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880705599106801811807755 11821058398660202717711633)
              ·
                refine ⟨8865793798995152038283725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11821058398660202717711633 8865793798995152038283725)
                ·
                  refine ⟨3324672674623182014356397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8865793798995152038283725 3324672674623182014356397)
                  ·
                    refine ⟨1246752252983693255383649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324672674623182014356397 1246752252983693255383649)
                    ·
                      refine ⟨935064189737769941537737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246752252983693255383649 935064189737769941537737)
                      ·
                        rfl

theorem cell23_1821031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_1821031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821031 prefixEnd_1821031 := by exact prefixLift 1821031
  have htrace : WordTrace (prefixWord ++ tailWord_1821031) baseStart_1821031 baseEnd_1821031 := by
    simpa [prefixWord, tailWord_1821031, baseEnd_1821031] using wordTrace_append hprefix tailTrace_1821031
  have hstable : (prefixWord ++ tailWord_1821031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821031).length < 2 ^ (prefixWord ++ tailWord_1821031).sum := by decide
  have hdescent : baseEnd_1821031 < baseStart_1821031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821047 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_1821047 : Nat := 118140960795 + 1821047 * 2 ^ 59
def prefixEnd_1821047 : Nat := 4983230072969 + 3 ^ 40 * 1821047 * 2
def baseEnd_1821047 : Nat := 935072405428241878937663

theorem tailTrace_1821047 : CollatzResearch.WordTrace tailWord_1821047 prefixEnd_1821047 935072405428241878937663 := by
  unfold tailWord_1821047
  simp only [CollatzResearch.WordTrace]
  refine ⟨66419040633665203911933395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44279360422443469274622263 66419040633665203911933395)
  ·
    refine ⟨99628560950497805867900093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66419040633665203911933395 99628560950497805867900093)
    ·
      refine ⟨37360710356436677200462535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99628560950497805867900093 37360710356436677200462535)
      ·
        refine ⟨56041065534655015800693803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37360710356436677200462535 56041065534655015800693803)
        ·
          refine ⟨84061598301982523701040705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56041065534655015800693803 84061598301982523701040705)
          ·
            refine ⟨63046198726486892775780529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84061598301982523701040705 63046198726486892775780529)
            ·
              refine ⟨47284649044865169581835397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63046198726486892775780529 47284649044865169581835397)
              ·
                refine ⟨8865871695912219296594137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47284649044865169581835397 8865871695912219296594137)
                ·
                  refine ⟨6649403771934164472445603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8865871695912219296594137 6649403771934164472445603)
                  ·
                    refine ⟨9974105657901246708668405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6649403771934164472445603 9974105657901246708668405)
                    ·
                      refine ⟨935072405428241878937663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9974105657901246708668405 935072405428241878937663)
                      ·
                        rfl

theorem cell23_1821047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_1821047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821047 prefixEnd_1821047 := by exact prefixLift 1821047
  have htrace : WordTrace (prefixWord ++ tailWord_1821047) baseStart_1821047 baseEnd_1821047 := by
    simpa [prefixWord, tailWord_1821047, baseEnd_1821047] using wordTrace_append hprefix tailTrace_1821047
  have hstable : (prefixWord ++ tailWord_1821047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821047).length < 2 ^ (prefixWord ++ tailWord_1821047).sum := by decide
  have hdescent : baseEnd_1821047 < baseStart_1821047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821061 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 4, 2, 2]
def baseStart_1821061 : Nat := 118140960795 + 1821061 * 2 ^ 59
def prefixEnd_1821061 : Nat := 4983230072969 + 3 ^ 40 * 1821061 * 2
def baseEnd_1821061 : Nat := 935079594157404824162599

theorem tailTrace_1821061 : CollatzResearch.WordTrace tailWord_1821061 prefixEnd_1821061 935079594157404824162599 := by
  unfold tailWord_1821061
  simp only [CollatzResearch.WordTrace]
  refine ⟨66419551255614484302943037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44279700837076322868628691 66419551255614484302943037)
  ·
    refine ⟨24907331720855431613603639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66419551255614484302943037 24907331720855431613603639)
    ·
      refine ⟨37360997581283147420405459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24907331720855431613603639 37360997581283147420405459)
      ·
        refine ⟨56041496371924721130608189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37360997581283147420405459 56041496371924721130608189)
        ·
          refine ⟨21015561139471770423978071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56041496371924721130608189 21015561139471770423978071)
          ·
            refine ⟨31523341709207655635967107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21015561139471770423978071 31523341709207655635967107)
            ·
              refine ⟨47285012563811483453950661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31523341709207655635967107 47285012563811483453950661)
              ·
                refine ⟨8865939855714653147615749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47285012563811483453950661 8865939855714653147615749)
                ·
                  refine ⟨1662363722946497465177953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8865939855714653147615749 1662363722946497465177953)
                  ·
                    refine ⟨1246772792209873098883465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662363722946497465177953 1246772792209873098883465)
                    ·
                      refine ⟨935079594157404824162599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246772792209873098883465 935079594157404824162599)
                      ·
                        rfl

theorem cell23_1821061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_1821061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821061 prefixEnd_1821061 := by exact prefixLift 1821061
  have htrace : WordTrace (prefixWord ++ tailWord_1821061) baseStart_1821061 baseEnd_1821061 := by
    simpa [prefixWord, tailWord_1821061, baseEnd_1821061] using wordTrace_append hprefix tailTrace_1821061
  have hstable : (prefixWord ++ tailWord_1821061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821061).length < 2 ^ (prefixWord ++ tailWord_1821061).sum := by decide
  have hdescent : baseEnd_1821061 < baseStart_1821061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821065 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 1, 3, 2]
def baseStart_1821065 : Nat := 118140960795 + 1821065 * 2 ^ 59
def prefixEnd_1821065 : Nat := 4983230072969 + 3 ^ 40 * 1821065 * 2
def baseEnd_1821065 : Nat := 935081648080022808512581

theorem tailTrace_1821065 : CollatzResearch.WordTrace tailWord_1821065 prefixEnd_1821065 935081648080022808512581 := by
  unfold tailWord_1821065
  simp only [CollatzResearch.WordTrace]
  refine ⟨66419697147599992986088649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44279798098399995324059099 66419697147599992986088649)
  ·
    refine ⟨49814772860699994739566487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66419697147599992986088649 49814772860699994739566487)
    ·
      refine ⟨74722159291049992109349731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49814772860699994739566487 74722159291049992109349731)
      ·
        refine ⟨112083238936574988164024597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74722159291049992109349731 112083238936574988164024597)
        ·
          refine ⟨5253901825151952570188653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112083238936574988164024597 5253901825151952570188653)
          ·
            refine ⟨1970213184431982213820745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5253901825151952570188653 1970213184431982213820745)
            ·
              refine ⟨1477659888323986660365559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970213184431982213820745 1477659888323986660365559)
              ·
                refine ⟨2216489832485979990548339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477659888323986660365559 2216489832485979990548339)
                ·
                  refine ⟨3324734748728969985822509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216489832485979990548339 3324734748728969985822509)
                  ·
                    refine ⟨1246775530773363744683441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324734748728969985822509 1246775530773363744683441)
                    ·
                      refine ⟨935081648080022808512581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246775530773363744683441 935081648080022808512581)
                      ·
                        rfl

theorem cell23_1821065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 3, 2].length) (baseStart_1821065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821065 prefixEnd_1821065 := by exact prefixLift 1821065
  have htrace : WordTrace (prefixWord ++ tailWord_1821065) baseStart_1821065 baseEnd_1821065 := by
    simpa [prefixWord, tailWord_1821065, baseEnd_1821065] using wordTrace_append hprefix tailTrace_1821065
  have hstable : (prefixWord ++ tailWord_1821065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821065).length < 2 ^ (prefixWord ++ tailWord_1821065).sum := by decide
  have hdescent : baseEnd_1821065 < baseStart_1821065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821104 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 3, 7, 2]
def baseStart_1821104 : Nat := 118140960795 + 1821104 * 2 ^ 59
def prefixEnd_1821104 : Nat := 4983230072969 + 3 ^ 40 * 1821104 * 2
def baseEnd_1821104 : Nat := 935101673825548155924901

theorem tailTrace_1821104 : CollatzResearch.WordTrace tailWord_1821104 prefixEnd_1821104 935101673825548155924901 := by
  unfold tailWord_1821104
  simp only [CollatzResearch.WordTrace]
  refine ⟨33210559797229351323379183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44280746396305801764505577 33210559797229351323379183)
  ·
    refine ⟨49815839695844026985068775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33210559797229351323379183 49815839695844026985068775)
    ·
      refine ⟨74723759543766040477603163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49815839695844026985068775 74723759543766040477603163)
      ·
        refine ⟨112085639315649060716404745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74723759543766040477603163 112085639315649060716404745)
        ·
          refine ⟨84064229486736795537303559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112085639315649060716404745 84064229486736795537303559)
          ·
            refine ⟨126096344230105193305955339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84064229486736795537303559 126096344230105193305955339)
            ·
              refine ⟨189144516345157789958933009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126096344230105193305955339 189144516345157789958933009)
              ·
                refine ⟨141858387258868342469199757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189144516345157789958933009 141858387258868342469199757)
                ·
                  refine ⟨53196895222075628425949909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141858387258868342469199757 53196895222075628425949909)
                  ·
                    refine ⟨1246802231767397541233201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53196895222075628425949909 1246802231767397541233201)
                    ·
                      refine ⟨935101673825548155924901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246802231767397541233201 935101673825548155924901)
                      ·
                        rfl

theorem cell23_1821104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 7, 2].length) (baseStart_1821104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821104 prefixEnd_1821104 := by exact prefixLift 1821104
  have htrace : WordTrace (prefixWord ++ tailWord_1821104) baseStart_1821104 baseEnd_1821104 := by
    simpa [prefixWord, tailWord_1821104, baseEnd_1821104] using wordTrace_append hprefix tailTrace_1821104
  have hstable : (prefixWord ++ tailWord_1821104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821104).length < 2 ^ (prefixWord ++ tailWord_1821104).sum := by decide
  have hdescent : baseEnd_1821104 < baseStart_1821104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821107 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 5]
def baseStart_1821107 : Nat := 118140960795 + 1821107 * 2 ^ 59
def prefixEnd_1821107 : Nat := 4983230072969 + 3 ^ 40 * 1821107 * 2
def baseEnd_1821107 : Nat := 935103214267511644187387

theorem tailTrace_1821107 : CollatzResearch.WordTrace tailWord_1821107 prefixEnd_1821107 935103214267511644187387 := by
  unfold tailWord_1821107
  simp only [CollatzResearch.WordTrace]
  refine ⟨66421229013447834159117575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44280819342298556106078383 66421229013447834159117575)
  ·
    refine ⟨99631843520171751238676363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66421229013447834159117575 99631843520171751238676363)
    ·
      refine ⟨149447765280257626858014545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99631843520171751238676363 149447765280257626858014545)
      ·
        refine ⟨112085823960193220143510909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149447765280257626858014545 112085823960193220143510909)
        ·
          refine ⟨42032183985072457553816591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112085823960193220143510909 42032183985072457553816591)
          ·
            refine ⟨63048275977608686330724887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42032183985072457553816591 63048275977608686330724887)
            ·
              refine ⟨94572413966413029496087331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63048275977608686330724887 94572413966413029496087331)
              ·
                refine ⟨141858620949619544244130997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94572413966413029496087331 141858620949619544244130997)
                ·
                  refine ⟨13299245714026832272887281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141858620949619544244130997 13299245714026832272887281)
                  ·
                    refine ⟨9974434285520124204665461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13299245714026832272887281 9974434285520124204665461)
                    ·
                      refine ⟨935103214267511644187387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9974434285520124204665461 935103214267511644187387)
                      ·
                        rfl

theorem cell23_1821107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_1821107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821107 prefixEnd_1821107 := by exact prefixLift 1821107
  have htrace : WordTrace (prefixWord ++ tailWord_1821107) baseStart_1821107 baseEnd_1821107 := by
    simpa [prefixWord, tailWord_1821107, baseEnd_1821107] using wordTrace_append hprefix tailTrace_1821107
  have hstable : (prefixWord ++ tailWord_1821107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821107).length < 2 ^ (prefixWord ++ tailWord_1821107).sum := by decide
  have hdescent : baseEnd_1821107 < baseStart_1821107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821171 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 3]
def baseStart_1821171 : Nat := 118140960795 + 1821171 * 2 ^ 59
def prefixEnd_1821171 : Nat := 4983230072969 + 3 ^ 40 * 1821171 * 2
def baseEnd_1821171 : Nat := 935136077029399393787093

theorem tailTrace_1821171 : CollatzResearch.WordTrace tailWord_1821171 prefixEnd_1821171 935136077029399393787093 := by
  unfold tailWord_1821171
  simp only [CollatzResearch.WordTrace]
  refine ⟨66423563285215973089447367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44282375523477315392964911 66423563285215973089447367)
  ·
    refine ⟨99635344927823959634171051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66423563285215973089447367 99635344927823959634171051)
    ·
      refine ⟨149453017391735939451256577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99635344927823959634171051 149453017391735939451256577)
      ·
        refine ⟨112089763043801954588442433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149453017391735939451256577 112089763043801954588442433)
        ·
          refine ⟨84067322282851465941331825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112089763043801954588442433 84067322282851465941331825)
          ·
            refine ⟨63050491712138599455998869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84067322282851465941331825 63050491712138599455998869)
            ·
              refine ⟨2955491799006496849499947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63050491712138599455998869 2955491799006496849499947)
              ·
                refine ⟨4433237698509745274249921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955491799006496849499947 4433237698509745274249921)
                ·
                  refine ⟨3324928273882308955687441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433237698509745274249921 3324928273882308955687441)
                  ·
                    refine ⟨2493696205411731716765581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3324928273882308955687441 2493696205411731716765581)
                    ·
                      refine ⟨935136077029399393787093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2493696205411731716765581 935136077029399393787093)
                      ·
                        rfl

theorem cell23_1821171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_1821171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821171 prefixEnd_1821171 := by exact prefixLift 1821171
  have htrace : WordTrace (prefixWord ++ tailWord_1821171) baseStart_1821171 baseEnd_1821171 := by
    simpa [prefixWord, tailWord_1821171, baseEnd_1821171] using wordTrace_append hprefix tailTrace_1821171
  have hstable : (prefixWord ++ tailWord_1821171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821171).length < 2 ^ (prefixWord ++ tailWord_1821171).sum := by decide
  have hdescent : baseEnd_1821171 < baseStart_1821171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821188 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1821188 : Nat := 118140960795 + 1821188 * 2 ^ 59
def prefixEnd_1821188 : Nat := 4983230072969 + 3 ^ 40 * 1821188 * 2
def baseEnd_1821188 : Nat := 935144806200525827274515

theorem tailTrace_1821188 : CollatzResearch.WordTrace tailWord_1821188 prefixEnd_1821188 935144806200525827274515 := by
  unfold tailWord_1821188
  simp only [CollatzResearch.WordTrace]
  refine ⟨33212091663077192496408109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44282788884102923328544145 33212091663077192496408109)
  ·
    refine ⟨12454534373653947186153041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33212091663077192496408109 12454534373653947186153041)
    ·
      refine ⟨9340900780240460389614781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12454534373653947186153041 9340900780240460389614781)
      ·
        refine ⟨3502837792590172646105543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9340900780240460389614781 3502837792590172646105543)
        ·
          refine ⟨5254256688885258969158315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502837792590172646105543 5254256688885258969158315)
          ·
            refine ⟨7881385033327888453737473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254256688885258969158315 7881385033327888453737473)
            ·
              refine ⟨5911038774995916340303105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7881385033327888453737473 5911038774995916340303105)
              ·
                refine ⟨4433279081246937255227329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5911038774995916340303105 4433279081246937255227329)
                ·
                  refine ⟨3324959310935202941420497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433279081246937255227329 3324959310935202941420497)
                  ·
                    refine ⟨2493719483201402206065373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3324959310935202941420497 2493719483201402206065373)
                    ·
                      refine ⟨935144806200525827274515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2493719483201402206065373 935144806200525827274515)
                      ·
                        rfl

theorem cell23_1821188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1821188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821188 prefixEnd_1821188 := by exact prefixLift 1821188
  have htrace : WordTrace (prefixWord ++ tailWord_1821188) baseStart_1821188 baseEnd_1821188 := by
    simpa [prefixWord, tailWord_1821188, baseEnd_1821188] using wordTrace_append hprefix tailTrace_1821188
  have hstable : (prefixWord ++ tailWord_1821188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821188).length < 2 ^ (prefixWord ++ tailWord_1821188).sum := by decide
  have hdescent : baseEnd_1821188 < baseStart_1821188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821194 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1821194 : Nat := 118140960795 + 1821194 * 2 ^ 59
def prefixEnd_1821194 : Nat := 4983230072969 + 3 ^ 40 * 1821194 * 2
def baseEnd_1821194 : Nat := 935147887084452803799487

theorem tailTrace_1821194 : CollatzResearch.WordTrace tailWord_1821194 prefixEnd_1821194 935147887084452803799487 := by
  unfold tailWord_1821194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606100541033162004383659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44282934776088432011689757 16606100541033162004383659)
  ·
    refine ⟨24909150811549743006575489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16606100541033162004383659 24909150811549743006575489)
    ·
      refine ⟨18681863108662307254931617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24909150811549743006575489 18681863108662307254931617)
      ·
        refine ⟨14011397331496730441198713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18681863108662307254931617 14011397331496730441198713)
        ·
          refine ⟨10508547998622547830899035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14011397331496730441198713 10508547998622547830899035)
          ·
            refine ⟨15762821997933821746348553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10508547998622547830899035 15762821997933821746348553)
            ·
              refine ⟨11822116498450366309761415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15762821997933821746348553 11822116498450366309761415)
              ·
                refine ⟨17733174747675549464642123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11822116498450366309761415 17733174747675549464642123)
                ·
                  refine ⟨26599762121513324196963185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17733174747675549464642123 26599762121513324196963185)
                  ·
                    refine ⟨19949821591134993147722389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26599762121513324196963185 19949821591134993147722389)
                    ·
                      refine ⟨935147887084452803799487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19949821591134993147722389 935147887084452803799487)
                      ·
                        rfl

theorem cell23_1821194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1821194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821194 prefixEnd_1821194 := by exact prefixLift 1821194
  have htrace : WordTrace (prefixWord ++ tailWord_1821194) baseStart_1821194 baseEnd_1821194 := by
    simpa [prefixWord, tailWord_1821194, baseEnd_1821194] using wordTrace_append hprefix tailTrace_1821194
  have hstable : (prefixWord ++ tailWord_1821194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821194).length < 2 ^ (prefixWord ++ tailWord_1821194).sum := by decide
  have hdescent : baseEnd_1821194 < baseStart_1821194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821195 : List Nat := [1, 1, 1, 1, 7, 1, 4, 2, 1, 4]
def baseStart_1821195 : Nat := 118140960795 + 1821195 * 2 ^ 59
def prefixEnd_1821195 : Nat := 4983230072969 + 3 ^ 40 * 1821195 * 2
def baseEnd_1821195 : Nat := 311716133521702433295661

theorem tailTrace_1821195 : CollatzResearch.WordTrace tailWord_1821195 prefixEnd_1821195 311716133521702433295661 := by
  unfold tailWord_1821195
  simp only [CollatzResearch.WordTrace]
  refine ⟨66424438637129025188321039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44282959091419350125547359 66424438637129025188321039)
  ·
    refine ⟨99636657955693537782481559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66424438637129025188321039 99636657955693537782481559)
    ·
      refine ⟨149454986933540306673722339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99636657955693537782481559 149454986933540306673722339)
      ·
        refine ⟨224182480400310460010583509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149454986933540306673722339 224182480400310460010583509)
        ·
          refine ⟨5254276884382276406498051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 224182480400310460010583509 5254276884382276406498051)
          ·
            refine ⟨7881415326573414609747077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254276884382276406498051 7881415326573414609747077)
            ·
              refine ⟨1477765373732515239327577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7881415326573414609747077 1477765373732515239327577)
              ·
                refine ⟨1108324030299386429495683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477765373732515239327577 1108324030299386429495683)
                ·
                  refine ⟨1662486045449079644243525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108324030299386429495683 1662486045449079644243525)
                  ·
                    refine ⟨311716133521702433295661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1662486045449079644243525 311716133521702433295661)
                    ·
                      rfl

theorem cell23_1821195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 4].length) (baseStart_1821195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821195 prefixEnd_1821195 := by exact prefixLift 1821195
  have htrace : WordTrace (prefixWord ++ tailWord_1821195) baseStart_1821195 baseEnd_1821195 := by
    simpa [prefixWord, tailWord_1821195, baseEnd_1821195] using wordTrace_append hprefix tailTrace_1821195
  have hstable : (prefixWord ++ tailWord_1821195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821195).length < 2 ^ (prefixWord ++ tailWord_1821195).sum := by decide
  have hdescent : baseEnd_1821195 < baseStart_1821195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821235 : List Nat := [1, 1, 1, 2, 4, 2, 4, 3, 1, 1, 3]
def baseStart_1821235 : Nat := 118140960795 + 1821235 * 2 ^ 59
def prefixEnd_1821235 : Nat := 4983230072969 + 3 ^ 40 * 1821235 * 2
def baseEnd_1821235 : Nat := 935168939791287143386799

theorem tailTrace_1821235 : CollatzResearch.WordTrace tailWord_1821235 prefixEnd_1821235 935168939791287143386799 := by
  unfold tailWord_1821235
  simp only [CollatzResearch.WordTrace]
  refine ⟨66425897556984112019777159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44283931704656074679851439 66425897556984112019777159)
  ·
    refine ⟨99638846335476168029665739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66425897556984112019777159 99638846335476168029665739)
    ·
      refine ⟨149458269503214252044498609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99638846335476168029665739 149458269503214252044498609)
      ·
        refine ⟨112093702127410689033373957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149458269503214252044498609 112093702127410689033373957)
        ·
          refine ⟨21017569148889504193757617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112093702127410689033373957 21017569148889504193757617)
          ·
            refine ⟨15763176861667128145318213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21017569148889504193757617 15763176861667128145318213)
            ·
              refine ⟨2955595661562586527247165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15763176861667128145318213 2955595661562586527247165)
              ·
                refine ⟨1108348373085969947717687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2955595661562586527247165 1108348373085969947717687)
                ·
                  refine ⟨1662522559628954921576531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108348373085969947717687 1662522559628954921576531)
                  ·
                    refine ⟨2493783839443432382364797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1662522559628954921576531 2493783839443432382364797)
                    ·
                      refine ⟨935168939791287143386799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2493783839443432382364797 935168939791287143386799)
                      ·
                        rfl

theorem cell23_1821235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 1, 3].length) (baseStart_1821235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821235 prefixEnd_1821235 := by exact prefixLift 1821235
  have htrace : WordTrace (prefixWord ++ tailWord_1821235) baseStart_1821235 baseEnd_1821235 := by
    simpa [prefixWord, tailWord_1821235, baseEnd_1821235] using wordTrace_append hprefix tailTrace_1821235
  have hstable : (prefixWord ++ tailWord_1821235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821235).length < 2 ^ (prefixWord ++ tailWord_1821235).sum := by decide
  have hdescent : baseEnd_1821235 < baseStart_1821235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821268 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_1821268 : Nat := 118140960795 + 1821268 * 2 ^ 59
def prefixEnd_1821268 : Nat := 4983230072969 + 3 ^ 40 * 1821268 * 2
def baseEnd_1821268 : Nat := 311728628217628504758049

theorem tailTrace_1821268 : CollatzResearch.WordTrace tailWord_1821268 prefixEnd_1821268 311728628217628504758049 := by
  unfold tailWord_1821268
  simp only [CollatzResearch.WordTrace]
  refine ⟨33213550582932279327864229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44284734110576372437152305 33213550582932279327864229)
  ·
    refine ⟨6227540734299802373974543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33213550582932279327864229 6227540734299802373974543)
    ·
      refine ⟨9341311101449703560961815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6227540734299802373974543 9341311101449703560961815)
      ·
        refine ⟨14011966652174555341442723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9341311101449703560961815 14011966652174555341442723)
        ·
          refine ⟨21017949978261833012164085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14011966652174555341442723 21017949978261833012164085)
          ·
            refine ⟨1970432810462046844890383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21017949978261833012164085 1970432810462046844890383)
            ·
              refine ⟨2955649215693070267335575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970432810462046844890383 2955649215693070267335575)
              ·
                refine ⟨4433473823539605401003363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955649215693070267335575 4433473823539605401003363)
                ·
                  refine ⟨6650210735309408101505045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4433473823539605401003363 6650210735309408101505045)
                  ·
                    refine ⟨311728628217628504758049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6650210735309408101505045 311728628217628504758049)
                    ·
                      rfl

theorem cell23_1821268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_1821268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821268 prefixEnd_1821268 := by exact prefixLift 1821268
  have htrace : WordTrace (prefixWord ++ tailWord_1821268) baseStart_1821268 baseEnd_1821268 := by
    simpa [prefixWord, tailWord_1821268, baseEnd_1821268] using wordTrace_append hprefix tailTrace_1821268
  have hstable : (prefixWord ++ tailWord_1821268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821268).length < 2 ^ (prefixWord ++ tailWord_1821268).sum := by decide
  have hdescent : baseEnd_1821268 < baseStart_1821268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821281 : List Nat := [1, 2, 3, 1, 1, 4, 4, 7]
def baseStart_1821281 : Nat := 118140960795 + 1821281 * 2 ^ 59
def prefixEnd_1821281 : Nat := 4983230072969 + 3 ^ 40 * 1821281 * 2
def baseEnd_1821281 : Nat := 34636761477829406052281

theorem tailTrace_1821281 : CollatzResearch.WordTrace tailWord_1821281 prefixEnd_1821281 34636761477829406052281 := by
  unfold tailWord_1821281
  simp only [CollatzResearch.WordTrace]
  refine ⟨66427575314817461875951697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44285050209878307917301131 66427575314817461875951697)
  ·
    refine ⟨49820681486113096406963773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66427575314817461875951697 49820681486113096406963773)
    ·
      refine ⟨18682755557292411152611415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49820681486113096406963773 18682755557292411152611415)
      ·
        refine ⟨28024133335938616728917123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18682755557292411152611415 28024133335938616728917123)
        ·
          refine ⟨42036200003907925093375685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28024133335938616728917123 42036200003907925093375685)
          ·
            refine ⟨7881787500732735955007941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42036200003907925093375685 7881787500732735955007941)
            ·
              refine ⟨1477835156387387991563989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7881787500732735955007941 1477835156387387991563989)
              ·
                refine ⟨34636761477829406052281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1477835156387387991563989 34636761477829406052281)
                ·
                  rfl

theorem cell23_1821281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 7].length) (baseStart_1821281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821281 prefixEnd_1821281 := by exact prefixLift 1821281
  have htrace : WordTrace (prefixWord ++ tailWord_1821281) baseStart_1821281 baseEnd_1821281 := by
    simpa [prefixWord, tailWord_1821281, baseEnd_1821281] using wordTrace_append hprefix tailTrace_1821281
  have hstable : (prefixWord ++ tailWord_1821281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821281).length < 2 ^ (prefixWord ++ tailWord_1821281).sum := by decide
  have hdescent : baseEnd_1821281 < baseStart_1821281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821292 : List Nat := [2, 2, 1, 1, 3, 1, 5, 3, 1, 2, 2]
def baseStart_1821292 : Nat := 118140960795 + 1821292 * 2 ^ 59
def prefixEnd_1821292 : Nat := 4983230072969 + 3 ^ 40 * 1821292 * 2
def baseEnd_1821292 : Nat := 935198208188593420374037

theorem tailTrace_1821292 : CollatzResearch.WordTrace tailWord_1821292 prefixEnd_1821292 935198208188593420374037 := by
  unfold tailWord_1821292
  simp only [CollatzResearch.WordTrace]
  refine ⟨33213988258888805377301065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44285317678518407169734753 33213988258888805377301065)
  ·
    refine ⟨24910491194166604032975799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33213988258888805377301065 24910491194166604032975799)
    ·
      refine ⟨37365736791249906049463699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24910491194166604032975799 37365736791249906049463699)
      ·
        refine ⟨56048605186874859074195549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37365736791249906049463699 56048605186874859074195549)
        ·
          refine ⟨21018226945078072152823331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56048605186874859074195549 21018226945078072152823331)
          ·
            refine ⟨31527340417617108229234997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21018226945078072152823331 31527340417617108229234997)
            ·
              refine ⟨2955688164151603896490781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31527340417617108229234997 2955688164151603896490781)
              ·
                refine ⟨1108383061556851461184043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2955688164151603896490781 1108383061556851461184043)
                ·
                  refine ⟨1662574592335277191776065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108383061556851461184043 1662574592335277191776065)
                  ·
                    refine ⟨1246930944251457893832049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662574592335277191776065 1246930944251457893832049)
                    ·
                      refine ⟨935198208188593420374037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246930944251457893832049 935198208188593420374037)
                      ·
                        rfl

theorem cell23_1821292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_1821292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821292 prefixEnd_1821292 := by exact prefixLift 1821292
  have htrace : WordTrace (prefixWord ++ tailWord_1821292) baseStart_1821292 baseEnd_1821292 := by
    simpa [prefixWord, tailWord_1821292, baseEnd_1821292] using wordTrace_append hprefix tailTrace_1821292
  have hstable : (prefixWord ++ tailWord_1821292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821292).length < 2 ^ (prefixWord ++ tailWord_1821292).sum := by decide
  have hdescent : baseEnd_1821292 < baseStart_1821292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821298 : List Nat := [3, 2, 1, 2, 5, 1, 9]
def baseStart_1821298 : Nat := 118140960795 + 1821298 * 2 ^ 59
def prefixEnd_1821298 : Nat := 4983230072969 + 3 ^ 40 * 1821298 * 2
def baseEnd_1821298 : Nat := 11545694926821239467889

theorem tailTrace_1821298 : CollatzResearch.WordTrace tailWord_1821298 prefixEnd_1821298 11545694926821239467889 := by
  unfold tailWord_1821298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16607048838938968444830137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44285463570503915852880365 16607048838938968444830137)
  ·
    refine ⟨12455286629204226333622603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16607048838938968444830137 12455286629204226333622603)
    ·
      refine ⟨18682929943806339500433905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12455286629204226333622603 18682929943806339500433905)
      ·
        refine ⟨14012197457854754625325429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18682929943806339500433905 14012197457854754625325429)
        ·
          refine ⟨1313643511673883246124259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14012197457854754625325429 1313643511673883246124259)
          ·
            refine ⟨1970465267510824869186389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313643511673883246124259 1970465267510824869186389)
            ·
              refine ⟨11545694926821239467889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1970465267510824869186389 11545694926821239467889)
              ·
                rfl

theorem cell23_1821298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 9].length) (baseStart_1821298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821298 prefixEnd_1821298 := by exact prefixLift 1821298
  have htrace : WordTrace (prefixWord ++ tailWord_1821298) baseStart_1821298 baseEnd_1821298 := by
    simpa [prefixWord, tailWord_1821298, baseEnd_1821298] using wordTrace_append hprefix tailTrace_1821298
  have hstable : (prefixWord ++ tailWord_1821298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821298).length < 2 ^ (prefixWord ++ tailWord_1821298).sum := by decide
  have hdescent : baseEnd_1821298 < baseStart_1821298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821308 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_1821308 : Nat := 118140960795 + 1821308 * 2 ^ 59
def prefixEnd_1821308 : Nat := 4983230072969 + 3 ^ 40 * 1821308 * 2
def baseEnd_1821308 : Nat := 935206423879065357773963

theorem tailTrace_1821308 : CollatzResearch.WordTrace tailWord_1821308 prefixEnd_1821308 935206423879065357773963 := by
  unfold tailWord_1821308
  simp only [CollatzResearch.WordTrace]
  refine ⟨33214280042859822743592289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44285706723813096991456385 33214280042859822743592289)
  ·
    refine ⟨24910710032144867057694217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33214280042859822743592289 24910710032144867057694217)
    ·
      refine ⟨18683032524108650293270663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24910710032144867057694217 18683032524108650293270663)
      ·
        refine ⟨28024548786162975439905995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18683032524108650293270663 28024548786162975439905995)
        ·
          refine ⟨42036823179244463159858993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28024548786162975439905995 42036823179244463159858993)
          ·
            refine ⟨31527617384433347369894245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42036823179244463159858993 31527617384433347369894245)
            ·
              refine ⟨5911428259581252631855171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31527617384433347369894245 5911428259581252631855171)
              ·
                refine ⟨8867142389371878947782757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911428259581252631855171 8867142389371878947782757)
                ·
                  refine ⟨1662589198007227302709267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8867142389371878947782757 1662589198007227302709267)
                  ·
                    refine ⟨2493883797010840954063901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1662589198007227302709267 2493883797010840954063901)
                    ·
                      refine ⟨935206423879065357773963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2493883797010840954063901 935206423879065357773963)
                      ·
                        rfl

theorem cell23_1821308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_1821308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821308 prefixEnd_1821308 := by exact prefixLift 1821308
  have htrace : WordTrace (prefixWord ++ tailWord_1821308) baseStart_1821308 baseEnd_1821308 := by
    simpa [prefixWord, tailWord_1821308, baseEnd_1821308] using wordTrace_append hprefix tailTrace_1821308
  have hstable : (prefixWord ++ tailWord_1821308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821308).length < 2 ^ (prefixWord ++ tailWord_1821308).sum := by decide
  have hdescent : baseEnd_1821308 < baseStart_1821308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821309 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_1821309 : Nat := 118140960795 + 1821309 * 2 ^ 59
def prefixEnd_1821309 : Nat := 4983230072969 + 3 ^ 40 * 1821309 * 2
def baseEnd_1821309 : Nat := 935206937359719853861459

theorem tailTrace_1821309 : CollatzResearch.WordTrace tailWord_1821309 prefixEnd_1821309 935206937359719853861459 := by
  unfold tailWord_1821309
  simp only [CollatzResearch.WordTrace]
  refine ⟨66428596558716022657970981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44285731039144015105313987 66428596558716022657970981)
  ·
    refine ⟨12455361854759254248369559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66428596558716022657970981 12455361854759254248369559)
    ·
      refine ⟨18683042782138881372554339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12455361854759254248369559 18683042782138881372554339)
      ·
        refine ⟨28024564173208322058831509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18683042782138881372554339 28024564173208322058831509)
        ·
          refine ⟨1313651445619140096507727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28024564173208322058831509 1313651445619140096507727)
          ·
            refine ⟨1970477168428710144761591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313651445619140096507727 1970477168428710144761591)
            ·
              refine ⟨2955715752643065217142387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970477168428710144761591 2955715752643065217142387)
              ·
                refine ⟨4433573628964597825713581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955715752643065217142387 4433573628964597825713581)
                ·
                  refine ⟨1662590110861724184642593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4433573628964597825713581 1662590110861724184642593)
                  ·
                    refine ⟨1246942583146293138481945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662590110861724184642593 1246942583146293138481945)
                    ·
                      refine ⟨935206937359719853861459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1246942583146293138481945 935206937359719853861459)
                      ·
                        rfl

theorem cell23_1821309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_1821309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821309 prefixEnd_1821309 := by exact prefixLift 1821309
  have htrace : WordTrace (prefixWord ++ tailWord_1821309) baseStart_1821309 baseEnd_1821309 := by
    simpa [prefixWord, tailWord_1821309, baseEnd_1821309] using wordTrace_append hprefix tailTrace_1821309
  have hstable : (prefixWord ++ tailWord_1821309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821309).length < 2 ^ (prefixWord ++ tailWord_1821309).sum := by decide
  have hdescent : baseEnd_1821309 < baseStart_1821309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821388 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 7]
def baseStart_1821388 : Nat := 118140960795 + 1821388 * 2 ^ 59
def prefixEnd_1821388 : Nat := 4983230072969 + 3 ^ 40 * 1821388 * 2
def baseEnd_1821388 : Nat := 103916389147936116085955

theorem tailTrace_1821388 : CollatzResearch.WordTrace tailWord_1821388 prefixEnd_1821388 103916389147936116085955 := by
  unfold tailWord_1821388
  simp only [CollatzResearch.WordTrace]
  refine ⟨33215738962714909575048409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44287651950286546100064545 33215738962714909575048409)
  ·
    refine ⟨24911804222036182181286307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33215738962714909575048409 24911804222036182181286307)
    ·
      refine ⟨37367706333054273271929461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24911804222036182181286307 37367706333054273271929461)
      ·
        refine ⟨3503222468723838119243387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37367706333054273271929461 3503222468723838119243387)
        ·
          refine ⟨5254833703085757178865081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3503222468723838119243387 5254833703085757178865081)
          ·
            refine ⟨3941125277314317884148811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5254833703085757178865081 3941125277314317884148811)
            ·
              refine ⟨5911687915971476826223217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941125277314317884148811 5911687915971476826223217)
              ·
                refine ⟨4433765936978607619667413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5911687915971476826223217 4433765936978607619667413)
                ·
                  refine ⟨103916389147936116085955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4433765936978607619667413 103916389147936116085955)
                  ·
                    rfl

theorem cell23_1821388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_1821388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821388 prefixEnd_1821388 := by exact prefixLift 1821388
  have htrace : WordTrace (prefixWord ++ tailWord_1821388) baseStart_1821388 baseEnd_1821388 := by
    simpa [prefixWord, tailWord_1821388, baseEnd_1821388] using wordTrace_append hprefix tailTrace_1821388
  have hstable : (prefixWord ++ tailWord_1821388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821388).length < 2 ^ (prefixWord ++ tailWord_1821388).sum := by decide
  have hdescent : baseEnd_1821388 < baseStart_1821388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821401 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 1, 7]
def baseStart_1821401 : Nat := 118140960795 + 1821401 * 2 ^ 59
def prefixEnd_1821401 : Nat := 4983230072969 + 3 ^ 40 * 1821401 * 2
def baseEnd_1821401 : Nat := 311751392526644497970345

theorem tailTrace_1821401 : CollatzResearch.WordTrace tailWord_1821401 prefixEnd_1821401 311751392526644497970345 := by
  unfold tailWord_1821401
  simp only [CollatzResearch.WordTrace]
  refine ⟨66431952074382722370320057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44287968049588481580213371 66431952074382722370320057)
  ·
    refine ⟨49823964055787041777740043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66431952074382722370320057 49823964055787041777740043)
    ·
      refine ⟨74735946083680562666610065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49823964055787041777740043 74735946083680562666610065)
      ·
        refine ⟨56051959562760421999957549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74735946083680562666610065 56051959562760421999957549)
        ·
          refine ⟨21019484836035158249984081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56051959562760421999957549 21019484836035158249984081)
          ·
            refine ⟨15764613627026368687488061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21019484836035158249984081 15764613627026368687488061)
            ·
              refine ⟨5911730110134888257808023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15764613627026368687488061 5911730110134888257808023)
              ·
                refine ⟨8867595165202332386712035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911730110134888257808023 8867595165202332386712035)
                ·
                  refine ⟨13301392747803498580068053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8867595165202332386712035 13301392747803498580068053)
                  ·
                    refine ⟨311751392526644497970345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13301392747803498580068053 311751392526644497970345)
                    ·
                      rfl

theorem cell23_1821401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_1821401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821401 prefixEnd_1821401 := by exact prefixLift 1821401
  have htrace : WordTrace (prefixWord ++ tailWord_1821401) baseStart_1821401 baseEnd_1821401 := by
    simpa [prefixWord, tailWord_1821401, baseEnd_1821401] using wordTrace_append hprefix tailTrace_1821401
  have hstable : (prefixWord ++ tailWord_1821401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821401).length < 2 ^ (prefixWord ++ tailWord_1821401).sum := by decide
  have hdescent : baseEnd_1821401 < baseStart_1821401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821416 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_1821416 : Nat := 118140960795 + 1821416 * 2 ^ 59
def prefixEnd_1821416 : Nat := 4983230072969 + 3 ^ 40 * 1821416 * 2
def baseEnd_1821416 : Nat := 935261879789750935223467

theorem tailTrace_1821416 : CollatzResearch.WordTrace tailWord_1821416 prefixEnd_1821416 935261879789750935223467 := by
  unfold tailWord_1821416
  simp only [CollatzResearch.WordTrace]
  refine ⟨33216249584664189966058051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44288332779552253288077401 33216249584664189966058051)
  ·
    refine ⟨49824374376996284949087077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33216249584664189966058051 49824374376996284949087077)
    ·
      refine ⟨9342070195686803427953827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49824374376996284949087077 9342070195686803427953827)
      ·
        refine ⟨14013105293530205141930741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9342070195686803427953827 14013105293530205141930741)
        ·
          refine ⟨1313728621268456732056007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14013105293530205141930741 1313728621268456732056007)
          ·
            refine ⟨1970592931902685098084011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313728621268456732056007 1970592931902685098084011)
            ·
              refine ⟨2955889397854027647126017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970592931902685098084011 2955889397854027647126017)
              ·
                refine ⟨2216917048390520735344513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955889397854027647126017 2216917048390520735344513)
                ·
                  refine ⟨1662687786292890551508385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2216917048390520735344513 1662687786292890551508385)
                  ·
                    refine ⟨1247015839719667913631289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662687786292890551508385 1247015839719667913631289)
                    ·
                      refine ⟨935261879789750935223467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247015839719667913631289 935261879789750935223467)
                      ·
                        rfl

theorem cell23_1821416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_1821416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821416 prefixEnd_1821416 := by exact prefixLift 1821416
  have htrace : WordTrace (prefixWord ++ tailWord_1821416) baseStart_1821416 baseEnd_1821416 := by
    simpa [prefixWord, tailWord_1821416, baseEnd_1821416] using wordTrace_append hprefix tailTrace_1821416
  have hstable : (prefixWord ++ tailWord_1821416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821416).length < 2 ^ (prefixWord ++ tailWord_1821416).sum := by decide
  have hdescent : baseEnd_1821416 < baseStart_1821416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821451 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 4]
def baseStart_1821451 : Nat := 118140960795 + 1821451 * 2 ^ 59
def prefixEnd_1821451 : Nat := 4983230072969 + 3 ^ 40 * 1821451 * 2
def baseEnd_1821451 : Nat := 935279851612658298285805

theorem tailTrace_1821451 : CollatzResearch.WordTrace tailWord_1821451 prefixEnd_1821451 935279851612658298285805 := by
  unfold tailWord_1821451
  simp only [CollatzResearch.WordTrace]
  refine ⟨66433775724201580909640207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44289183816134387273093471 66433775724201580909640207)
  ·
    refine ⟨99650663586302371364460311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66433775724201580909640207 99650663586302371364460311)
    ·
      refine ⟨149475995379453557046690467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99650663586302371364460311 149475995379453557046690467)
      ·
        refine ⟨224213993069180335570035701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149475995379453557046690467 224213993069180335570035701)
        ·
          refine ⟨21020061850235656459690847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224213993069180335570035701 21020061850235656459690847)
          ·
            refine ⟨31530092775353484689536271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21020061850235656459690847 31530092775353484689536271)
            ·
              refine ⟨47295139163030227034304407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31530092775353484689536271 47295139163030227034304407)
              ·
                refine ⟨70942708744545340551456611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47295139163030227034304407 70942708744545340551456611)
                ·
                  refine ⟨106414063116818010827184917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70942708744545340551456611 106414063116818010827184917)
                  ·
                    refine ⟨4988159208600844257524293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106414063116818010827184917 4988159208600844257524293)
                    ·
                      refine ⟨935279851612658298285805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4988159208600844257524293 935279851612658298285805)
                      ·
                        rfl

theorem cell23_1821451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 4].length) (baseStart_1821451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821451 prefixEnd_1821451 := by exact prefixLift 1821451
  have htrace : WordTrace (prefixWord ++ tailWord_1821451) baseStart_1821451 baseEnd_1821451 := by
    simpa [prefixWord, tailWord_1821451, baseEnd_1821451] using wordTrace_append hprefix tailTrace_1821451
  have hstable : (prefixWord ++ tailWord_1821451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821451).length < 2 ^ (prefixWord ++ tailWord_1821451).sum := by decide
  have hdescent : baseEnd_1821451 < baseStart_1821451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821461 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 10]
def baseStart_1821461 : Nat := 118140960795 + 1821461 * 2 ^ 59
def prefixEnd_1821461 : Nat := 4983230072969 + 3 ^ 40 * 1821461 * 2
def baseEnd_1821461 : Nat := 103920554046578139906751

theorem tailTrace_1821461 : CollatzResearch.WordTrace tailWord_1821461 prefixEnd_1821461 103920554046578139906751 := by
  unfold tailWord_1821461
  simp only [CollatzResearch.WordTrace]
  refine ⟨66434140454165352617504237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44289426969443568411669491 66434140454165352617504237)
  ·
    refine ⟨24912802670312007231564089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66434140454165352617504237 24912802670312007231564089)
    ·
      refine ⟨18684602002734005423673067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24912802670312007231564089 18684602002734005423673067)
      ·
        refine ⟨28026903004101008135509601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18684602002734005423673067 28026903004101008135509601)
        ·
          refine ⟨21020177253075756101632201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28026903004101008135509601 21020177253075756101632201)
          ·
            refine ⟨15765132939806817076224151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21020177253075756101632201 15765132939806817076224151)
            ·
              refine ⟨23647699409710225614336227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15765132939806817076224151 23647699409710225614336227)
              ·
                refine ⟨35471549114565338421504341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23647699409710225614336227 35471549114565338421504341)
                ·
                  refine ⟨103920554046578139906751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 35471549114565338421504341 103920554046578139906751)
                  ·
                    rfl

theorem cell23_1821461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_1821461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821461 prefixEnd_1821461 := by exact prefixLift 1821461
  have htrace : WordTrace (prefixWord ++ tailWord_1821461) baseStart_1821461 baseEnd_1821461 := by
    simpa [prefixWord, tailWord_1821461, baseEnd_1821461] using wordTrace_append hprefix tailTrace_1821461
  have hstable : (prefixWord ++ tailWord_1821461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821461).length < 2 ^ (prefixWord ++ tailWord_1821461).sum := by decide
  have hdescent : baseEnd_1821461 < baseStart_1821461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821465 : List Nat := [1, 2, 1, 2, 1, 1, 1, 9, 1, 4]
def baseStart_1821465 : Nat := 118140960795 + 1821465 * 2 ^ 59
def prefixEnd_1821465 : Nat := 4983230072969 + 3 ^ 40 * 1821465 * 2
def baseEnd_1821465 : Nat := 311762346780607081170247

theorem tailTrace_1821465 : CollatzResearch.WordTrace tailWord_1821465 prefixEnd_1821465 311762346780607081170247 := by
  unfold tailWord_1821465
  simp only [CollatzResearch.WordTrace]
  refine ⟨66434286346150861300649849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44289524230767240867099899 66434286346150861300649849)
  ·
    refine ⟨49825714759613145975487387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66434286346150861300649849 49825714759613145975487387)
    ·
      refine ⟨74738572139419718963231081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49825714759613145975487387 74738572139419718963231081)
      ·
        refine ⟨56053929104564789222423311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74738572139419718963231081 56053929104564789222423311)
        ·
          refine ⟨84080893656847183833634967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56053929104564789222423311 84080893656847183833634967)
          ·
            refine ⟨126121340485270775750452451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84080893656847183833634967 126121340485270775750452451)
            ·
              refine ⟨189182010727906163625678677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126121340485270775750452451 189182010727906163625678677)
              ·
                refine ⟨1108488344108825177494211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 189182010727906163625678677 1108488344108825177494211)
                ·
                  refine ⟨1662732516163237766241317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108488344108825177494211 1662732516163237766241317)
                  ·
                    refine ⟨311762346780607081170247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1662732516163237766241317 311762346780607081170247)
                    ·
                      rfl

theorem cell23_1821465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 4].length) (baseStart_1821465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821465 prefixEnd_1821465 := by exact prefixLift 1821465
  have htrace : WordTrace (prefixWord ++ tailWord_1821465) baseStart_1821465 baseEnd_1821465 := by
    simpa [prefixWord, tailWord_1821465, baseEnd_1821465] using wordTrace_append hprefix tailTrace_1821465
  have hstable : (prefixWord ++ tailWord_1821465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821465).length < 2 ^ (prefixWord ++ tailWord_1821465).sum := by decide
  have hdescent : baseEnd_1821465 < baseStart_1821465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821539 : List Nat := [1, 1, 1, 5, 3, 2, 1, 4, 1, 1, 3]
def baseStart_1821539 : Nat := 118140960795 + 1821539 * 2 ^ 59
def prefixEnd_1821539 : Nat := 4983230072969 + 3 ^ 40 * 1821539 * 2
def baseEnd_1821539 : Nat := 935325037910253953985401

theorem tailTrace_1821539 : CollatzResearch.WordTrace tailWord_1821539 prefixEnd_1821539 935325037910253953985401 := by
  unfold tailWord_1821539
  simp only [CollatzResearch.WordTrace]
  refine ⟨66436985347882771938843671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44291323565255181292562447 66436985347882771938843671)
  ·
    refine ⟨99655478021824157908265507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66436985347882771938843671 99655478021824157908265507)
    ·
      refine ⟨149483217032736236862398261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99655478021824157908265507 149483217032736236862398261)
      ·
        refine ⟨14014051596819022205849837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149483217032736236862398261 14014051596819022205849837)
        ·
          refine ⟨5255269348807133327193689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14014051596819022205849837 5255269348807133327193689)
          ·
            refine ⟨3941452011605349995395267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5255269348807133327193689 3941452011605349995395267)
            ·
              refine ⟨5912178017408024993092901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941452011605349995395267 5912178017408024993092901)
              ·
                refine ⟨1108533378264004686204919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5912178017408024993092901 1108533378264004686204919)
                ·
                  refine ⟨1662800067396007029307379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108533378264004686204919 1662800067396007029307379)
                  ·
                    refine ⟨2494200101094010543961069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1662800067396007029307379 2494200101094010543961069)
                    ·
                      refine ⟨935325037910253953985401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2494200101094010543961069 935325037910253953985401)
                      ·
                        rfl

theorem cell23_1821539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_1821539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821539 prefixEnd_1821539 := by exact prefixLift 1821539
  have htrace : WordTrace (prefixWord ++ tailWord_1821539) baseStart_1821539 baseEnd_1821539 := by
    simpa [prefixWord, tailWord_1821539, baseEnd_1821539] using wordTrace_append hprefix tailTrace_1821539
  have hstable : (prefixWord ++ tailWord_1821539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821539).length < 2 ^ (prefixWord ++ tailWord_1821539).sum := by decide
  have hdescent : baseEnd_1821539 < baseStart_1821539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821548 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_1821548 : Nat := 118140960795 + 1821548 * 2 ^ 59
def prefixEnd_1821548 : Nat := 4983230072969 + 3 ^ 40 * 1821548 * 2
def baseEnd_1821548 : Nat := 935329659236144418772859

theorem tailTrace_1821548 : CollatzResearch.WordTrace tailWord_1821548 prefixEnd_1821548 935329659236144418772859 := by
  unfold tailWord_1821548
  simp only [CollatzResearch.WordTrace]
  refine ⟨33218656802425083237960649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44291542403233444317280865 33218656802425083237960649)
  ·
    refine ⟨24913992601818812428470487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33218656802425083237960649 24913992601818812428470487)
    ·
      refine ⟨37370988902728218642705731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24913992601818812428470487 37370988902728218642705731)
      ·
        refine ⟨56056483354092327964058597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37370988902728218642705731 56056483354092327964058597)
        ·
          refine ⟨10510590628892311493260987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56056483354092327964058597 10510590628892311493260987)
          ·
            refine ⟨15765885943338467239891481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10510590628892311493260987 15765885943338467239891481)
            ·
              refine ⟨11824414457503850429918611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15765885943338467239891481 11824414457503850429918611)
              ·
                refine ⟨17736621686255775644877917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11824414457503850429918611 17736621686255775644877917)
                ·
                  refine ⟨6651233132345915866829219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17736621686255775644877917 6651233132345915866829219)
                  ·
                    refine ⟨9976849698518873800243829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6651233132345915866829219 9976849698518873800243829)
                    ·
                      refine ⟨935329659236144418772859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9976849698518873800243829 935329659236144418772859)
                      ·
                        rfl

theorem cell23_1821548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_1821548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821548 prefixEnd_1821548 := by exact prefixLift 1821548
  have htrace : WordTrace (prefixWord ++ tailWord_1821548) baseStart_1821548 baseEnd_1821548 := by
    simpa [prefixWord, tailWord_1821548, baseEnd_1821548] using wordTrace_append hprefix tailTrace_1821548
  have hstable : (prefixWord ++ tailWord_1821548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821548).length < 2 ^ (prefixWord ++ tailWord_1821548).sum := by decide
  have hdescent : baseEnd_1821548 < baseStart_1821548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821555 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 2, 4]
def baseStart_1821555 : Nat := 118140960795 + 1821555 * 2 ^ 59
def prefixEnd_1821555 : Nat := 4983230072969 + 3 ^ 40 * 1821555 * 2
def baseEnd_1821555 : Nat := 311777751200241963795109

theorem tailTrace_1821555 : CollatzResearch.WordTrace tailWord_1821555 prefixEnd_1821555 311777751200241963795109 := by
  unfold tailWord_1821555
  simp only [CollatzResearch.WordTrace]
  refine ⟨66437568915824806671426119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44291712610549871114284079 66437568915824806671426119)
  ·
    refine ⟨99656353373737210007139179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66437568915824806671426119 99656353373737210007139179)
    ·
      refine ⟨149484530060605815010708769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99656353373737210007139179 149484530060605815010708769)
      ·
        refine ⟨112113397545454361258031577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149484530060605815010708769 112113397545454361258031577)
        ·
          refine ⟨84085048159090770943523683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112113397545454361258031577 84085048159090770943523683)
          ·
            refine ⟨126127572238636156415285525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84085048159090770943523683 126127572238636156415285525)
            ·
              refine ⟨5912229948686069831966509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126127572238636156415285525 5912229948686069831966509)
              ·
                refine ⟨2217086230757276186987441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5912229948686069831966509 2217086230757276186987441)
                ·
                  refine ⟨1662814673067957140240581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2217086230757276186987441 1662814673067957140240581)
                  ·
                    refine ⟨311777751200241963795109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1662814673067957140240581 311777751200241963795109)
                    ·
                      rfl

theorem cell23_1821555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 4].length) (baseStart_1821555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821555 prefixEnd_1821555 := by exact prefixLift 1821555
  have htrace : WordTrace (prefixWord ++ tailWord_1821555) baseStart_1821555 baseEnd_1821555 := by
    simpa [prefixWord, tailWord_1821555, baseEnd_1821555] using wordTrace_append hprefix tailTrace_1821555
  have hstable : (prefixWord ++ tailWord_1821555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821555).length < 2 ^ (prefixWord ++ tailWord_1821555).sum := by decide
  have hdescent : baseEnd_1821555 < baseStart_1821555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821565 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_1821565 : Nat := 118140960795 + 1821565 * 2 ^ 59
def prefixEnd_1821565 : Nat := 4983230072969 + 3 ^ 40 * 1821565 * 2
def baseEnd_1821565 : Nat := 935338388407270852260281

theorem tailTrace_1821565 : CollatzResearch.WordTrace tailWord_1821565 prefixEnd_1821565 935338388407270852260281 := by
  unfold tailWord_1821565
  simp only [CollatzResearch.WordTrace]
  refine ⟨66437933645788578379290149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44291955763859052252860099 66437933645788578379290149)
  ·
    refine ⟨12457112558585358446116903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66437933645788578379290149 12457112558585358446116903)
    ·
      refine ⟨18685668837878037669175355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12457112558585358446116903 18685668837878037669175355)
      ·
        refine ⟨28028503256817056503763033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18685668837878037669175355 28028503256817056503763033)
        ·
          refine ⟨21021377442612792377822275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28028503256817056503763033 21021377442612792377822275)
          ·
            refine ⟨31532066163919188566733413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21021377442612792377822275 31532066163919188566733413)
            ·
              refine ⟨5912262405734847856262515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31532066163919188566733413 5912262405734847856262515)
              ·
                refine ⟨8868393608602271784393773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5912262405734847856262515 8868393608602271784393773)
                ·
                  refine ⟨3325647603225851919147665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8868393608602271784393773 3325647603225851919147665)
                  ·
                    refine ⟨2494235702419388939360749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3325647603225851919147665 2494235702419388939360749)
                    ·
                      refine ⟨935338388407270852260281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2494235702419388939360749 935338388407270852260281)
                      ·
                        rfl

theorem cell23_1821565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_1821565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821565 prefixEnd_1821565 := by exact prefixLift 1821565
  have htrace : WordTrace (prefixWord ++ tailWord_1821565) baseStart_1821565 baseEnd_1821565 := by
    simpa [prefixWord, tailWord_1821565, baseEnd_1821565] using wordTrace_append hprefix tailTrace_1821565
  have hstable : (prefixWord ++ tailWord_1821565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821565).length < 2 ^ (prefixWord ++ tailWord_1821565).sum := by decide
  have hdescent : baseEnd_1821565 < baseStart_1821565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821575 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_1821575 : Nat := 118140960795 + 1821575 * 2 ^ 59
def prefixEnd_1821575 : Nat := 4983230072969 + 3 ^ 40 * 1821575 * 2
def baseEnd_1821575 : Nat := 935343523213815813135235

theorem tailTrace_1821575 : CollatzResearch.WordTrace tailWord_1821575 prefixEnd_1821575 935343523213815813135235 := by
  unfold tailWord_1821575
  simp only [CollatzResearch.WordTrace]
  refine ⟨66438298375752350087154179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44292198917168233391436119 66438298375752350087154179)
  ·
    refine ⟨99657447563628525130731269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66438298375752350087154179 99657447563628525130731269)
    ·
      refine ⟨18685771418180348462012113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99657447563628525130731269 18685771418180348462012113)
      ·
        refine ⟨14014328563635261346509085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18685771418180348462012113 14014328563635261346509085)
        ·
          refine ⟨5255373211363223004940907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14014328563635261346509085 5255373211363223004940907)
          ·
            refine ⟨7883059817044834507411361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5255373211363223004940907 7883059817044834507411361)
            ·
              refine ⟨5912294862783625880558521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7883059817044834507411361 5912294862783625880558521)
              ·
                refine ⟨4434221147087719410418891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912294862783625880558521 4434221147087719410418891)
                ·
                  refine ⟨6651331720631579115628337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434221147087719410418891 6651331720631579115628337)
                  ·
                    refine ⟨4988498790473684336721253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6651331720631579115628337 4988498790473684336721253)
                    ·
                      refine ⟨935343523213815813135235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4988498790473684336721253 935343523213815813135235)
                      ·
                        rfl

theorem cell23_1821575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_1821575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821575 prefixEnd_1821575 := by exact prefixLift 1821575
  have htrace : WordTrace (prefixWord ++ tailWord_1821575) baseStart_1821575 baseEnd_1821575 := by
    simpa [prefixWord, tailWord_1821575, baseEnd_1821575] using wordTrace_append hprefix tailTrace_1821575
  have hstable : (prefixWord ++ tailWord_1821575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821575).length < 2 ^ (prefixWord ++ tailWord_1821575).sum := by decide
  have hdescent : baseEnd_1821575 < baseStart_1821575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821579 : List Nat := [1, 1, 1, 1, 4, 2, 3, 5, 1, 2, 2]
def baseStart_1821579 : Nat := 118140960795 + 1821579 * 2 ^ 59
def prefixEnd_1821579 : Nat := 4983230072969 + 3 ^ 40 * 1821579 * 2
def baseEnd_1821579 : Nat := 935345577136433797485217

theorem tailTrace_1821579 : CollatzResearch.WordTrace tailWord_1821579 prefixEnd_1821579 935345577136433797485217 := by
  unfold tailWord_1821579
  simp only [CollatzResearch.WordTrace]
  refine ⟨66438444267737858770299791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44292296178491905846866527 66438444267737858770299791)
  ·
    refine ⟨99657666401606788155449687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66438444267737858770299791 99657666401606788155449687)
    ·
      refine ⟨149486499602410182233174531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99657666401606788155449687 149486499602410182233174531)
      ·
        refine ⟨224229749403615273349761797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149486499602410182233174531 224229749403615273349761797)
        ·
          refine ⟨42043078013177863753080337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224229749403615273349761797 42043078013177863753080337)
          ·
            refine ⟨31532308509883397814810253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42043078013177863753080337 31532308509883397814810253)
            ·
              refine ⟨11824615691206274180553845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31532308509883397814810253 11824615691206274180553845)
              ·
                refine ⟨1108557721050588204426923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11824615691206274180553845 1108557721050588204426923)
                ·
                  refine ⟨1662836581575882306640385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108557721050588204426923 1662836581575882306640385)
                  ·
                    refine ⟨1247127436181911729980289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662836581575882306640385 1247127436181911729980289)
                    ·
                      refine ⟨935345577136433797485217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247127436181911729980289 935345577136433797485217)
                      ·
                        rfl

theorem cell23_1821579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 2, 2].length) (baseStart_1821579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821579 prefixEnd_1821579 := by exact prefixLift 1821579
  have htrace : WordTrace (prefixWord ++ tailWord_1821579) baseStart_1821579 baseEnd_1821579 := by
    simpa [prefixWord, tailWord_1821579, baseEnd_1821579] using wordTrace_append hprefix tailTrace_1821579
  have hstable : (prefixWord ++ tailWord_1821579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821579).length < 2 ^ (prefixWord ++ tailWord_1821579).sum := by decide
  have hdescent : baseEnd_1821579 < baseStart_1821579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821596 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1821596 : Nat := 118140960795 + 1821596 * 2 ^ 59
def prefixEnd_1821596 : Nat := 4983230072969 + 3 ^ 40 * 1821596 * 2
def baseEnd_1821596 : Nat := 935354306307560230972639

theorem tailTrace_1821596 : CollatzResearch.WordTrace tailWord_1821596 prefixEnd_1821596 935354306307560230972639 := by
  unfold tailWord_1821596
  simp only [CollatzResearch.WordTrace]
  refine ⟨33219532154338135336834321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44292709539117513782445761 33219532154338135336834321)
  ·
    refine ⟨24914649115753601502625741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33219532154338135336834321 24914649115753601502625741)
    ·
      refine ⟨9342993418407600563484653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24914649115753601502625741 9342993418407600563484653)
      ·
        refine ⟨3503622531902850211306745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9342993418407600563484653 3503622531902850211306745)
        ·
          refine ⟨2627716898927137658480059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3503622531902850211306745 2627716898927137658480059)
          ·
            refine ⟨3941575348390706487720089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627716898927137658480059 3941575348390706487720089)
            ·
              refine ⟨2956181511293029865790067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941575348390706487720089 2956181511293029865790067)
              ·
                refine ⟨4434272266939544798685101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956181511293029865790067 4434272266939544798685101)
                ·
                  refine ⟨1662852100102329299506913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4434272266939544798685101 1662852100102329299506913)
                  ·
                    refine ⟨1247139075076746974630185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662852100102329299506913 1247139075076746974630185)
                    ·
                      refine ⟨935354306307560230972639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247139075076746974630185 935354306307560230972639)
                      ·
                        rfl

theorem cell23_1821596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1821596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821596 prefixEnd_1821596 := by exact prefixLift 1821596
  have htrace : WordTrace (prefixWord ++ tailWord_1821596) baseStart_1821596 baseEnd_1821596 := by
    simpa [prefixWord, tailWord_1821596, baseEnd_1821596] using wordTrace_append hprefix tailTrace_1821596
  have hstable : (prefixWord ++ tailWord_1821596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821596).length < 2 ^ (prefixWord ++ tailWord_1821596).sum := by decide
  have hdescent : baseEnd_1821596 < baseStart_1821596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821663 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 2, 1, 3]
def baseStart_1821663 : Nat := 118140960795 + 1821663 * 2 ^ 59
def prefixEnd_1821663 : Nat := 4983230072969 + 3 ^ 40 * 1821663 * 2
def baseEnd_1821663 : Nat := 935388709511411468834831

theorem tailTrace_1821663 : CollatzResearch.WordTrace tailWord_1821663 prefixEnd_1821663 935388709511411468834831 := by
  unfold tailWord_1821663
  simp only [CollatzResearch.WordTrace]
  refine ⟨66441507999433541116357643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44294338666289027410905095 66441507999433541116357643)
  ·
    refine ⟨99662261999150311674536465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66441507999433541116357643 99662261999150311674536465)
    ·
      refine ⟨74746696499362733755902349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99662261999150311674536465 74746696499362733755902349)
      ·
        refine ⟨28030011187261025158463381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74746696499362733755902349 28030011187261025158463381)
        ·
          refine ⟨1313906774402860554302971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28030011187261025158463381 1313906774402860554302971)
          ·
            refine ⟨1970860161604290831454457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313906774402860554302971 1970860161604290831454457)
            ·
              refine ⟨1478145121203218123590843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970860161604290831454457 1478145121203218123590843)
              ·
                refine ⟨2217217681804827185386265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478145121203218123590843 2217217681804827185386265)
                ·
                  refine ⟨1662913261353620389039699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2217217681804827185386265 1662913261353620389039699)
                  ·
                    refine ⟨2494369892030430583559549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1662913261353620389039699 2494369892030430583559549)
                    ·
                      refine ⟨935388709511411468834831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2494369892030430583559549 935388709511411468834831)
                      ·
                        rfl

theorem cell23_1821663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_1821663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821663 prefixEnd_1821663 := by exact prefixLift 1821663
  have htrace : WordTrace (prefixWord ++ tailWord_1821663) baseStart_1821663 baseEnd_1821663 := by
    simpa [prefixWord, tailWord_1821663, baseEnd_1821663] using wordTrace_append hprefix tailTrace_1821663
  have hstable : (prefixWord ++ tailWord_1821663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821663).length < 2 ^ (prefixWord ++ tailWord_1821663).sum := by decide
  have hdescent : baseEnd_1821663 < baseStart_1821663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821742 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1821742 : Nat := 118140960795 + 1821742 * 2 ^ 59
def prefixEnd_1821742 : Nat := 4983230072969 + 3 ^ 40 * 1821742 * 2
def baseEnd_1821742 : Nat := 935429274483116659746967

theorem tailTrace_1821742 : CollatzResearch.WordTrace tailWord_1821742 prefixEnd_1821742 935429274483116659746967 := by
  unfold tailWord_1821742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8305548670768417201060435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44296259577431558405655653 8305548670768417201060435)
  ·
    refine ⟨12458323006152625801590653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8305548670768417201060435 12458323006152625801590653)
    ·
      refine ⟨4671871127307234675596495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12458323006152625801590653 4671871127307234675596495)
      ·
        refine ⟨7007806690960852013394743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671871127307234675596495 7007806690960852013394743)
        ·
          refine ⟨10511710036441278020092115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7007806690960852013394743 10511710036441278020092115)
          ·
            refine ⟨15767565054661917030138173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511710036441278020092115 15767565054661917030138173)
            ·
              refine ⟨5912836895498218886301815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15767565054661917030138173 5912836895498218886301815)
              ·
                refine ⟨8869255343247328329452723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5912836895498218886301815 8869255343247328329452723)
                ·
                  refine ⟨13303883014870992494179085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8869255343247328329452723 13303883014870992494179085)
                  ·
                    refine ⟨4988956130576622185317157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13303883014870992494179085 4988956130576622185317157)
                    ·
                      refine ⟨935429274483116659746967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4988956130576622185317157 935429274483116659746967)
                      ·
                        rfl

theorem cell23_1821742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1821742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821742 prefixEnd_1821742 := by exact prefixLift 1821742
  have htrace : WordTrace (prefixWord ++ tailWord_1821742) baseStart_1821742 baseEnd_1821742 := by
    simpa [prefixWord, tailWord_1821742, baseEnd_1821742] using wordTrace_append hprefix tailTrace_1821742
  have hstable : (prefixWord ++ tailWord_1821742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821742).length < 2 ^ (prefixWord ++ tailWord_1821742).sum := by decide
  have hdescent : baseEnd_1821742 < baseStart_1821742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821775 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 3]
def baseStart_1821775 : Nat := 118140960795 + 1821775 * 2 ^ 59
def prefixEnd_1821775 : Nat := 4983230072969 + 3 ^ 40 * 1821775 * 2
def baseEnd_1821775 : Nat := 935446219344715030634315

theorem tailTrace_1821775 : CollatzResearch.WordTrace tailWord_1821775 prefixEnd_1821775 935446219344715030634315 := by
  unfold tailWord_1821775
  simp only [CollatzResearch.WordTrace]
  refine ⟨66445592975027784244434779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44297061983351856162956519 66445592975027784244434779)
  ·
    refine ⟨99668389462541676366652169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66445592975027784244434779 99668389462541676366652169)
    ·
      refine ⟨74751292096906257274989127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99668389462541676366652169 74751292096906257274989127)
      ·
        refine ⟨112126938145359385912483691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74751292096906257274989127 112126938145359385912483691)
        ·
          refine ⟨168190407218039078868725537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112126938145359385912483691 168190407218039078868725537)
          ·
            refine ⟨126142805413529309151544153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168190407218039078868725537 126142805413529309151544153)
            ·
              refine ⟨94607104060146981863658115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126142805413529309151544153 94607104060146981863658115)
              ·
                refine ⟨141910656090220472795487173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94607104060146981863658115 141910656090220472795487173)
                ·
                  refine ⟨26608248016916338649153845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141910656090220472795487173 26608248016916338649153845)
                  ·
                    refine ⟨2494523251585906748358173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26608248016916338649153845 2494523251585906748358173)
                    ·
                      refine ⟨935446219344715030634315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2494523251585906748358173 935446219344715030634315)
                      ·
                        rfl

theorem cell23_1821775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_1821775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821775 prefixEnd_1821775 := by exact prefixLift 1821775
  have htrace : WordTrace (prefixWord ++ tailWord_1821775) baseStart_1821775 baseEnd_1821775 := by
    simpa [prefixWord, tailWord_1821775, baseEnd_1821775] using wordTrace_append hprefix tailTrace_1821775
  have hstable : (prefixWord ++ tailWord_1821775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821775).length < 2 ^ (prefixWord ++ tailWord_1821775).sum := by decide
  have hdescent : baseEnd_1821775 < baseStart_1821775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821882 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_1821882 : Nat := 118140960795 + 1821882 * 2 ^ 59
def prefixEnd_1821882 : Nat := 4983230072969 + 3 ^ 40 * 1821882 * 2
def baseEnd_1821882 : Nat := 935501161774746111996323

theorem tailTrace_1821882 : CollatzResearch.WordTrace tailWord_1821882 prefixEnd_1821882 935501161774746111996323 := by
  unfold tailWord_1821882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16612373896410035379644975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44299663723760094345719933 16612373896410035379644975)
  ·
    refine ⟨24918560844615053069467463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16612373896410035379644975 24918560844615053069467463)
    ·
      refine ⟨37377841266922579604201195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24918560844615053069467463 37377841266922579604201195)
      ·
        refine ⟨56066761900383869406301793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37377841266922579604201195 56066761900383869406301793)
        ·
          refine ⟨42050071425287902054726345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56066761900383869406301793 42050071425287902054726345)
          ·
            refine ⟨31537553568965926541044759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42050071425287902054726345 31537553568965926541044759)
            ·
              refine ⟨47306330353448889811567139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31537553568965926541044759 47306330353448889811567139)
              ·
                refine ⟨70959495530173334717350709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47306330353448889811567139 70959495530173334717350709)
                ·
                  refine ⟨6652452705953750129751629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70959495530173334717350709 6652452705953750129751629)
                  ·
                    refine ⟨2494669764732656298656861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6652452705953750129751629 2494669764732656298656861)
                    ·
                      refine ⟨935501161774746111996323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2494669764732656298656861 935501161774746111996323)
                      ·
                        rfl

theorem cell23_1821882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_1821882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821882 prefixEnd_1821882 := by exact prefixLift 1821882
  have htrace : WordTrace (prefixWord ++ tailWord_1821882) baseStart_1821882 baseEnd_1821882 := by
    simpa [prefixWord, tailWord_1821882, baseEnd_1821882] using wordTrace_append hprefix tailTrace_1821882
  have hstable : (prefixWord ++ tailWord_1821882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821882).length < 2 ^ (prefixWord ++ tailWord_1821882).sum := by decide
  have hdescent : baseEnd_1821882 < baseStart_1821882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821889 : List Nat := [1, 2, 6, 1, 1, 1, 3, 8]
def baseStart_1821889 : Nat := 118140960795 + 1821889 * 2 ^ 59
def prefixEnd_1821889 : Nat := 4983230072969 + 3 ^ 40 * 1821889 * 2
def baseEnd_1821889 : Nat := 34648324301456577207733

theorem tailTrace_1821889 : CollatzResearch.WordTrace tailWord_1821889 prefixEnd_1821889 34648324301456577207733 := by
  unfold tailWord_1821889
  simp only [CollatzResearch.WordTrace]
  refine ⟨66449750896614781714084721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44299833931076521142723147 66449750896614781714084721)
  ·
    refine ⟨49837313172461086285563541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66449750896614781714084721 49837313172461086285563541)
    ·
      refine ⟨2336124054959113419635791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49837313172461086285563541 2336124054959113419635791)
      ·
        refine ⟨3504186082438670129453687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336124054959113419635791 3504186082438670129453687)
        ·
          refine ⟨5256279123658005194180531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504186082438670129453687 5256279123658005194180531)
          ·
            refine ⟨7884418685487007791270797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256279123658005194180531 7884418685487007791270797)
            ·
              refine ⟨2956657007057627921726549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7884418685487007791270797 2956657007057627921726549)
              ·
                refine ⟨34648324301456577207733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2956657007057627921726549 34648324301456577207733)
                ·
                  rfl

theorem cell23_1821889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 8].length) (baseStart_1821889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821889 prefixEnd_1821889 := by exact prefixLift 1821889
  have htrace : WordTrace (prefixWord ++ tailWord_1821889) baseStart_1821889 baseEnd_1821889 := by
    simpa [prefixWord, tailWord_1821889, baseEnd_1821889] using wordTrace_append hprefix tailTrace_1821889
  have hstable : (prefixWord ++ tailWord_1821889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821889).length < 2 ^ (prefixWord ++ tailWord_1821889).sum := by decide
  have hdescent : baseEnd_1821889 < baseStart_1821889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821917 : List Nat := [1, 4, 3, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1821917 : Nat := 118140960795 + 1821917 * 2 ^ 59
def prefixEnd_1821917 : Nat := 4983230072969 + 3 ^ 40 * 1821917 * 2
def baseEnd_1821917 : Nat := 935519133597653475058663

theorem tailTrace_1821917 : CollatzResearch.WordTrace tailWord_1821917 prefixEnd_1821917 935519133597653475058663 := by
  unfold tailWord_1821917
  simp only [CollatzResearch.WordTrace]
  refine ⟨66450772140513342496104005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44300514760342228330736003 66450772140513342496104005)
  ·
    refine ⟨12459519776346251718019501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66450772140513342496104005 12459519776346251718019501)
    ·
      refine ⟨4672319916129844394257313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12459519776346251718019501 4672319916129844394257313)
      ·
        refine ⟨3504239937097383295692985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4672319916129844394257313 3504239937097383295692985)
        ·
          refine ⟨2628179952823037471769739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3504239937097383295692985 2628179952823037471769739)
          ·
            refine ⟨3942269929234556207654609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628179952823037471769739 3942269929234556207654609)
            ·
              refine ⟨2956702446925917155740957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942269929234556207654609 2956702446925917155740957)
              ·
                refine ⟨1108763417597218933402859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2956702446925917155740957 1108763417597218933402859)
                ·
                  refine ⟨1663145126395828400104289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108763417597218933402859 1663145126395828400104289)
                  ·
                    refine ⟨1247358844796871300078217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1663145126395828400104289 1247358844796871300078217)
                    ·
                      refine ⟨935519133597653475058663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247358844796871300078217 935519133597653475058663)
                      ·
                        rfl

theorem cell23_1821917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1821917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821917 prefixEnd_1821917 := by exact prefixLift 1821917
  have htrace : WordTrace (prefixWord ++ tailWord_1821917) baseStart_1821917 baseEnd_1821917 := by
    simpa [prefixWord, tailWord_1821917, baseEnd_1821917] using wordTrace_append hprefix tailTrace_1821917
  have hstable : (prefixWord ++ tailWord_1821917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821917).length < 2 ^ (prefixWord ++ tailWord_1821917).sum := by decide
  have hdescent : baseEnd_1821917 < baseStart_1821917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
