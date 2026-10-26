import V185TrunkScan23Chunk0888

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5261799 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 1, 5]
def baseStart_5261799 : Nat := 118140960795 + 5261799 * 2 ^ 59
def prefixEnd_5261799 : Nat := 4983230072969 + 3 ^ 40 * 5261799 * 2
def baseEnd_5261799 : Nat := 900610664782321306971311

theorem tailTrace_5261799 : CollatzResearch.WordTrace tailWord_5261799 prefixEnd_5261799 900610664782321306971311 := by
  unfold tailWord_5261799
  simp only [CollatzResearch.WordTrace]
  refine ⟨191913575864408341569628451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127942383909605561046418967 191913575864408341569628451)
  ·
    refine ⟨287870363796612512354442677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191913575864408341569628451 287870363796612512354442677)
    ·
      refine ⟨26987846605932423033229001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 287870363796612512354442677 26987846605932423033229001)
      ·
        refine ⟨20240884954449317274921751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26987846605932423033229001 20240884954449317274921751)
        ·
          refine ⟨30361327431673975912382627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20240884954449317274921751 30361327431673975912382627)
          ·
            refine ⟨45541991147510963868573941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30361327431673975912382627 45541991147510963868573941)
            ·
              refine ⟨4269561670079152862678807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45541991147510963868573941 4269561670079152862678807)
              ·
                refine ⟨6404342505118729294018211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269561670079152862678807 6404342505118729294018211)
                ·
                  refine ⟨9606513757678093941027317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6404342505118729294018211 9606513757678093941027317)
                  ·
                    refine ⟨900610664782321306971311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9606513757678093941027317 900610664782321306971311)
                    ·
                      rfl

theorem cell23_5261799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_5261799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261799 prefixEnd_5261799 := by exact prefixLift 5261799
  have htrace : WordTrace (prefixWord ++ tailWord_5261799) baseStart_5261799 baseEnd_5261799 := by
    simpa [prefixWord, tailWord_5261799, baseEnd_5261799] using wordTrace_append hprefix tailTrace_5261799
  have hstable : (prefixWord ++ tailWord_5261799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261799).length < 2 ^ (prefixWord ++ tailWord_5261799).sum := by decide
  have hdescent : baseEnd_5261799 < baseStart_5261799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261830 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_5261830 : Nat := 118140960795 + 5261830 * 2 ^ 59
def prefixEnd_5261830 : Nat := 4983230072969 + 3 ^ 40 * 5261830 * 2
def baseEnd_5261830 : Nat := 2701847912247253299626291

theorem tailTrace_5261830 : CollatzResearch.WordTrace tailWord_5261830 prefixEnd_5261830 2701847912247253299626291 := by
  unfold tailWord_5261830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5997334578978001058250217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127943137684864022576004629 5997334578978001058250217)
  ·
    refine ⟨4498000934233500793687663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5997334578978001058250217 4498000934233500793687663)
    ·
      refine ⟨6747001401350251190531495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4498000934233500793687663 6747001401350251190531495)
      ·
        refine ⟨10120502102025376785797243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6747001401350251190531495 10120502102025376785797243)
        ·
          refine ⟨15180753153038065178695865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10120502102025376785797243 15180753153038065178695865)
          ·
            refine ⟨11385564864778548884021899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15180753153038065178695865 11385564864778548884021899)
            ·
              refine ⟨17078347297167823326032849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11385564864778548884021899 17078347297167823326032849)
              ·
                refine ⟨12808760472875867494524637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17078347297167823326032849 12808760472875867494524637)
                ·
                  refine ⟨4803285177328450310446739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12808760472875867494524637 4803285177328450310446739)
                  ·
                    refine ⟨7204927765992675465670109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4803285177328450310446739 7204927765992675465670109)
                    ·
                      refine ⟨2701847912247253299626291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7204927765992675465670109 2701847912247253299626291)
                      ·
                        rfl

theorem cell23_5261830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_5261830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261830 prefixEnd_5261830 := by exact prefixLift 5261830
  have htrace : WordTrace (prefixWord ++ tailWord_5261830) baseStart_5261830 baseEnd_5261830 := by
    simpa [prefixWord, tailWord_5261830, baseEnd_5261830] using wordTrace_append hprefix tailTrace_5261830
  have hstable : (prefixWord ++ tailWord_5261830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261830).length < 2 ^ (prefixWord ++ tailWord_5261830).sum := by decide
  have hdescent : baseEnd_5261830 < baseStart_5261830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261836 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 3, 2, 2]
def baseStart_5261836 : Nat := 118140960795 + 5261836 * 2 ^ 59
def prefixEnd_5261836 : Nat := 4983230072969 + 3 ^ 40 * 5261836 * 2
def baseEnd_5261836 : Nat := 2701850993131180276151263

theorem tailTrace_5261836 : CollatzResearch.WordTrace tailWord_5261836 prefixEnd_5261836 2701850993131180276151263 := by
  unfold tailWord_5261836
  simp only [CollatzResearch.WordTrace]
  refine ⟨95957462682637148444362681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127943283576849531259150241 95957462682637148444362681)
  ·
    refine ⟨71968097011977861333272011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95957462682637148444362681 71968097011977861333272011)
    ·
      refine ⟨107952145517966791999908017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71968097011977861333272011 107952145517966791999908017)
      ·
        refine ⟨80964109138475093999931013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107952145517966791999908017 80964109138475093999931013)
        ·
          refine ⟨15180770463464080124987065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80964109138475093999931013 15180770463464080124987065)
          ·
            refine ⟨11385577847598060093740299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15180770463464080124987065 11385577847598060093740299)
            ·
              refine ⟨17078366771397090140610449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11385577847598060093740299 17078366771397090140610449)
              ·
                refine ⟨12808775078547817605457837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17078366771397090140610449 12808775078547817605457837)
                ·
                  refine ⟨4803290654455431602046689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12808775078547817605457837 4803290654455431602046689)
                  ·
                    refine ⟨3602467990841573701535017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803290654455431602046689 3602467990841573701535017)
                    ·
                      refine ⟨2701850993131180276151263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602467990841573701535017 2701850993131180276151263)
                      ·
                        rfl

theorem cell23_5261836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_5261836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261836 prefixEnd_5261836 := by exact prefixLift 5261836
  have htrace : WordTrace (prefixWord ++ tailWord_5261836) baseStart_5261836 baseEnd_5261836 := by
    simpa [prefixWord, tailWord_5261836, baseEnd_5261836] using wordTrace_append hprefix tailTrace_5261836
  have hstable : (prefixWord ++ tailWord_5261836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261836).length < 2 ^ (prefixWord ++ tailWord_5261836).sum := by decide
  have hdescent : baseEnd_5261836 < baseStart_5261836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261853 : List Nat := [1, 4, 2, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_5261853 : Nat := 118140960795 + 5261853 * 2 ^ 59
def prefixEnd_5261853 : Nat := 4983230072969 + 3 ^ 40 * 5261853 * 2
def baseEnd_5261853 : Nat := 2701859722302306709638685

theorem tailTrace_5261853 : CollatzResearch.WordTrace tailWord_5261853 prefixEnd_5261853 2701859722302306709638685 := by
  unfold tailWord_5261853
  simp only [CollatzResearch.WordTrace]
  refine ⟨191915545406212708792094213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127943696937475139194729475 191915545406212708792094213)
  ·
    refine ⟨35984164763664882898517665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191915545406212708792094213 35984164763664882898517665)
    ·
      refine ⟨26988123572748662173888249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35984164763664882898517665 26988123572748662173888249)
      ·
        refine ⟨20241092679561496630416187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26988123572748662173888249 20241092679561496630416187)
        ·
          refine ⟨30361639019342244945624281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20241092679561496630416187 30361639019342244945624281)
          ·
            refine ⟨22771229264506683709218211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30361639019342244945624281 22771229264506683709218211)
            ·
              refine ⟨34156843896760025563827317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22771229264506683709218211 34156843896760025563827317)
              ·
                refine ⟨3202204115321252396608811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34156843896760025563827317 3202204115321252396608811)
                ·
                  refine ⟨4803306172981878594913217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202204115321252396608811 4803306172981878594913217)
                  ·
                    refine ⟨3602479629736408946184913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803306172981878594913217 3602479629736408946184913)
                    ·
                      refine ⟨2701859722302306709638685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602479629736408946184913 2701859722302306709638685)
                      ·
                        rfl

theorem cell23_5261853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_5261853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261853 prefixEnd_5261853 := by exact prefixLift 5261853
  have htrace : WordTrace (prefixWord ++ tailWord_5261853) baseStart_5261853 baseEnd_5261853 := by
    simpa [prefixWord, tailWord_5261853, baseEnd_5261853] using wordTrace_append hprefix tailTrace_5261853
  have hstable : (prefixWord ++ tailWord_5261853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261853).length < 2 ^ (prefixWord ++ tailWord_5261853).sum := by decide
  have hdescent : baseEnd_5261853 < baseStart_5261853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261856 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5261856 : Nat := 118140960795 + 5261856 * 2 ^ 59
def prefixEnd_5261856 : Nat := 4983230072969 + 3 ^ 40 * 5261856 * 2
def baseEnd_5261856 : Nat := 2701861262744270197901171

theorem tailTrace_5261856 : CollatzResearch.WordTrace tailWord_5261856 prefixEnd_5261856 2701861262744270197901171 := by
  unfold tailWord_5261856
  simp only [CollatzResearch.WordTrace]
  refine ⟨95957827412600920152226711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127943769883467893536302281 95957827412600920152226711)
  ·
    refine ⟨143936741118901380228340067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95957827412600920152226711 143936741118901380228340067)
    ·
      refine ⟨215905111678352070342510101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143936741118901380228340067 215905111678352070342510101)
      ·
        refine ⟨10120552109922753297305161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 215905111678352070342510101 10120552109922753297305161)
        ·
          refine ⟨7590414082442064972978871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10120552109922753297305161 7590414082442064972978871)
          ·
            refine ⟨11385621123663097459468307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7590414082442064972978871 11385621123663097459468307)
            ·
              refine ⟨17078431685494646189202461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11385621123663097459468307 17078431685494646189202461)
              ·
                refine ⟨6404411882060492320950923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17078431685494646189202461 6404411882060492320950923)
                ·
                  refine ⟨9606617823090738481426385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6404411882060492320950923 9606617823090738481426385)
                  ·
                    refine ⟨7204963367318053861069789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9606617823090738481426385 7204963367318053861069789)
                    ·
                      refine ⟨2701861262744270197901171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7204963367318053861069789 2701861262744270197901171)
                      ·
                        rfl

theorem cell23_5261856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5261856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261856 prefixEnd_5261856 := by exact prefixLift 5261856
  have htrace : WordTrace (prefixWord ++ tailWord_5261856) baseStart_5261856 baseEnd_5261856 := by
    simpa [prefixWord, tailWord_5261856, baseEnd_5261856] using wordTrace_append hprefix tailTrace_5261856
  have hstable : (prefixWord ++ tailWord_5261856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261856).length < 2 ^ (prefixWord ++ tailWord_5261856).sum := by decide
  have hdescent : baseEnd_5261856 < baseStart_5261856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261909 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_5261909 : Nat := 118140960795 + 5261909 * 2 ^ 59
def prefixEnd_5261909 : Nat := 4983230072969 + 3 ^ 40 * 5261909 * 2
def baseEnd_5261909 : Nat := 2701888477218958490538427

theorem tailTrace_5261909 : CollatzResearch.WordTrace tailWord_5261909 prefixEnd_5261909 2701888477218958490538427 := by
  unfold tailWord_5261909
  simp only [CollatzResearch.WordTrace]
  refine ⟨191917587894009830356132781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127945058596006553570755187 191917587894009830356132781)
  ·
    refine ⟨71969095460253686383549793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191917587894009830356132781 71969095460253686383549793)
    ·
      refine ⟨53976821595190264787662345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71969095460253686383549793 53976821595190264787662345)
      ·
        refine ⟨40482616196392698590746759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53976821595190264787662345 40482616196392698590746759)
        ·
          refine ⟨60723924294589047886120139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40482616196392698590746759 60723924294589047886120139)
          ·
            refine ⟨91085886441883571829180209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60723924294589047886120139 91085886441883571829180209)
            ·
              refine ⟨68314414831412678871885157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91085886441883571829180209 68314414831412678871885157)
              ·
                refine ⟨12808952780889877288478467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68314414831412678871885157 12808952780889877288478467)
                ·
                  refine ⟨19213429171334815932717701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12808952780889877288478467 19213429171334815932717701)
                  ·
                    refine ⟨3602517969625277987384569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19213429171334815932717701 3602517969625277987384569)
                    ·
                      refine ⟨2701888477218958490538427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602517969625277987384569 2701888477218958490538427)
                      ·
                        rfl

theorem cell23_5261909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_5261909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261909 prefixEnd_5261909 := by exact prefixLift 5261909
  have htrace : WordTrace (prefixWord ++ tailWord_5261909) baseStart_5261909 baseEnd_5261909 := by
    simpa [prefixWord, tailWord_5261909, baseEnd_5261909] using wordTrace_append hprefix tailTrace_5261909
  have hstable : (prefixWord ++ tailWord_5261909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261909).length < 2 ^ (prefixWord ++ tailWord_5261909).sum := by decide
  have hdescent : baseEnd_5261909 < baseStart_5261909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261932 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 7]
def baseStart_5261932 : Nat := 118140960795 + 5261932 * 2 ^ 59
def prefixEnd_5261932 : Nat := 4983230072969 + 3 ^ 40 * 5261932 * 2
def baseEnd_5261932 : Nat := 300211143030445766727869

theorem tailTrace_5261932 : CollatzResearch.WordTrace tailWord_5261932 prefixEnd_5261932 300211143030445766727869 := by
  unfold tailWord_5261932
  simp only [CollatzResearch.WordTrace]
  refine ⟨95959213386463252642110025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127945617848617670189480033 95959213386463252642110025)
  ·
    refine ⟨71969410039847439481582519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95959213386463252642110025 71969410039847439481582519)
    ·
      refine ⟨107954115059771159222373779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71969410039847439481582519 107954115059771159222373779)
      ·
        refine ⟨161931172589656738833560669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107954115059771159222373779 161931172589656738833560669)
        ·
          refine ⟨60724189721121277062585251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161931172589656738833560669 60724189721121277062585251)
          ·
            refine ⟨91086284581681915593877877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60724189721121277062585251 91086284581681915593877877)
            ·
              refine ⟨8539339179532679586926051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91086284581681915593877877 8539339179532679586926051)
              ·
                refine ⟨12809008769299019380389077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8539339179532679586926051 12809008769299019380389077)
                ·
                  refine ⟨300211143030445766727869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12809008769299019380389077 300211143030445766727869)
                  ·
                    rfl

theorem cell23_5261932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_5261932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261932 prefixEnd_5261932 := by exact prefixLift 5261932
  have htrace : WordTrace (prefixWord ++ tailWord_5261932) baseStart_5261932 baseEnd_5261932 := by
    simpa [prefixWord, tailWord_5261932, baseEnd_5261932] using wordTrace_append hprefix tailTrace_5261932
  have hstable : (prefixWord ++ tailWord_5261932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261932).length < 2 ^ (prefixWord ++ tailWord_5261932).sum := by decide
  have hdescent : baseEnd_5261932 < baseStart_5261932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261943 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 2, 2, 2]
def baseStart_5261943 : Nat := 118140960795 + 5261943 * 2 ^ 59
def prefixEnd_5261943 : Nat := 4983230072969 + 3 ^ 40 * 5261943 * 2
def baseEnd_5261943 : Nat := 2701905935561211357513271

theorem tailTrace_5261943 : CollatzResearch.WordTrace tailWord_5261943 prefixEnd_5261943 2701905935561211357513271 := by
  unfold tailWord_5261943
  simp only [CollatzResearch.WordTrace]
  refine ⟨191918827975886654162870483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127945885317257769441913655 191918827975886654162870483)
  ·
    refine ⟨287878241963829981244305725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191918827975886654162870483 287878241963829981244305725)
    ·
      refine ⟨107954340736436242966614647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287878241963829981244305725 107954340736436242966614647)
      ·
        refine ⟨161931511104654364449921971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107954340736436242966614647 161931511104654364449921971)
        ·
          refine ⟨242897266656981546674882957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161931511104654364449921971 242897266656981546674882957)
          ·
            refine ⟨91086474996368080003081109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242897266656981546674882957 91086474996368080003081109)
            ·
              refine ⟨4269678515454753750144427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91086474996368080003081109 4269678515454753750144427)
              ·
                refine ⟨6404517773182130625216641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269678515454753750144427 6404517773182130625216641)
                ·
                  refine ⟨4803388329886597968912481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6404517773182130625216641 4803388329886597968912481)
                  ·
                    refine ⟨3602541247414948476684361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803388329886597968912481 3602541247414948476684361)
                    ·
                      refine ⟨2701905935561211357513271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602541247414948476684361 2701905935561211357513271)
                      ·
                        rfl

theorem cell23_5261943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_5261943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261943 prefixEnd_5261943 := by exact prefixLift 5261943
  have htrace : WordTrace (prefixWord ++ tailWord_5261943) baseStart_5261943 baseEnd_5261943 := by
    simpa [prefixWord, tailWord_5261943, baseEnd_5261943] using wordTrace_append hprefix tailTrace_5261943
  have hstable : (prefixWord ++ tailWord_5261943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261943).length < 2 ^ (prefixWord ++ tailWord_5261943).sum := by decide
  have hdescent : baseEnd_5261943 < baseStart_5261943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5261999 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 1, 6, 2]
def baseStart_5261999 : Nat := 118140960795 + 5261999 * 2 ^ 59
def prefixEnd_5261999 : Nat := 4983230072969 + 3 ^ 40 * 5261999 * 2
def baseEnd_5261999 : Nat := 2701934690477863138413013

theorem tailTrace_5261999 : CollatzResearch.WordTrace tailWord_5261999 prefixEnd_5261999 2701934690477863138413013 := by
  unfold tailWord_5261999
  simp only [CollatzResearch.WordTrace]
  refine ⟨191920870463683775726909051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127947246975789183817939367 191920870463683775726909051)
  ·
    refine ⟨287881305695525663590363577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191920870463683775726909051 287881305695525663590363577)
    ·
      refine ⟨215910979271644247692772683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287881305695525663590363577 215910979271644247692772683)
      ·
        refine ⟨323866468907466371539159025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215910979271644247692772683 323866468907466371539159025)
        ·
          refine ⟨242899851680599778654369269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323866468907466371539159025 242899851680599778654369269)
          ·
            refine ⟨22771861095056229248847119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242899851680599778654369269 22771861095056229248847119)
            ·
              refine ⟨34157791642584343873270679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22771861095056229248847119 34157791642584343873270679)
              ·
                refine ⟨51236687463876515809906019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34157791642584343873270679 51236687463876515809906019)
                ·
                  refine ⟨76855031195814773714859029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51236687463876515809906019 76855031195814773714859029)
                  ·
                    refine ⟨3602579587303817517884017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76855031195814773714859029 3602579587303817517884017)
                    ·
                      refine ⟨2701934690477863138413013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602579587303817517884017 2701934690477863138413013)
                      ·
                        rfl

theorem cell23_5261999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 6, 2].length) (baseStart_5261999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5261999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5261999 prefixEnd_5261999 := by exact prefixLift 5261999
  have htrace : WordTrace (prefixWord ++ tailWord_5261999) baseStart_5261999 baseEnd_5261999 := by
    simpa [prefixWord, tailWord_5261999, baseEnd_5261999] using wordTrace_append hprefix tailTrace_5261999
  have hstable : (prefixWord ++ tailWord_5261999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5261999).length < 2 ^ (prefixWord ++ tailWord_5261999).sum := by decide
  have hdescent : baseEnd_5261999 < baseStart_5261999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5261999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262016 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 4]
def baseStart_5262016 : Nat := 118140960795 + 5262016 * 2 ^ 59
def prefixEnd_5262016 : Nat := 4983230072969 + 3 ^ 40 * 5262016 * 2
def baseEnd_5262016 : Nat := 2701943419648989571900435

theorem tailTrace_5262016 : CollatzResearch.WordTrace tailWord_5262016 prefixEnd_5262016 2701943419648989571900435 := by
  unfold tailWord_5262016
  simp only [CollatzResearch.WordTrace]
  refine ⟨95960745252311093815138951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127947660336414791753518601 95960745252311093815138951)
  ·
    refine ⟨143941117878466640722708427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95960745252311093815138951 143941117878466640722708427)
    ·
      refine ⟨215911676817699961084062641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143941117878466640722708427 215911676817699961084062641)
      ·
        refine ⟨161933757613274970813046981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215911676817699961084062641 161933757613274970813046981)
        ·
          refine ⟨30362579552489057027446309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161933757613274970813046981 30362579552489057027446309)
          ·
            refine ⟨5692983666091698192646183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30362579552489057027446309 5692983666091698192646183)
            ·
              refine ⟨8539475499137547288969275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5692983666091698192646183 8539475499137547288969275)
              ·
                refine ⟨12809213248706320933453913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8539475499137547288969275 12809213248706320933453913)
                ·
                  refine ⟨9606909936529740700090435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12809213248706320933453913 9606909936529740700090435)
                  ·
                    refine ⟨14410364904794611050135653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9606909936529740700090435 14410364904794611050135653)
                    ·
                      refine ⟨2701943419648989571900435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14410364904794611050135653 2701943419648989571900435)
                      ·
                        rfl

theorem cell23_5262016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_5262016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262016 prefixEnd_5262016 := by exact prefixLift 5262016
  have htrace : WordTrace (prefixWord ++ tailWord_5262016) baseStart_5262016 baseEnd_5262016 := by
    simpa [prefixWord, tailWord_5262016, baseEnd_5262016] using wordTrace_append hprefix tailTrace_5262016
  have hstable : (prefixWord ++ tailWord_5262016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262016).length < 2 ^ (prefixWord ++ tailWord_5262016).sum := by decide
  have hdescent : baseEnd_5262016 < baseStart_5262016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262039 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 6]
def baseStart_5262039 : Nat := 118140960795 + 5262039 * 2 ^ 59
def prefixEnd_5262039 : Nat := 4983230072969 + 3 ^ 40 * 5262039 * 2
def baseEnd_5262039 : Nat := 300217247744893664656981

theorem tailTrace_5262039 : CollatzResearch.WordTrace tailWord_5262039 prefixEnd_5262039 300217247744893664656981 := by
  unfold tailWord_5262039
  simp only [CollatzResearch.WordTrace]
  refine ⟨191922329383538862558365171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127948219589025908372243447 191922329383538862558365171)
  ·
    refine ⟨287883494075308293837547757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191922329383538862558365171 287883494075308293837547757)
    ·
      refine ⟨107956310278240610189080409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287883494075308293837547757 107956310278240610189080409)
      ·
        refine ⟨80967232708680457641810307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107956310278240610189080409 80967232708680457641810307)
        ·
          refine ⟨121450849063020686462715461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80967232708680457641810307 121450849063020686462715461)
          ·
            refine ⟨22772034199316378711759149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121450849063020686462715461 22772034199316378711759149)
            ·
              refine ⟨8539512824743642016909681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22772034199316378711759149 8539512824743642016909681)
              ·
                refine ⟨6404634618557731512682261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8539512824743642016909681 6404634618557731512682261)
                ·
                  refine ⟨300217247744893664656981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6404634618557731512682261 300217247744893664656981)
                  ·
                    rfl

theorem cell23_5262039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 6].length) (baseStart_5262039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262039 prefixEnd_5262039 := by exact prefixLift 5262039
  have htrace : WordTrace (prefixWord ++ tailWord_5262039) baseStart_5262039 baseEnd_5262039 := by
    simpa [prefixWord, tailWord_5262039, baseEnd_5262039] using wordTrace_append hprefix tailTrace_5262039
  have hstable : (prefixWord ++ tailWord_5262039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262039).length < 2 ^ (prefixWord ++ tailWord_5262039).sum := by decide
  have hdescent : baseEnd_5262039 < baseStart_5262039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262042 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_5262042 : Nat := 118140960795 + 5262042 * 2 ^ 59
def prefixEnd_5262042 : Nat := 4983230072969 + 3 ^ 40 * 5262042 * 2
def baseEnd_5262042 : Nat := 2701956770146006470175315

theorem tailTrace_5262042 : CollatzResearch.WordTrace tailWord_5262042 prefixEnd_5262042 2701956770146006470175315 := by
  unfold tailWord_5262042
  simp only [CollatzResearch.WordTrace]
  refine ⟨47980609700631998517681095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127948292535018662713816253 47980609700631998517681095)
  ·
    refine ⟨71970914550947997776521643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47980609700631998517681095 71970914550947997776521643)
    ·
      refine ⟨107956371826421996664782465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71970914550947997776521643 107956371826421996664782465)
      ·
        refine ⟨80967278869816497498586849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107956371826421996664782465 80967278869816497498586849)
        ·
          refine ⟨60725459152362373123940137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80967278869816497498586849 60725459152362373123940137)
          ·
            refine ⟨45544094364271779842955103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60725459152362373123940137 45544094364271779842955103)
            ·
              refine ⟨68316141546407669764432655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45544094364271779842955103 68316141546407669764432655)
              ·
                refine ⟨102474212319611504646648983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68316141546407669764432655 102474212319611504646648983)
                ·
                  refine ⟨153711318479417256969973475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102474212319611504646648983 153711318479417256969973475)
                  ·
                    refine ⟨230566977719125885454960213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153711318479417256969973475 230566977719125885454960213)
                    ·
                      refine ⟨2701956770146006470175315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 230566977719125885454960213 2701956770146006470175315)
                      ·
                        rfl

theorem cell23_5262042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_5262042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262042 prefixEnd_5262042 := by exact prefixLift 5262042
  have htrace : WordTrace (prefixWord ++ tailWord_5262042) baseStart_5262042 baseEnd_5262042 := by
    simpa [prefixWord, tailWord_5262042, baseEnd_5262042] using wordTrace_append hprefix tailTrace_5262042
  have hstable : (prefixWord ++ tailWord_5262042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262042).length < 2 ^ (prefixWord ++ tailWord_5262042).sum := by decide
  have hdescent : baseEnd_5262042 < baseStart_5262042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262076 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_5262076 : Nat := 118140960795 + 5262076 * 2 ^ 59
def prefixEnd_5262076 : Nat := 4983230072969 + 3 ^ 40 * 5262076 * 2
def baseEnd_5262076 : Nat := 2701974228488259337150159

theorem tailTrace_5262076 : CollatzResearch.WordTrace tailWord_5262076 prefixEnd_5262076 2701974228488259337150159 := by
  unfold tailWord_5262076
  simp only [CollatzResearch.WordTrace]
  refine ⟨95961839442202408938731041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127949119256269878584974721 95961839442202408938731041)
  ·
    refine ⟨71971379581651806704048281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95961839442202408938731041 71971379581651806704048281)
    ·
      refine ⟨53978534686238855028036211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71971379581651806704048281 53978534686238855028036211)
      ·
        refine ⟨80967802029358282542054317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53978534686238855028036211 80967802029358282542054317)
        ·
          refine ⟨30362925761009355953270369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80967802029358282542054317 30362925761009355953270369)
          ·
            refine ⟨22772194320757016964952777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30362925761009355953270369 22772194320757016964952777)
            ·
              refine ⟨17079145740567762723714583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22772194320757016964952777 17079145740567762723714583)
              ·
                refine ⟨25618718610851644085571875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17079145740567762723714583 25618718610851644085571875)
                ·
                  refine ⟨38428077916277466128357813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25618718610851644085571875 38428077916277466128357813)
                  ·
                    refine ⟨3602632304651012449533545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38428077916277466128357813 3602632304651012449533545)
                    ·
                      refine ⟨2701974228488259337150159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602632304651012449533545 2701974228488259337150159)
                      ·
                        rfl

theorem cell23_5262076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_5262076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262076 prefixEnd_5262076 := by exact prefixLift 5262076
  have htrace : WordTrace (prefixWord ++ tailWord_5262076) baseStart_5262076 baseEnd_5262076 := by
    simpa [prefixWord, tailWord_5262076, baseEnd_5262076] using wordTrace_append hprefix tailTrace_5262076
  have hstable : (prefixWord ++ tailWord_5262076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262076).length < 2 ^ (prefixWord ++ tailWord_5262076).sum := by decide
  have hdescent : baseEnd_5262076 < baseStart_5262076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262099 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 4, 4]
def baseStart_5262099 : Nat := 118140960795 + 5262099 * 2 ^ 59
def prefixEnd_5262099 : Nat := 4983230072969 + 3 ^ 40 * 5262099 * 2
def baseEnd_5262099 : Nat := 900662012847770915720851

theorem tailTrace_5262099 : CollatzResearch.WordTrace tailWord_5262099 prefixEnd_5262099 900662012847770915720851 := by
  unfold tailWord_5262099
  simp only [CollatzResearch.WordTrace]
  refine ⟨191924517763321492805549351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127949678508880995203699567 191924517763321492805549351)
  ·
    refine ⟨287886776644982239208324027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191924517763321492805549351 287886776644982239208324027)
    ·
      refine ⟨431830164967473358812486041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287886776644982239208324027 431830164967473358812486041)
      ·
        refine ⟨323872623725605019109364531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431830164967473358812486041 323872623725605019109364531)
        ·
          refine ⟨485808935588407528664046797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323872623725605019109364531 485808935588407528664046797)
          ·
            refine ⟨182178350845652823249017549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 485808935588407528664046797 182178350845652823249017549)
            ·
              refine ⟨68316881567119808718381581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182178350845652823249017549 68316881567119808718381581)
              ·
                refine ⟨25618830587669928269393093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68316881567119808718381581 25618830587669928269393093)
                ·
                  refine ⟨4803530735188111550511205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25618830587669928269393093 4803530735188111550511205)
                  ·
                    refine ⟨900662012847770915720851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4803530735188111550511205 900662012847770915720851)
                    ·
                      rfl

theorem cell23_5262099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 4].length) (baseStart_5262099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262099 prefixEnd_5262099 := by exact prefixLift 5262099
  have htrace : WordTrace (prefixWord ++ tailWord_5262099) baseStart_5262099 baseEnd_5262099 := by
    simpa [prefixWord, tailWord_5262099, baseEnd_5262099] using wordTrace_append hprefix tailTrace_5262099
  have hstable : (prefixWord ++ tailWord_5262099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262099).length < 2 ^ (prefixWord ++ tailWord_5262099).sum := by decide
  have hdescent : baseEnd_5262099 < baseStart_5262099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262140 : List Nat := [2, 2, 2, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_5262140 : Nat := 118140960795 + 5262140 * 2 ^ 59
def prefixEnd_5262140 : Nat := 4983230072969 + 3 ^ 40 * 5262140 * 2
def baseEnd_5262140 : Nat := 2702007091250147086749865

theorem tailTrace_5262140 : CollatzResearch.WordTrace tailWord_5262140 prefixEnd_5262140 2702007091250147086749865 := by
  unfold tailWord_5262140
  simp only [CollatzResearch.WordTrace]
  refine ⟨95963006578086478403895937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127950675437448637871861249 95963006578086478403895937)
  ·
    refine ⟨71972254933564858802921953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95963006578086478403895937 71972254933564858802921953)
    ·
      refine ⟨53979191200173644102191465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71972254933564858802921953 53979191200173644102191465)
      ·
        refine ⟨40484393400130233076643599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53979191200173644102191465 40484393400130233076643599)
        ·
          refine ⟨60726590100195349614965399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40484393400130233076643599 60726590100195349614965399)
          ·
            refine ⟨91089885150293024422448099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60726590100195349614965399 91089885150293024422448099)
            ·
              refine ⟨136634827725439536633672149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91089885150293024422448099 136634827725439536633672149)
              ·
                refine ⟨3202378774814989139851691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 136634827725439536633672149 3202378774814989139851691)
                ·
                  refine ⟨4803568162222483709777537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202378774814989139851691 4803568162222483709777537)
                  ·
                    refine ⟨3602676121666862782333153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803568162222483709777537 3602676121666862782333153)
                    ·
                      refine ⟨2702007091250147086749865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602676121666862782333153 2702007091250147086749865)
                      ·
                        rfl

theorem cell23_5262140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_5262140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262140 prefixEnd_5262140 := by exact prefixLift 5262140
  have htrace : WordTrace (prefixWord ++ tailWord_5262140) baseStart_5262140 baseEnd_5262140 := by
    simpa [prefixWord, tailWord_5262140, baseEnd_5262140] using wordTrace_append hprefix tailTrace_5262140
  have hstable : (prefixWord ++ tailWord_5262140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262140).length < 2 ^ (prefixWord ++ tailWord_5262140).sum := by decide
  have hdescent : baseEnd_5262140 < baseStart_5262140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262183 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_5262183 : Nat := 118140960795 + 5262183 * 2 ^ 59
def prefixEnd_5262183 : Nat := 4983230072969 + 3 ^ 40 * 5262183 * 2
def baseEnd_5262183 : Nat := 2702029170918290418512167

theorem tailTrace_5262183 : CollatzResearch.WordTrace tailWord_5262183 prefixEnd_5262183 2702029170918290418512167 := by
  unfold tailWord_5262183
  simp only [CollatzResearch.WordTrace]
  refine ⟨191927581495017175151607203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127951720996678116767738135 191927581495017175151607203)
  ·
    refine ⟨287891372242525762727410805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191927581495017175151607203 287891372242525762727410805)
    ·
      refine ⟨26989816147736790255694763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 287891372242525762727410805 26989816147736790255694763)
      ·
        refine ⟨40484724221605185383542145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26989816147736790255694763 40484724221605185383542145)
        ·
          refine ⟨30363543166203889037656609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40484724221605185383542145 30363543166203889037656609)
          ·
            refine ⟨22772657374652916778242457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30363543166203889037656609 22772657374652916778242457)
            ·
              refine ⟨17079493030989687583681843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22772657374652916778242457 17079493030989687583681843)
              ·
                refine ⟨25619239546484531375522765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17079493030989687583681843 25619239546484531375522765)
                ·
                  refine ⟨9607214829931699265821037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25619239546484531375522765 9607214829931699265821037)
                  ·
                    refine ⟨3602705561224387224682889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9607214829931699265821037 3602705561224387224682889)
                    ·
                      refine ⟨2702029170918290418512167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602705561224387224682889 2702029170918290418512167)
                      ·
                        rfl

theorem cell23_5262183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_5262183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262183 prefixEnd_5262183 := by exact prefixLift 5262183
  have htrace : WordTrace (prefixWord ++ tailWord_5262183) baseStart_5262183 baseEnd_5262183 := by
    simpa [prefixWord, tailWord_5262183, baseEnd_5262183] using wordTrace_append hprefix tailTrace_5262183
  have hstable : (prefixWord ++ tailWord_5262183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262183).length < 2 ^ (prefixWord ++ tailWord_5262183).sum := by decide
  have hdescent : baseEnd_5262183 < baseStart_5262183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262189 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_5262189 : Nat := 118140960795 + 5262189 * 2 ^ 59
def prefixEnd_5262189 : Nat := 4983230072969 + 3 ^ 40 * 5262189 * 2
def baseEnd_5262189 : Nat := 900677417267405798345713

theorem tailTrace_5262189 : CollatzResearch.WordTrace tailWord_5262189 prefixEnd_5262189 900677417267405798345713 := by
  unfold tailWord_5262189
  simp only [CollatzResearch.WordTrace]
  refine ⟨191927800332995438176325621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127951866888663625450883747 191927800332995438176325621)
  ·
    refine ⟨17993231281218322329030527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191927800332995438176325621 17993231281218322329030527)
    ·
      refine ⟨26989846921827483493545791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17993231281218322329030527 26989846921827483493545791)
      ·
        refine ⟨40484770382741225240318687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26989846921827483493545791 40484770382741225240318687)
        ·
          refine ⟨60727155574111837860478031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40484770382741225240318687 60727155574111837860478031)
          ·
            refine ⟨91090733361167756790717047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60727155574111837860478031 91090733361167756790717047)
            ·
              refine ⟨136636100041751635186075571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91090733361167756790717047 136636100041751635186075571)
              ·
                refine ⟨204954150062627452779113357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136636100041751635186075571 204954150062627452779113357)
                ·
                  refine ⟨76857806273485294792167509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204954150062627452779113357 76857806273485294792167509)
                  ·
                    refine ⟨900677417267405798345713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76857806273485294792167509 900677417267405798345713)
                    ·
                      rfl

theorem cell23_5262189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_5262189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262189 prefixEnd_5262189 := by exact prefixLift 5262189
  have htrace : WordTrace (prefixWord ++ tailWord_5262189) baseStart_5262189 baseEnd_5262189 := by
    simpa [prefixWord, tailWord_5262189, baseEnd_5262189] using wordTrace_append hprefix tailTrace_5262189
  have hstable : (prefixWord ++ tailWord_5262189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262189).length < 2 ^ (prefixWord ++ tailWord_5262189).sum := by decide
  have hdescent : baseEnd_5262189 < baseStart_5262189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262199 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_5262199 : Nat := 118140960795 + 5262199 * 2 ^ 59
def prefixEnd_5262199 : Nat := 4983230072969 + 3 ^ 40 * 5262199 * 2
def baseEnd_5262199 : Nat := 2702037386608762355912093

theorem tailTrace_5262199 : CollatzResearch.WordTrace tailWord_5262199 prefixEnd_5262199 2702037386608762355912093 := by
  unfold tailWord_5262199
  simp only [CollatzResearch.WordTrace]
  refine ⟨191928165062959209884189651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127952110041972806589459767 191928165062959209884189651)
  ·
    refine ⟨287892247594438814826284477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191928165062959209884189651 287892247594438814826284477)
    ·
      refine ⟨107959592847914555559856679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287892247594438814826284477 107959592847914555559856679)
      ·
        refine ⟨161939389271871833339785019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107959592847914555559856679 161939389271871833339785019)
        ·
          refine ⟨242909083907807750009677529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161939389271871833339785019 242909083907807750009677529)
          ·
            refine ⟨182181812930855812507258147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242909083907807750009677529 182181812930855812507258147)
            ·
              refine ⟨273272719396283718760887221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182181812930855812507258147 273272719396283718760887221)
              ·
                refine ⟨25619317443401598633833177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 273272719396283718760887221 25619317443401598633833177)
                ·
                  refine ⟨19214488082551198975374883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25619317443401598633833177 19214488082551198975374883)
                  ·
                    refine ⟨28821732123826798463062325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19214488082551198975374883 28821732123826798463062325)
                    ·
                      refine ⟨2702037386608762355912093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28821732123826798463062325 2702037386608762355912093)
                      ·
                        rfl

theorem cell23_5262199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_5262199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262199 prefixEnd_5262199 := by exact prefixLift 5262199
  have htrace : WordTrace (prefixWord ++ tailWord_5262199) baseStart_5262199 baseEnd_5262199 := by
    simpa [prefixWord, tailWord_5262199, baseEnd_5262199] using wordTrace_append hprefix tailTrace_5262199
  have hstable : (prefixWord ++ tailWord_5262199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262199).length < 2 ^ (prefixWord ++ tailWord_5262199).sum := by decide
  have hdescent : baseEnd_5262199 < baseStart_5262199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262219 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 7]
def baseStart_5262219 : Nat := 118140960795 + 5262219 * 2 ^ 59
def prefixEnd_5262219 : Nat := 4983230072969 + 3 ^ 40 * 5262219 * 2
def baseEnd_5262219 : Nat := 300227517357983586406889

theorem tailTrace_5262219 : CollatzResearch.WordTrace tailWord_5262219 prefixEnd_5262219 300227517357983586406889 := by
  unfold tailWord_5262219
  simp only [CollatzResearch.WordTrace]
  refine ⟨191928894522886753299917711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127952596348591168866611807 191928894522886753299917711)
  ·
    refine ⟨287893341784330129949876567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191928894522886753299917711 287893341784330129949876567)
    ·
      refine ⟨431840012676495194924814851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287893341784330129949876567 431840012676495194924814851)
      ·
        refine ⟨647760019014742792387222277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431840012676495194924814851 647760019014742792387222277)
        ·
          refine ⟨121455003565264273572604177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 647760019014742792387222277 121455003565264273572604177)
          ·
            refine ⟨91091252673948205179453133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121455003565264273572604177 91091252673948205179453133)
            ·
              refine ⟨34159219752730576942294925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91091252673948205179453133 34159219752730576942294925)
              ·
                refine ⟨12809707407273966353360597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34159219752730576942294925 12809707407273966353360597)
                ·
                  refine ⟨300227517357983586406889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12809707407273966353360597 300227517357983586406889)
                  ·
                    rfl

theorem cell23_5262219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 7].length) (baseStart_5262219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262219 prefixEnd_5262219 := by exact prefixLift 5262219
  have htrace : WordTrace (prefixWord ++ tailWord_5262219) baseStart_5262219 baseEnd_5262219 := by
    simpa [prefixWord, tailWord_5262219, baseEnd_5262219] using wordTrace_append hprefix tailTrace_5262219
  have hstable : (prefixWord ++ tailWord_5262219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262219).length < 2 ^ (prefixWord ++ tailWord_5262219).sum := by decide
  have hdescent : baseEnd_5262219 < baseStart_5262219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262249 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 1, 7]
def baseStart_5262249 : Nat := 118140960795 + 5262249 * 2 ^ 59
def prefixEnd_5262249 : Nat := 4983230072969 + 3 ^ 40 * 5262249 * 2
def baseEnd_5262249 : Nat := 900687686880495720095621

theorem tailTrace_5262249 : CollatzResearch.WordTrace tailWord_5262249 prefixEnd_5262249 900687686880495720095621 := by
  unfold tailWord_5262249
  simp only [CollatzResearch.WordTrace]
  refine ⟨191929988712778068423509801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127953325808518712282339867 191929988712778068423509801)
  ·
    refine ⟨143947491534583551317632351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191929988712778068423509801 143947491534583551317632351)
    ·
      refine ⟨215921237301875326976448527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143947491534583551317632351 215921237301875326976448527)
      ·
        refine ⟨323881855952812990464672791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215921237301875326976448527 323881855952812990464672791)
        ·
          refine ⟨485822783929219485697009187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323881855952812990464672791 485822783929219485697009187)
          ·
            refine ⟨728734175893829228545513781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485822783929219485697009187 728734175893829228545513781)
            ·
              refine ⟨68318828990046490176141917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 728734175893829228545513781 68318828990046490176141917)
              ·
                refine ⟨25619560871267433816053219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68318828990046490176141917 25619560871267433816053219)
                ·
                  refine ⟨38429341306901150724079829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25619560871267433816053219 38429341306901150724079829)
                  ·
                    refine ⟨900687686880495720095621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38429341306901150724079829 900687686880495720095621)
                    ·
                      rfl

theorem cell23_5262249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_5262249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262249 prefixEnd_5262249 := by exact prefixLift 5262249
  have htrace : WordTrace (prefixWord ++ tailWord_5262249) baseStart_5262249 baseEnd_5262249 := by
    simpa [prefixWord, tailWord_5262249, baseEnd_5262249] using wordTrace_append hprefix tailTrace_5262249
  have hstable : (prefixWord ++ tailWord_5262249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262249).length < 2 ^ (prefixWord ++ tailWord_5262249).sum := by decide
  have hdescent : baseEnd_5262249 < baseStart_5262249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262266 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_5262266 : Nat := 118140960795 + 5262266 * 2 ^ 59
def prefixEnd_5262266 : Nat := 4983230072969 + 3 ^ 40 * 5262266 * 2
def baseEnd_5262266 : Nat := 900690596604204531258095

theorem tailTrace_5262266 : CollatzResearch.WordTrace tailWord_5262266 prefixEnd_5262266 900690596604204531258095 := by
  unfold tailWord_5262266
  simp only [CollatzResearch.WordTrace]
  refine ⟨47982652188429120081719663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127953739169144320217919101 47982652188429120081719663)
  ·
    refine ⟨71973978282643680122579495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47982652188429120081719663 71973978282643680122579495)
    ·
      refine ⟨107960967423965520183869243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71973978282643680122579495 107960967423965520183869243)
      ·
        refine ⟨161941451135948280275803865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107960967423965520183869243 161941451135948280275803865)
        ·
          refine ⟨121456088351961210206852899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161941451135948280275803865 121456088351961210206852899)
          ·
            refine ⟨182184132527941815310279349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121456088351961210206852899 182184132527941815310279349)
            ·
              refine ⟨17079762424494545185338689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 182184132527941815310279349 17079762424494545185338689)
              ·
                refine ⟨12809821818370908889004017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17079762424494545185338689 12809821818370908889004017)
                ·
                  refine ⟨9607366363778181666753013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12809821818370908889004017 9607366363778181666753013)
                  ·
                    refine ⟨900690596604204531258095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9607366363778181666753013 900690596604204531258095)
                    ·
                      rfl

theorem cell23_5262266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_5262266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262266 prefixEnd_5262266 := by exact prefixLift 5262266
  have htrace : WordTrace (prefixWord ++ tailWord_5262266) baseStart_5262266 baseEnd_5262266 := by
    simpa [prefixWord, tailWord_5262266, baseEnd_5262266] using wordTrace_append hprefix tailTrace_5262266
  have hstable : (prefixWord ++ tailWord_5262266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262266).length < 2 ^ (prefixWord ++ tailWord_5262266).sum := by decide
  have hdescent : baseEnd_5262266 < baseStart_5262266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262270 : List Nat := [4, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_5262270 : Nat := 118140960795 + 5262270 * 2 ^ 59
def prefixEnd_5262270 : Nat := 4983230072969 + 3 ^ 40 * 5262270 * 2
def baseEnd_5262270 : Nat := 300230427081692397569363

theorem tailTrace_5262270 : CollatzResearch.WordTrace tailWord_5262270 prefixEnd_5262270 300230427081692397569363 := by
  unfold tailWord_5262270
  simp only [CollatzResearch.WordTrace]
  refine ⟨23991344330712748626253033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127953836430467992673349509 23991344330712748626253033)
  ·
    refine ⟨17993508248034561469689775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23991344330712748626253033 17993508248034561469689775)
    ·
      refine ⟨26990262372051842204534663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17993508248034561469689775 26990262372051842204534663)
      ·
        refine ⟨40485393558077763306801995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26990262372051842204534663 40485393558077763306801995)
        ·
          refine ⟨60728090337116644960202993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40485393558077763306801995 60728090337116644960202993)
          ·
            refine ⟨45546067752837483720152245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60728090337116644960202993 45546067752837483720152245)
            ·
              refine ⟨4269943851828514098764273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45546067752837483720152245 4269943851828514098764273)
              ·
                refine ⟨3202457888871385574073205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269943851828514098764273 3202457888871385574073205)
                ·
                  refine ⟨300230427081692397569363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3202457888871385574073205 300230427081692397569363)
                  ·
                    rfl

theorem cell23_5262270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_5262270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262270 prefixEnd_5262270 := by exact prefixLift 5262270
  have htrace : WordTrace (prefixWord ++ tailWord_5262270) baseStart_5262270 baseEnd_5262270 := by
    simpa [prefixWord, tailWord_5262270, baseEnd_5262270] using wordTrace_append hprefix tailTrace_5262270
  have hstable : (prefixWord ++ tailWord_5262270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262270).length < 2 ^ (prefixWord ++ tailWord_5262270).sum := by decide
  have hdescent : baseEnd_5262270 < baseStart_5262270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262373 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_5262373 : Nat := 118140960795 + 5262373 * 2 ^ 59
def prefixEnd_5262373 : Nat := 4983230072969 + 3 ^ 40 * 5262373 * 2
def baseEnd_5262373 : Nat := 900708910747548225045431

theorem tailTrace_5262373 : CollatzResearch.WordTrace tailWord_5262373 prefixEnd_5262373 900708910747548225045431 := by
  unfold tailWord_5262373
  simp only [CollatzResearch.WordTrace]
  refine ⟨191934511364328837601023773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127956340909552558400682515 191934511364328837601023773)
  ·
    refine ⟨71975441761623314100383915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191934511364328837601023773 71975441761623314100383915)
    ·
      refine ⟨107963162642434971150575873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71975441761623314100383915 107963162642434971150575873)
      ·
        refine ⟨80972371981826228362931905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107963162642434971150575873 80972371981826228362931905)
        ·
          refine ⟨60729278986369671272198929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80972371981826228362931905 60729278986369671272198929)
          ·
            refine ⟨45546959239777253454149197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60729278986369671272198929 45546959239777253454149197)
            ·
              refine ⟨17080109714916470045305949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45546959239777253454149197 17080109714916470045305949)
              ·
                refine ⟨6405041143093676266989731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17080109714916470045305949 6405041143093676266989731)
                ·
                  refine ⟨9607561714640514400484597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6405041143093676266989731 9607561714640514400484597)
                  ·
                    refine ⟨900708910747548225045431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9607561714640514400484597 900708910747548225045431)
                    ·
                      rfl

theorem cell23_5262373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_5262373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262373 prefixEnd_5262373 := by exact prefixLift 5262373
  have htrace : WordTrace (prefixWord ++ tailWord_5262373) baseStart_5262373 baseEnd_5262373 := by
    simpa [prefixWord, tailWord_5262373, baseEnd_5262373] using wordTrace_append hprefix tailTrace_5262373
  have hstable : (prefixWord ++ tailWord_5262373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262373).length < 2 ^ (prefixWord ++ tailWord_5262373).sum := by decide
  have hdescent : baseEnd_5262373 < baseStart_5262373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262493 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_5262493 : Nat := 118140960795 + 5262493 * 2 ^ 59
def prefixEnd_5262493 : Nat := 4983230072969 + 3 ^ 40 * 5262493 * 2
def baseEnd_5262493 : Nat := 900729449973728068545247

theorem tailTrace_5262493 : CollatzResearch.WordTrace tailWord_5262493 prefixEnd_5262493 900729449973728068545247 := by
  unfold tailWord_5262493
  simp only [CollatzResearch.WordTrace]
  refine ⟨191938888123894098095392133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127959258749262732063594755 191938888123894098095392133)
  ·
    refine ⟨35988541523230143392886025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191938888123894098095392133 35988541523230143392886025)
    ·
      refine ⟨26991406142422607544664519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35988541523230143392886025 26991406142422607544664519)
      ·
        refine ⟨40487109213633911316996779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26991406142422607544664519 40487109213633911316996779)
        ·
          refine ⟨60730663820450866975495169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40487109213633911316996779 60730663820450866975495169)
          ·
            refine ⟨45547997865338150231621377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60730663820450866975495169 45547997865338150231621377)
            ·
              refine ⟨34160998399003612673716033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45547997865338150231621377 34160998399003612673716033)
              ·
                refine ⟨25620748799252709505287025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34160998399003612673716033 25620748799252709505287025)
                ·
                  refine ⟨19215561599439532128965269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25620748799252709505287025 19215561599439532128965269)
                  ·
                    refine ⟨900729449973728068545247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19215561599439532128965269 900729449973728068545247)
                    ·
                      rfl

theorem cell23_5262493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_5262493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262493 prefixEnd_5262493 := by exact prefixLift 5262493
  have htrace : WordTrace (prefixWord ++ tailWord_5262493) baseStart_5262493 baseEnd_5262493 := by
    simpa [prefixWord, tailWord_5262493, baseEnd_5262493] using wordTrace_append hprefix tailTrace_5262493
  have hstable : (prefixWord ++ tailWord_5262493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262493).length < 2 ^ (prefixWord ++ tailWord_5262493).sum := by decide
  have hdescent : baseEnd_5262493 < baseStart_5262493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262494 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_5262494 : Nat := 118140960795 + 5262494 * 2 ^ 59
def prefixEnd_5262494 : Nat := 4983230072969 + 3 ^ 40 * 5262494 * 2
def baseEnd_5262494 : Nat := 2702188863401838701723237

theorem tailTrace_5262494 : CollatzResearch.WordTrace tailWord_5262494 prefixEnd_5262494 2702188863401838701723237 := by
  unfold tailWord_5262494
  simp only [CollatzResearch.WordTrace]
  refine ⟨23992365574611309408272317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127959283064593650177452357 23992365574611309408272317)
  ·
    refine ⟨8997137090479241028102119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23992365574611309408272317 8997137090479241028102119)
    ·
      refine ⟨13495705635718861542153179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8997137090479241028102119 13495705635718861542153179)
      ·
        refine ⟨20243558453578292313229769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13495705635718861542153179 20243558453578292313229769)
        ·
          refine ⟨15182668840183719234922327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20243558453578292313229769 15182668840183719234922327)
          ·
            refine ⟨22774003260275578852383491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15182668840183719234922327 22774003260275578852383491)
            ·
              refine ⟨34161004890413368278575237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22774003260275578852383491 34161004890413368278575237)
              ·
                refine ⟨6405188416952506552232857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34161004890413368278575237 6405188416952506552232857)
                ·
                  refine ⟨4803891312714379914174643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6405188416952506552232857 4803891312714379914174643)
                  ·
                    refine ⟨7205836969071569871261965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4803891312714379914174643 7205836969071569871261965)
                    ·
                      refine ⟨2702188863401838701723237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7205836969071569871261965 2702188863401838701723237)
                      ·
                        rfl

theorem cell23_5262494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_5262494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262494 prefixEnd_5262494 := by exact prefixLift 5262494
  have htrace : WordTrace (prefixWord ++ tailWord_5262494) baseStart_5262494 baseEnd_5262494 := by
    simpa [prefixWord, tailWord_5262494, baseEnd_5262494] using wordTrace_append hprefix tailTrace_5262494
  have hstable : (prefixWord ++ tailWord_5262494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262494).length < 2 ^ (prefixWord ++ tailWord_5262494).sum := by decide
  have hdescent : baseEnd_5262494 < baseStart_5262494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262495 : List Nat := [1, 1, 2, 6, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5262495 : Nat := 118140960795 + 5262495 * 2 ^ 59
def prefixEnd_5262495 : Nat := 4983230072969 + 3 ^ 40 * 5262495 * 2
def baseEnd_5262495 : Nat := 2702189376882493197810733

theorem tailTrace_5262495 : CollatzResearch.WordTrace tailWord_5262495 prefixEnd_5262495 2702189376882493197810733 := by
  unfold tailWord_5262495
  simp only [CollatzResearch.WordTrace]
  refine ⟨191938961069886852436964939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127959307379924568291309959 191938961069886852436964939)
  ·
    refine ⟨287908441604830278655447409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191938961069886852436964939 287908441604830278655447409)
    ·
      refine ⟨215931331203622708991585557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287908441604830278655447409 215931331203622708991585557)
      ·
        refine ⟨10121781150169814483980573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 215931331203622708991585557 10121781150169814483980573)
        ·
          refine ⟨3795667931313680431492715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10121781150169814483980573 3795667931313680431492715)
          ·
            refine ⟨5693501896970520647239073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795667931313680431492715 5693501896970520647239073)
            ·
              refine ⟨4270126422727890485429305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5693501896970520647239073 4270126422727890485429305)
              ·
                refine ⟨3202594817045917864071979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4270126422727890485429305 3202594817045917864071979)
                ·
                  refine ⟨4803892225568876796107969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202594817045917864071979 4803892225568876796107969)
                  ·
                    refine ⟨3602919169176657597080977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803892225568876796107969 3602919169176657597080977)
                    ·
                      refine ⟨2702189376882493197810733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3602919169176657597080977 2702189376882493197810733)
                      ·
                        rfl

theorem cell23_5262495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5262495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262495 prefixEnd_5262495 := by exact prefixLift 5262495
  have htrace : WordTrace (prefixWord ++ tailWord_5262495) baseStart_5262495 baseEnd_5262495 := by
    simpa [prefixWord, tailWord_5262495, baseEnd_5262495] using wordTrace_append hprefix tailTrace_5262495
  have hstable : (prefixWord ++ tailWord_5262495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262495).length < 2 ^ (prefixWord ++ tailWord_5262495).sum := by decide
  have hdescent : baseEnd_5262495 < baseStart_5262495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262533 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_5262533 : Nat := 118140960795 + 5262533 * 2 ^ 59
def prefixEnd_5262533 : Nat := 4983230072969 + 3 ^ 40 * 5262533 * 2
def baseEnd_5262533 : Nat := 2702208889147364049135557

theorem tailTrace_5262533 : CollatzResearch.WordTrace tailWord_5262533 prefixEnd_5262533 2702208889147364049135557 := by
  unfold tailWord_5262533
  simp only [CollatzResearch.WordTrace]
  refine ⟨191940347043749184926848253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127960231362499456617898835 191940347043749184926848253)
  ·
    refine ⟨71977630141405944347568095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191940347043749184926848253 71977630141405944347568095)
    ·
      refine ⟨107966445212108916521352143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71977630141405944347568095 107966445212108916521352143)
      ·
        refine ⟨161949667818163374782028215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107966445212108916521352143 161949667818163374782028215)
        ·
          refine ⟨242924501727245062173042323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161949667818163374782028215 242924501727245062173042323)
          ·
            refine ⟨364386752590867593259563485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242924501727245062173042323 364386752590867593259563485)
            ·
              refine ⟨136645032221575347472336307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364386752590867593259563485 136645032221575347472336307)
              ·
                refine ⟨204967548332363021208504461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136645032221575347472336307 204967548332363021208504461)
                ·
                  refine ⟨76862830624636132953189173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204967548332363021208504461 76862830624636132953189173)
                  ·
                    refine ⟨7205890371059637464361485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76862830624636132953189173 7205890371059637464361485)
                    ·
                      refine ⟨2702208889147364049135557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7205890371059637464361485 2702208889147364049135557)
                      ·
                        rfl

theorem cell23_5262533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_5262533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262533 prefixEnd_5262533 := by exact prefixLift 5262533
  have htrace : WordTrace (prefixWord ++ tailWord_5262533) baseStart_5262533 baseEnd_5262533 := by
    simpa [prefixWord, tailWord_5262533, baseEnd_5262533] using wordTrace_append hprefix tailTrace_5262533
  have hstable : (prefixWord ++ tailWord_5262533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262533).length < 2 ^ (prefixWord ++ tailWord_5262533).sum := by decide
  have hdescent : baseEnd_5262533 < baseStart_5262533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262553 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 4, 5]
def baseStart_5262553 : Nat := 118140960795 + 5262553 * 2 ^ 59
def prefixEnd_5262553 : Nat := 4983230072969 + 3 ^ 40 * 5262553 * 2
def baseEnd_5262553 : Nat := 900739719586817990295155

theorem tailTrace_5262553 : CollatzResearch.WordTrace tailWord_5262553 prefixEnd_5262553 900739719586817990295155 := by
  unfold tailWord_5262553
  simp only [CollatzResearch.WordTrace]
  refine ⟨191941076503676728342576313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127960717669117818895050875 191941076503676728342576313)
  ·
    refine ⟨143955807377757546256932235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191941076503676728342576313 143955807377757546256932235)
    ·
      refine ⟨215933711066636319385398353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143955807377757546256932235 215933711066636319385398353)
      ·
        refine ⟨161950283299977239539048765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215933711066636319385398353 161950283299977239539048765)
        ·
          refine ⟨60731356237491464827143287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161950283299977239539048765 60731356237491464827143287)
          ·
            refine ⟨91097034356237197240714931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60731356237491464827143287 91097034356237197240714931)
            ·
              refine ⟨136645551534355795861072397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91097034356237197240714931 136645551534355795861072397)
              ·
                refine ⟨51242081825383423447902149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136645551534355795861072397 51242081825383423447902149)
                ·
                  refine ⟨9607890342259391896481653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51242081825383423447902149 9607890342259391896481653)
                  ·
                    refine ⟨900739719586817990295155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9607890342259391896481653 900739719586817990295155)
                    ·
                      rfl

theorem cell23_5262553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_5262553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262553 prefixEnd_5262553 := by exact prefixLift 5262553
  have htrace : WordTrace (prefixWord ++ tailWord_5262553) baseStart_5262553 baseEnd_5262553 := by
    simpa [prefixWord, tailWord_5262553, baseEnd_5262553] using wordTrace_append hprefix tailTrace_5262553
  have hstable : (prefixWord ++ tailWord_5262553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262553).length < 2 ^ (prefixWord ++ tailWord_5262553).sum := by decide
  have hdescent : baseEnd_5262553 < baseStart_5262553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262557 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 7]
def baseStart_5262557 : Nat := 118140960795 + 5262557 * 2 ^ 59
def prefixEnd_5262557 : Nat := 4983230072969 + 3 ^ 40 * 5262557 * 2
def baseEnd_5262557 : Nat := 300246801409230217248383

theorem tailTrace_5262557 : CollatzResearch.WordTrace tailWord_5262557 prefixEnd_5262557 300246801409230217248383 := by
  unfold tailWord_5262557
  simp only [CollatzResearch.WordTrace]
  refine ⟨191941222395662237025721925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127960814930441491350481283 191941222395662237025721925)
  ·
    refine ⟨35988979199186669442322861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191941222395662237025721925 35988979199186669442322861)
    ·
      refine ⟨13495867199695001040871073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35988979199186669442322861 13495867199695001040871073)
      ·
        refine ⟨10121900399771250780653305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13495867199695001040871073 10121900399771250780653305)
        ·
          refine ⟨7591425299828438085489979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10121900399771250780653305 7591425299828438085489979)
          ·
            refine ⟨11387137949742657128234969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7591425299828438085489979 11387137949742657128234969)
            ·
              refine ⟨8540353462306992846176227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11387137949742657128234969 8540353462306992846176227)
              ·
                refine ⟨12810530193460489269264341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8540353462306992846176227 12810530193460489269264341)
                ·
                  refine ⟨300246801409230217248383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12810530193460489269264341 300246801409230217248383)
                  ·
                    rfl

theorem cell23_5262557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_5262557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262557 prefixEnd_5262557 := by exact prefixLift 5262557
  have htrace : WordTrace (prefixWord ++ tailWord_5262557) baseStart_5262557 baseEnd_5262557 := by
    simpa [prefixWord, tailWord_5262557, baseEnd_5262557] using wordTrace_append hprefix tailTrace_5262557
  have hstable : (prefixWord ++ tailWord_5262557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262557).length < 2 ^ (prefixWord ++ tailWord_5262557).sum := by decide
  have hdescent : baseEnd_5262557 < baseStart_5262557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262644 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_5262644 : Nat := 118140960795 + 5262644 * 2 ^ 59
def prefixEnd_5262644 : Nat := 4983230072969 + 3 ^ 40 * 5262644 * 2
def baseEnd_5262644 : Nat := 2702265885500013114847547

theorem tailTrace_5262644 : CollatzResearch.WordTrace tailWord_5262644 prefixEnd_5262644 2702265885500013114847547 := by
  unfold tailWord_5262644
  simp only [CollatzResearch.WordTrace]
  refine ⟨95972197773173525442069493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127962930364231367256092657 95972197773173525442069493)
  ·
    refine ⟨8997393541235018010194015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95972197773173525442069493 8997393541235018010194015)
    ·
      refine ⟨13496090311852527015291023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8997393541235018010194015 13496090311852527015291023)
      ·
        refine ⟨20244135467778790522936535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13496090311852527015291023 20244135467778790522936535)
        ·
          refine ⟨30366203201668185784404803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20244135467778790522936535 30366203201668185784404803)
          ·
            refine ⟨45549304802502278676607205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30366203201668185784404803 45549304802502278676607205)
            ·
              refine ⟨8540494650469177251863851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45549304802502278676607205 8540494650469177251863851)
              ·
                refine ⟨12810741975703765877795777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8540494650469177251863851 12810741975703765877795777)
                ·
                  refine ⟨9608056481777824408346833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12810741975703765877795777 9608056481777824408346833)
                  ·
                    refine ⟨7206042361333368306260125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9608056481777824408346833 7206042361333368306260125)
                    ·
                      refine ⟨2702265885500013114847547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7206042361333368306260125 2702265885500013114847547)
                      ·
                        rfl

theorem cell23_5262644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_5262644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262644 prefixEnd_5262644 := by exact prefixLift 5262644
  have htrace : WordTrace (prefixWord ++ tailWord_5262644) baseStart_5262644 baseEnd_5262644 := by
    simpa [prefixWord, tailWord_5262644, baseEnd_5262644] using wordTrace_append hprefix tailTrace_5262644
  have hstable : (prefixWord ++ tailWord_5262644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262644).length < 2 ^ (prefixWord ++ tailWord_5262644).sum := by decide
  have hdescent : baseEnd_5262644 < baseStart_5262644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262680 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_5262680 : Nat := 118140960795 + 5262680 * 2 ^ 59
def prefixEnd_5262680 : Nat := 4983230072969 + 3 ^ 40 * 5262680 * 2
def baseEnd_5262680 : Nat := 2702284370803574973997381

theorem tailTrace_5262680 : CollatzResearch.WordTrace tailWord_5262680 prefixEnd_5262680 2702284370803574973997381 := by
  unfold tailWord_5262680
  simp only [CollatzResearch.WordTrace]
  refine ⟨95972854287108314516224747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127963805716144419354966329 95972854287108314516224747)
  ·
    refine ⟨143959281430662471774337121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95972854287108314516224747 143959281430662471774337121)
    ·
      refine ⟨107969461072996853830752841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143959281430662471774337121 107969461072996853830752841)
      ·
        refine ⟨80977095804747640373064631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107969461072996853830752841 80977095804747640373064631)
        ·
          refine ⟨121465643707121460559596947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80977095804747640373064631 121465643707121460559596947)
          ·
            refine ⟨182198465560682190839395421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121465643707121460559596947 182198465560682190839395421)
            ·
              refine ⟨68324424585255821564773283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182198465560682190839395421 68324424585255821564773283)
              ·
                refine ⟨102486636877883732347159925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68324424585255821564773283 102486636877883732347159925)
                ·
                  refine ⟨9608122207301599907546243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102486636877883732347159925 9608122207301599907546243)
                  ·
                    refine ⟨14412183310952399861319365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9608122207301599907546243 14412183310952399861319365)
                    ·
                      refine ⟨2702284370803574973997381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14412183310952399861319365 2702284370803574973997381)
                      ·
                        rfl

theorem cell23_5262680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_5262680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262680 prefixEnd_5262680 := by exact prefixLift 5262680
  have htrace : WordTrace (prefixWord ++ tailWord_5262680) baseStart_5262680 baseEnd_5262680 := by
    simpa [prefixWord, tailWord_5262680, baseEnd_5262680] using wordTrace_append hprefix tailTrace_5262680
  have hstable : (prefixWord ++ tailWord_5262680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262680).length < 2 ^ (prefixWord ++ tailWord_5262680).sum := by decide
  have hdescent : baseEnd_5262680 < baseStart_5262680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262701 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_5262701 : Nat := 118140960795 + 5262701 * 2 ^ 59
def prefixEnd_5262701 : Nat := 4983230072969 + 3 ^ 40 * 5262701 * 2
def baseEnd_5262701 : Nat := 2702295153897319391834785

theorem tailTrace_5262701 : CollatzResearch.WordTrace tailWord_5262701 prefixEnd_5262701 2702295153897319391834785 := by
  unfold tailWord_5262701
  simp only [CollatzResearch.WordTrace]
  refine ⟨191946474507140549618963957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127964316338093699745975971 191946474507140549618963957)
  ·
    refine ⟨17994981985044426526777871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191946474507140549618963957 17994981985044426526777871)
    ·
      refine ⟨26992472977566639790166807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17994981985044426526777871 26992472977566639790166807)
      ·
        refine ⟨40488709466349959685250211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26992472977566639790166807 40488709466349959685250211)
        ·
          refine ⟨60733064199524939527875317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40488709466349959685250211 60733064199524939527875317)
          ·
            refine ⟨5693724768705463080738311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60733064199524939527875317 5693724768705463080738311)
            ·
              refine ⟨8540587153058194621107467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693724768705463080738311 8540587153058194621107467)
              ·
                refine ⟨12810880729587291931661201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8540587153058194621107467 12810880729587291931661201)
                ·
                  refine ⟨9608160547190468948745901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12810880729587291931661201 9608160547190468948745901)
                  ·
                    refine ⟨3603060205196425855779713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9608160547190468948745901 3603060205196425855779713)
                    ·
                      refine ⟨2702295153897319391834785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603060205196425855779713 2702295153897319391834785)
                      ·
                        rfl

theorem cell23_5262701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_5262701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262701 prefixEnd_5262701 := by exact prefixLift 5262701
  have htrace : WordTrace (prefixWord ++ tailWord_5262701) baseStart_5262701 baseEnd_5262701 := by
    simpa [prefixWord, tailWord_5262701, baseEnd_5262701] using wordTrace_append hprefix tailTrace_5262701
  have hstable : (prefixWord ++ tailWord_5262701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262701).length < 2 ^ (prefixWord ++ tailWord_5262701).sum := by decide
  have hdescent : baseEnd_5262701 < baseStart_5262701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262724 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_5262724 : Nat := 118140960795 + 5262724 * 2 ^ 59
def prefixEnd_5262724 : Nat := 4983230072969 + 3 ^ 40 * 5262724 * 2
def baseEnd_5262724 : Nat := 900768987984124267282393

theorem tailTrace_5262724 : CollatzResearch.WordTrace tailWord_5262724 prefixEnd_5262724 900768987984124267282393 := by
  unfold tailWord_5262724
  simp only [CollatzResearch.WordTrace]
  refine ⟨95973656693028612273525613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127964875590704816364700817 95973656693028612273525613)
  ·
    refine ⟨35990121259885729602572105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95973656693028612273525613 35990121259885729602572105)
    ·
      refine ⟨26992590944914297201929079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35990121259885729602572105 26992590944914297201929079)
      ·
        refine ⟨40488886417371445802893619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26992590944914297201929079 40488886417371445802893619)
        ·
          refine ⟨60733329626057168704340429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40488886417371445802893619 60733329626057168704340429)
          ·
            refine ⟨22774998609771438264127661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60733329626057168704340429 22774998609771438264127661)
            ·
              refine ⟨8540624478664289349047873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22774998609771438264127661 8540624478664289349047873)
              ·
                refine ⟨6405468358998217011785905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8540624478664289349047873 6405468358998217011785905)
                ·
                  refine ⟨4804101269248662758839429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6405468358998217011785905 4804101269248662758839429)
                  ·
                    refine ⟨900768987984124267282393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804101269248662758839429 900768987984124267282393)
                    ·
                      rfl

theorem cell23_5262724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_5262724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262724 prefixEnd_5262724 := by exact prefixLift 5262724
  have htrace : WordTrace (prefixWord ++ tailWord_5262724) baseStart_5262724 baseEnd_5262724 := by
    simpa [prefixWord, tailWord_5262724, baseEnd_5262724] using wordTrace_append hprefix tailTrace_5262724
  have hstable : (prefixWord ++ tailWord_5262724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262724).length < 2 ^ (prefixWord ++ tailWord_5262724).sum := by decide
  have hdescent : baseEnd_5262724 < baseStart_5262724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262731 : List Nat := [1, 1, 1, 1, 4, 3, 1, 6, 1, 2, 2]
def baseStart_5262731 : Nat := 118140960795 + 5262731 * 2 ^ 59
def prefixEnd_5262731 : Nat := 4983230072969 + 3 ^ 40 * 5262731 * 2
def baseEnd_5262731 : Nat := 2702310558316954274459647

theorem tailTrace_5262731 : CollatzResearch.WordTrace tailWord_5262731 prefixEnd_5262731 2702310558316954274459647 := by
  unfold tailWord_5262731
  simp only [CollatzResearch.WordTrace]
  refine ⟨191947568697031864742556047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127965045798021243161704031 191947568697031864742556047)
  ·
    refine ⟨287921353045547797113834071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191947568697031864742556047 287921353045547797113834071)
    ·
      refine ⟨431882029568321695670751107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287921353045547797113834071 431882029568321695670751107)
      ·
        refine ⟨647823044352482543506126661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431882029568321695670751107 647823044352482543506126661)
        ·
          refine ⟨121466820816090476907398749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 647823044352482543506126661 121466820816090476907398749)
          ·
            refine ⟨45550057806033928840274531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121466820816090476907398749 45550057806033928840274531)
            ·
              refine ⟨68325086709050893260411797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45550057806033928840274531 68325086709050893260411797)
              ·
                refine ⟨3202738439486760621581803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68325086709050893260411797 3202738439486760621581803)
                ·
                  refine ⟨4804107659230140932372705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202738439486760621581803 4804107659230140932372705)
                  ·
                    refine ⟨3603080744422605699279529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4804107659230140932372705 3603080744422605699279529)
                    ·
                      refine ⟨2702310558316954274459647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603080744422605699279529 2702310558316954274459647)
                      ·
                        rfl

theorem cell23_5262731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 2, 2].length) (baseStart_5262731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262731 prefixEnd_5262731 := by exact prefixLift 5262731
  have htrace : WordTrace (prefixWord ++ tailWord_5262731) baseStart_5262731 baseEnd_5262731 := by
    simpa [prefixWord, tailWord_5262731, baseEnd_5262731] using wordTrace_append hprefix tailTrace_5262731
  have hstable : (prefixWord ++ tailWord_5262731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262731).length < 2 ^ (prefixWord ++ tailWord_5262731).sum := by decide
  have hdescent : baseEnd_5262731 < baseStart_5262731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262734 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5262734 : Nat := 118140960795 + 5262734 * 2 ^ 59
def prefixEnd_5262734 : Nat := 4983230072969 + 3 ^ 40 * 5262734 * 2
def baseEnd_5262734 : Nat := 2702312098758917762722133

theorem tailTrace_5262734 : CollatzResearch.WordTrace tailWord_5262734 prefixEnd_5262734 2702312098758917762722133 := by
  unfold tailWord_5262734
  simp only [CollatzResearch.WordTrace]
  refine ⟨23993459764502624531864407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127965118744013997503276837 23993459764502624531864407)
  ·
    refine ⟨35990189646753936797796611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23993459764502624531864407 35990189646753936797796611)
    ·
      refine ⟨53985284470130905196694917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35990189646753936797796611 53985284470130905196694917)
      ·
        refine ⟨10122240838149544724380297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53985284470130905196694917 10122240838149544724380297)
        ·
          refine ⟨7591680628612158543285223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10122240838149544724380297 7591680628612158543285223)
          ·
            refine ⟨11387520942918237814927835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7591680628612158543285223 11387520942918237814927835)
            ·
              refine ⟨17081281414377356722391753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11387520942918237814927835 17081281414377356722391753)
              ·
                refine ⟨12810961060783017541793815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17081281414377356722391753 12810961060783017541793815)
                ·
                  refine ⟨19216441591174526312690723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12810961060783017541793815 19216441591174526312690723)
                  ·
                    refine ⟨28824662386761789469036085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19216441591174526312690723 28824662386761789469036085)
                    ·
                      refine ⟨2702312098758917762722133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28824662386761789469036085 2702312098758917762722133)
                      ·
                        rfl

theorem cell23_5262734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5262734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262734 prefixEnd_5262734 := by exact prefixLift 5262734
  have htrace : WordTrace (prefixWord ++ tailWord_5262734) baseStart_5262734 baseEnd_5262734 := by
    simpa [prefixWord, tailWord_5262734, baseEnd_5262734] using wordTrace_append hprefix tailTrace_5262734
  have hstable : (prefixWord ++ tailWord_5262734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262734).length < 2 ^ (prefixWord ++ tailWord_5262734).sum := by decide
  have hdescent : baseEnd_5262734 < baseStart_5262734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262754 : List Nat := [3, 3, 1, 2, 1, 4, 2, 7]
def baseStart_5262754 : Nat := 118140960795 + 5262754 * 2 ^ 59
def prefixEnd_5262754 : Nat := 4983230072969 + 3 ^ 40 * 5262754 * 2
def baseEnd_5262754 : Nat := 100086013643407692017483

theorem tailTrace_5262754 : CollatzResearch.WordTrace tailWord_5262754 prefixEnd_5262754 100086013643407692017483 := by
  unfold tailWord_5262754
  simp only [CollatzResearch.WordTrace]
  refine ⟨47987101893987134917660829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127965605050632359780428877 47987101893987134917660829)
  ·
    refine ⟨17995163210245175594122811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47987101893987134917660829 17995163210245175594122811)
    ·
      refine ⟨26992744815367763391184217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17995163210245175594122811 26992744815367763391184217)
      ·
        refine ⟨20244558611525822543388163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26992744815367763391184217 20244558611525822543388163)
        ·
          refine ⟨30366837917288733815082245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20244558611525822543388163 30366837917288733815082245)
          ·
            refine ⟨5693782109491637590327921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30366837917288733815082245 5693782109491637590327921)
            ·
              refine ⟨4270336582118728192745941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5693782109491637590327921 4270336582118728192745941)
              ·
                refine ⟨100086013643407692017483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4270336582118728192745941 100086013643407692017483)
                ·
                  rfl

theorem cell23_5262754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 7].length) (baseStart_5262754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262754 prefixEnd_5262754 := by exact prefixLift 5262754
  have htrace : WordTrace (prefixWord ++ tailWord_5262754) baseStart_5262754 baseEnd_5262754 := by
    simpa [prefixWord, tailWord_5262754, baseEnd_5262754] using wordTrace_append hprefix tailTrace_5262754
  have hstable : (prefixWord ++ tailWord_5262754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262754).length < 2 ^ (prefixWord ++ tailWord_5262754).sum := by decide
  have hdescent : baseEnd_5262754 < baseStart_5262754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262765 : List Nat := [1, 5, 2, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_5262765 : Nat := 118140960795 + 5262765 * 2 ^ 59
def prefixEnd_5262765 : Nat := 4983230072969 + 3 ^ 40 * 5262765 * 2
def baseEnd_5262765 : Nat := 2702328016659207141434491

theorem tailTrace_5262765 : CollatzResearch.WordTrace tailWord_5262765 prefixEnd_5262765 2702328016659207141434491 := by
  unfold tailWord_5262765
  simp only [CollatzResearch.WordTrace]
  refine ⟨191948808778908688549293749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127965872519272459032862499 191948808778908688549293749)
  ·
    refine ⟨17995200823022689551496289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191948808778908688549293749 17995200823022689551496289)
    ·
      refine ⟨13496400617267017163622217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17995200823022689551496289 13496400617267017163622217)
      ·
        refine ⟨10122300462950262872716663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13496400617267017163622217 10122300462950262872716663)
        ·
          refine ⟨15183450694425394309074995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10122300462950262872716663 15183450694425394309074995)
          ·
            refine ⟨22775176041638091463612493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15183450694425394309074995 22775176041638091463612493)
            ·
              refine ⟨8540691015614284298854685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22775176041638091463612493 8540691015614284298854685)
              ·
                refine ⟨3202759130855356612070507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8540691015614284298854685 3202759130855356612070507)
                ·
                  refine ⟨4804138696283034918105761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202759130855356612070507 4804138696283034918105761)
                  ·
                    refine ⟨3603104022212276188579321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4804138696283034918105761 3603104022212276188579321)
                    ·
                      refine ⟨2702328016659207141434491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603104022212276188579321 2702328016659207141434491)
                      ·
                        rfl

theorem cell23_5262765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_5262765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262765 prefixEnd_5262765 := by exact prefixLift 5262765
  have htrace : WordTrace (prefixWord ++ tailWord_5262765) baseStart_5262765 baseEnd_5262765 := by
    simpa [prefixWord, tailWord_5262765, baseEnd_5262765] using wordTrace_append hprefix tailTrace_5262765
  have hstable : (prefixWord ++ tailWord_5262765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262765).length < 2 ^ (prefixWord ++ tailWord_5262765).sum := by decide
  have hdescent : baseEnd_5262765 < baseStart_5262765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262821 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 1, 4, 2]
def baseStart_5262821 : Nat := 118140960795 + 5262821 * 2 ^ 59
def prefixEnd_5262821 : Nat := 4983230072969 + 3 ^ 40 * 5262821 * 2
def baseEnd_5262821 : Nat := 2702356771575858922334233

theorem tailTrace_5262821 : CollatzResearch.WordTrace tailWord_5262821 prefixEnd_5262821 2702356771575858922334233 := by
  unfold tailWord_5262821
  simp only [CollatzResearch.WordTrace]
  refine ⟨191950851266705810113332317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127967234177803873408888211 191950851266705810113332317)
  ·
    refine ⟨71981569225014678792499619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191950851266705810113332317 71981569225014678792499619)
    ·
      refine ⟨107972353837522018188749429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71981569225014678792499619 107972353837522018188749429)
      ·
        refine ⟨10122408172267689205195259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107972353837522018188749429 10122408172267689205195259)
        ·
          refine ⟨15183612258401533807792889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10122408172267689205195259 15183612258401533807792889)
          ·
            refine ⟨11387709193801150355844667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15183612258401533807792889 11387709193801150355844667)
            ·
              refine ⟨17081563790701725533767001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11387709193801150355844667 17081563790701725533767001)
              ·
                refine ⟨12811172843026294150325251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17081563790701725533767001 12811172843026294150325251)
                ·
                  refine ⟨19216759264539441225487877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12811172843026294150325251 19216759264539441225487877)
                  ·
                    refine ⟨3603142362101145229778977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19216759264539441225487877 3603142362101145229778977)
                    ·
                      refine ⟨2702356771575858922334233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603142362101145229778977 2702356771575858922334233)
                      ·
                        rfl

theorem cell23_5262821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_5262821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262821 prefixEnd_5262821 := by exact prefixLift 5262821
  have htrace : WordTrace (prefixWord ++ tailWord_5262821) baseStart_5262821 baseEnd_5262821 := by
    simpa [prefixWord, tailWord_5262821, baseEnd_5262821] using wordTrace_append hprefix tailTrace_5262821
  have hstable : (prefixWord ++ tailWord_5262821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262821).length < 2 ^ (prefixWord ++ tailWord_5262821).sum := by decide
  have hdescent : baseEnd_5262821 < baseStart_5262821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262838 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_5262838 : Nat := 118140960795 + 5262838 * 2 ^ 59
def prefixEnd_5262838 : Nat := 4983230072969 + 3 ^ 40 * 5262838 * 2
def baseEnd_5262838 : Nat := 2702365500746985355821655

theorem tailTrace_5262838 : CollatzResearch.WordTrace tailWord_5262838 prefixEnd_5262838 2702365500746985355821655 := by
  unfold tailWord_5262838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11996966956727763876043823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127967647538429481344467445 11996966956727763876043823)
  ·
    refine ⟨17995450435091645814065735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11996966956727763876043823 17995450435091645814065735)
    ·
      refine ⟨26993175652637468721098603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17995450435091645814065735 26993175652637468721098603)
      ·
        refine ⟨40489763478956203081647905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26993175652637468721098603 40489763478956203081647905)
        ·
          refine ⟨30367322609217152311235929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40489763478956203081647905 30367322609217152311235929)
          ·
            refine ⟨22775491956912864233426947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30367322609217152311235929 22775491956912864233426947)
            ·
              refine ⟨34163237935369296350140421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22775491956912864233426947 34163237935369296350140421)
              ·
                refine ⟨6405607112881743065651329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34163237935369296350140421 6405607112881743065651329)
                ·
                  refine ⟨4804205334661307299238497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6405607112881743065651329 4804205334661307299238497)
                  ·
                    refine ⟨3603154000995980474428873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4804205334661307299238497 3603154000995980474428873)
                    ·
                      refine ⟨2702365500746985355821655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603154000995980474428873 2702365500746985355821655)
                      ·
                        rfl

theorem cell23_5262838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_5262838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262838 prefixEnd_5262838 := by exact prefixLift 5262838
  have htrace : WordTrace (prefixWord ++ tailWord_5262838) baseStart_5262838 baseEnd_5262838 := by
    simpa [prefixWord, tailWord_5262838, baseEnd_5262838] using wordTrace_append hprefix tailTrace_5262838
  have hstable : (prefixWord ++ tailWord_5262838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262838).length < 2 ^ (prefixWord ++ tailWord_5262838).sum := by decide
  have hdescent : baseEnd_5262838 < baseStart_5262838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262904 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 3, 4]
def baseStart_5262904 : Nat := 118140960795 + 5262904 * 2 ^ 59
def prefixEnd_5262904 : Nat := 4983230072969 + 3 ^ 40 * 5262904 * 2
def baseEnd_5262904 : Nat := 900799796823394032532117

theorem tailTrace_5262904 : CollatzResearch.WordTrace tailWord_5262904 prefixEnd_5262904 900799796823394032532117 := by
  unfold tailWord_5262904
  simp only [CollatzResearch.WordTrace]
  refine ⟨95976939262702557644301883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127969252350270076859069177 95976939262702557644301883)
  ·
    refine ⟨143965408894053836466452825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95976939262702557644301883 143965408894053836466452825)
    ·
      refine ⟨107974056670540377349839619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143965408894053836466452825 107974056670540377349839619)
      ·
        refine ⟨161961085005810566024759429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107974056670540377349839619 161961085005810566024759429)
        ·
          refine ⟨30367703438589481129642393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161961085005810566024759429 30367703438589481129642393)
          ·
            refine ⟨22775777578942110847231795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30367703438589481129642393 22775777578942110847231795)
            ·
              refine ⟨34163666368413166270847693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22775777578942110847231795 34163666368413166270847693)
              ·
                refine ⟨12811374888154937351567885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34163666368413166270847693 12811374888154937351567885)
                ·
                  refine ⟨4804265583058101506837957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12811374888154937351567885 4804265583058101506837957)
                  ·
                    refine ⟨900799796823394032532117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804265583058101506837957 900799796823394032532117)
                    ·
                      rfl

theorem cell23_5262904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_5262904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262904 prefixEnd_5262904 := by exact prefixLift 5262904
  have htrace : WordTrace (prefixWord ++ tailWord_5262904) baseStart_5262904 baseEnd_5262904 := by
    simpa [prefixWord, tailWord_5262904, baseEnd_5262904] using wordTrace_append hprefix tailTrace_5262904
  have hstable : (prefixWord ++ tailWord_5262904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262904).length < 2 ^ (prefixWord ++ tailWord_5262904).sum := by decide
  have hdescent : baseEnd_5262904 < baseStart_5262904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262927 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 3]
def baseStart_5262927 : Nat := 118140960795 + 5262927 * 2 ^ 59
def prefixEnd_5262927 : Nat := 4983230072969 + 3 ^ 40 * 5262927 * 2
def baseEnd_5262927 : Nat := 2702411200525235507608745

theorem tailTrace_5262927 : CollatzResearch.WordTrace tailWord_5262927 prefixEnd_5262927 2702411200525235507608745 := by
  unfold tailWord_5262927
  simp only [CollatzResearch.WordTrace]
  refine ⟨191954717404321790216691035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127969811602881193477794023 191954717404321790216691035)
  ·
    refine ⟨287932076106482685325036553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191954717404321790216691035 287932076106482685325036553)
    ·
      refine ⟨215949057079862013993777415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287932076106482685325036553 215949057079862013993777415)
      ·
        refine ⟨323923585619793020990666123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215949057079862013993777415 323923585619793020990666123)
        ·
          refine ⟨485885378429689531485999185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323923585619793020990666123 485885378429689531485999185)
          ·
            refine ⟨364414033822267148614499389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485885378429689531485999185 364414033822267148614499389)
            ·
              refine ⟨136655262683350180730437271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364414033822267148614499389 136655262683350180730437271)
              ·
                refine ⟨204982894025025271095655907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136655262683350180730437271 204982894025025271095655907)
                ·
                  refine ⟨307474341037537906643483861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204982894025025271095655907 307474341037537906643483861)
                  ·
                    refine ⟨7206429868067294686956653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 307474341037537906643483861 7206429868067294686956653)
                    ·
                      refine ⟨2702411200525235507608745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7206429868067294686956653 2702411200525235507608745)
                      ·
                        rfl

theorem cell23_5262927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_5262927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262927 prefixEnd_5262927 := by exact prefixLift 5262927
  have htrace : WordTrace (prefixWord ++ tailWord_5262927) baseStart_5262927 baseEnd_5262927 := by
    simpa [prefixWord, tailWord_5262927, baseEnd_5262927] using wordTrace_append hprefix tailTrace_5262927
  have hstable : (prefixWord ++ tailWord_5262927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262927).length < 2 ^ (prefixWord ++ tailWord_5262927).sum := by decide
  have hdescent : baseEnd_5262927 < baseStart_5262927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5262967 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_5262967 : Nat := 118140960795 + 5262967 * 2 ^ 59
def prefixEnd_5262967 : Nat := 4983230072969 + 3 ^ 40 * 5262967 * 2
def baseEnd_5262967 : Nat := 2702431739751415351108561

theorem tailTrace_5262967 : CollatzResearch.WordTrace tailWord_5262967 prefixEnd_5262967 2702431739751415351108561 := by
  unfold tailWord_5262967
  simp only [CollatzResearch.WordTrace]
  refine ⟨191956176324176877048147155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127970784216117918032098103 191956176324176877048147155)
  ·
    refine ⟨287934264486265315572220733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191956176324176877048147155 287934264486265315572220733)
    ·
      refine ⟨107975349182349493339582775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287934264486265315572220733 107975349182349493339582775)
      ·
        refine ⟨161963023773524240009374163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107975349182349493339582775 161963023773524240009374163)
        ·
          refine ⟨242944535660286360014061245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161963023773524240009374163 242944535660286360014061245)
          ·
            refine ⟨91104200872607385005272967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242944535660286360014061245 91104200872607385005272967)
            ·
              refine ⟨136656301308911077507909451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91104200872607385005272967 136656301308911077507909451)
              ·
                refine ⟨204984451963366616261864177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136656301308911077507909451 204984451963366616261864177)
                ·
                  refine ⟨153738338972524962196398133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204984451963366616261864177 153738338972524962196398133)
                  ·
                    refine ⟨14412969278674215205912325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153738338972524962196398133 14412969278674215205912325)
                    ·
                      refine ⟨2702431739751415351108561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14412969278674215205912325 2702431739751415351108561)
                      ·
                        rfl

theorem cell23_5262967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_5262967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5262967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5262967 prefixEnd_5262967 := by exact prefixLift 5262967
  have htrace : WordTrace (prefixWord ++ tailWord_5262967) baseStart_5262967 baseEnd_5262967 := by
    simpa [prefixWord, tailWord_5262967, baseEnd_5262967] using wordTrace_append hprefix tailTrace_5262967
  have hstable : (prefixWord ++ tailWord_5262967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5262967).length < 2 ^ (prefixWord ++ tailWord_5262967).sum := by decide
  have hdescent : baseEnd_5262967 < baseStart_5262967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5262967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263001 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 7, 2, 2]
def baseStart_5263001 : Nat := 118140960795 + 5263001 * 2 ^ 59
def prefixEnd_5263001 : Nat := 4983230072969 + 3 ^ 40 * 5263001 * 2
def baseEnd_5263001 : Nat := 2702449198093668218083405

theorem tailTrace_5263001 : CollatzResearch.WordTrace tailWord_5263001 prefixEnd_5263001 2702449198093668218083405 := by
  unfold tailWord_5263001
  simp only [CollatzResearch.WordTrace]
  refine ⟨191957416406053700854884857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127971610937369133903256571 191957416406053700854884857)
  ·
    refine ⟨143968062304540275641163643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191957416406053700854884857 143968062304540275641163643)
    ·
      refine ⟨215952093456810413461745465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143968062304540275641163643 215952093456810413461745465)
      ·
        refine ⟨161964070092607810096309099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215952093456810413461745465 161964070092607810096309099)
        ·
          refine ⟨242946105138911715144463649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161964070092607810096309099 242946105138911715144463649)
          ·
            refine ⟨182209578854183786358347737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242946105138911715144463649 182209578854183786358347737)
            ·
              refine ⟨136657184140637839768760803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182209578854183786358347737 136657184140637839768760803)
              ·
                refine ⟨204985776210956759653141205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136657184140637839768760803 204985776210956759653141205)
                ·
                  refine ⟨4804354129944299054370497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 204985776210956759653141205 4804354129944299054370497)
                  ·
                    refine ⟨3603265597458224290777873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4804354129944299054370497 3603265597458224290777873)
                    ·
                      refine ⟨2702449198093668218083405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603265597458224290777873 2702449198093668218083405)
                      ·
                        rfl

theorem cell23_5263001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_5263001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263001 prefixEnd_5263001 := by exact prefixLift 5263001
  have htrace : WordTrace (prefixWord ++ tailWord_5263001) baseStart_5263001 baseEnd_5263001 := by
    simpa [prefixWord, tailWord_5263001, baseEnd_5263001] using wordTrace_append hprefix tailTrace_5263001
  have hstable : (prefixWord ++ tailWord_5263001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263001).length < 2 ^ (prefixWord ++ tailWord_5263001).sum := by decide
  have hdescent : baseEnd_5263001 < baseStart_5263001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263011 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 2, 4]
def baseStart_5263011 : Nat := 118140960795 + 5263011 * 2 ^ 59
def prefixEnd_5263011 : Nat := 4983230072969 + 3 ^ 40 * 5263011 * 2
def baseEnd_5263011 : Nat := 900818110966737726319453

theorem tailTrace_5263011 : CollatzResearch.WordTrace tailWord_5263011 prefixEnd_5263011 900818110966737726319453 := by
  unfold tailWord_5263011
  simp only [CollatzResearch.WordTrace]
  refine ⟨191957781136017472562748887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127971854090678315041832591 191957781136017472562748887)
  ·
    refine ⟨287936671704026208844123331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191957781136017472562748887 287936671704026208844123331)
    ·
      refine ⟨431905007556039313266184997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287936671704026208844123331 431905007556039313266184997)
      ·
        refine ⟨80982188916757371237409687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 431905007556039313266184997 80982188916757371237409687)
        ·
          refine ⟨121473283375136056856114531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80982188916757371237409687 121473283375136056856114531)
          ·
            refine ⟨182209925062704085284171797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121473283375136056856114531 182209925062704085284171797)
            ·
              refine ⟨8541090237314253997695553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182209925062704085284171797 8541090237314253997695553)
              ·
                refine ⟨6405817677985690498271665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8541090237314253997695553 6405817677985690498271665)
                ·
                  refine ⟨4804363258489267873703749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6405817677985690498271665 4804363258489267873703749)
                  ·
                    refine ⟨900818110966737726319453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804363258489267873703749 900818110966737726319453)
                    ·
                      rfl

theorem cell23_5263011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 4].length) (baseStart_5263011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263011 prefixEnd_5263011 := by exact prefixLift 5263011
  have htrace : WordTrace (prefixWord ++ tailWord_5263011) baseStart_5263011 baseEnd_5263011 := by
    simpa [prefixWord, tailWord_5263011, baseEnd_5263011] using wordTrace_append hprefix tailTrace_5263011
  have hstable : (prefixWord ++ tailWord_5263011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263011).length < 2 ^ (prefixWord ++ tailWord_5263011).sum := by decide
  have hdescent : baseEnd_5263011 < baseStart_5263011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263012 : List Nat := [2, 3, 1, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_5263012 : Nat := 118140960795 + 5263012 * 2 ^ 59
def prefixEnd_5263012 : Nat := 4983230072969 + 3 ^ 40 * 5263012 * 2
def baseEnd_5263012 : Nat := 2702454846380867675045855

theorem tailTrace_5263012 : CollatzResearch.WordTrace tailWord_5263012 prefixEnd_5263012 2702454846380867675045855 := by
  unfold tailWord_5263012
  simp only [CollatzResearch.WordTrace]
  refine ⟨95978908804506924866767645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127971878406009233155690193 95978908804506924866767645)
  ·
    refine ⟨35992090801690096825037867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95978908804506924866767645 35992090801690096825037867)
    ·
      refine ⟨53988136202535145237556801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35992090801690096825037867 53988136202535145237556801)
      ·
        refine ⟨40491102151901358928167601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53988136202535145237556801 40491102151901358928167601)
        ·
          refine ⟨30368326613926019196125701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40491102151901358928167601 30368326613926019196125701)
          ·
            refine ⟨5694061240111128599273569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30368326613926019196125701 5694061240111128599273569)
            ·
              refine ⟨4270545930083346449455177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5694061240111128599273569 4270545930083346449455177)
              ·
                refine ⟨3202909447562509837091383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4270545930083346449455177 3202909447562509837091383)
                ·
                  refine ⟨4804364171343764755637075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202909447562509837091383 4804364171343764755637075)
                  ·
                    refine ⟨7206546257015647133455613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4804364171343764755637075 7206546257015647133455613)
                    ·
                      refine ⟨2702454846380867675045855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7206546257015647133455613 2702454846380867675045855)
                      ·
                        rfl

theorem cell23_5263012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_5263012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263012 prefixEnd_5263012 := by exact prefixLift 5263012
  have htrace : WordTrace (prefixWord ++ tailWord_5263012) baseStart_5263012 baseEnd_5263012 := by
    simpa [prefixWord, tailWord_5263012, baseEnd_5263012] using wordTrace_append hprefix tailTrace_5263012
  have hstable : (prefixWord ++ tailWord_5263012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263012).length < 2 ^ (prefixWord ++ tailWord_5263012).sum := by decide
  have hdescent : baseEnd_5263012 < baseStart_5263012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263021 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_5263021 : Nat := 118140960795 + 5263021 * 2 ^ 59
def prefixEnd_5263021 : Nat := 4983230072969 + 3 ^ 40 * 5263021 * 2
def baseEnd_5263021 : Nat := 2702459467706758139833313

theorem tailTrace_5263021 : CollatzResearch.WordTrace tailWord_5263021 prefixEnd_5263021 2702459467706758139833313 := by
  unfold tailWord_5263021
  simp only [CollatzResearch.WordTrace]
  refine ⟨191958145865981244270612917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127972097243987496180408611 191958145865981244270612917)
  ·
    refine ⟨17996076174935741650369961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191958145865981244270612917 17996076174935741650369961)
    ·
      refine ⟨13497057131201806237777471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17996076174935741650369961 13497057131201806237777471)
      ·
        refine ⟨20245585696802709356666207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13497057131201806237777471 20245585696802709356666207)
        ·
          refine ⟨30368378545204064034999311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20245585696802709356666207 30368378545204064034999311)
          ·
            refine ⟨45552567817806096052498967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30368378545204064034999311 45552567817806096052498967)
            ·
              refine ⟨68328851726709144078748451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45552567817806096052498967 68328851726709144078748451)
              ·
                refine ⟨102493277590063716118122677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68328851726709144078748451 102493277590063716118122677)
                ·
                  refine ⟨9608744774068473386074001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102493277590063716118122677 9608744774068473386074001)
                  ·
                    refine ⟨7206558580551355039555501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9608744774068473386074001 7206558580551355039555501)
                    ·
                      refine ⟨2702459467706758139833313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7206558580551355039555501 2702459467706758139833313)
                      ·
                        rfl

theorem cell23_5263021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_5263021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263021 prefixEnd_5263021 := by exact prefixLift 5263021
  have htrace : WordTrace (prefixWord ++ tailWord_5263021) baseStart_5263021 baseEnd_5263021 := by
    simpa [prefixWord, tailWord_5263021, baseEnd_5263021] using wordTrace_append hprefix tailTrace_5263021
  have hstable : (prefixWord ++ tailWord_5263021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263021).length < 2 ^ (prefixWord ++ tailWord_5263021).sum := by decide
  have hdescent : baseEnd_5263021 < baseStart_5263021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263031 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_5263031 : Nat := 118140960795 + 5263031 * 2 ^ 59
def prefixEnd_5263031 : Nat := 4983230072969 + 3 ^ 40 * 5263031 * 2
def baseEnd_5263031 : Nat := 2702464602513303100708267

theorem tailTrace_5263031 : CollatzResearch.WordTrace tailWord_5263031 prefixEnd_5263031 2702464602513303100708267 := by
  unfold tailWord_5263031
  simp only [CollatzResearch.WordTrace]
  refine ⟨191958510595945015978476947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127972340397296677318984631 191958510595945015978476947)
  ·
    refine ⟨287937765893917523967715421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191958510595945015978476947 287937765893917523967715421)
    ·
      refine ⟨107976662210219071487893283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287937765893917523967715421 107976662210219071487893283)
      ·
        refine ⟨161964993315328607231839925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107976662210219071487893283 161964993315328607231839925)
        ·
          refine ⟨15184218123312056927984993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161964993315328607231839925 15184218123312056927984993)
          ·
            refine ⟨11388163592484042695988745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15184218123312056927984993 11388163592484042695988745)
            ·
              refine ⟨8541122694363032021991559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11388163592484042695988745 8541122694363032021991559)
              ·
                refine ⟨12811684041544548032987339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8541122694363032021991559 12811684041544548032987339)
                ·
                  refine ⟨19217526062316822049481009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12811684041544548032987339 19217526062316822049481009)
                  ·
                    refine ⟨14413144546737616537110757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19217526062316822049481009 14413144546737616537110757)
                    ·
                      refine ⟨2702464602513303100708267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14413144546737616537110757 2702464602513303100708267)
                      ·
                        rfl

theorem cell23_5263031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_5263031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263031 prefixEnd_5263031 := by exact prefixLift 5263031
  have htrace : WordTrace (prefixWord ++ tailWord_5263031) baseStart_5263031 baseEnd_5263031 := by
    simpa [prefixWord, tailWord_5263031, baseEnd_5263031] using wordTrace_append hprefix tailTrace_5263031
  have hstable : (prefixWord ++ tailWord_5263031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263031).length < 2 ^ (prefixWord ++ tailWord_5263031).sum := by decide
  have hdescent : baseEnd_5263031 < baseStart_5263031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263052 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5263052 : Nat := 118140960795 + 5263052 * 2 ^ 59
def prefixEnd_5263052 : Nat := 4983230072969 + 3 ^ 40 * 5263052 * 2
def baseEnd_5263052 : Nat := 2702475385607047518545671

theorem tailTrace_5263052 : CollatzResearch.WordTrace tailWord_5263052 prefixEnd_5263052 2702475385607047518545671 := by
  unfold tailWord_5263052
  simp only [CollatzResearch.WordTrace]
  refine ⟨95979638264434468282495705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127972851019245957709994273 95979638264434468282495705)
  ·
    refine ⟨71984728698325851211871779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95979638264434468282495705 71984728698325851211871779)
    ·
      refine ⟨107977093047488776817807669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71984728698325851211871779 107977093047488776817807669)
      ·
        refine ⟨10122852473202072826669469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107977093047488776817807669 10122852473202072826669469)
        ·
          refine ⟨3796069677450777310001051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10122852473202072826669469 3796069677450777310001051)
          ·
            refine ⟨5694104516176165965001577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796069677450777310001051 5694104516176165965001577)
            ·
              refine ⟨4270578387132124473751183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5694104516176165965001577 4270578387132124473751183)
              ·
                refine ⟨6405867580698186710626775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4270578387132124473751183 6405867580698186710626775)
                ·
                  refine ⟨9608801371047280065940163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6405867580698186710626775 9608801371047280065940163)
                  ·
                    refine ⟨14413202056570920098910245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9608801371047280065940163 14413202056570920098910245)
                    ·
                      refine ⟨2702475385607047518545671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14413202056570920098910245 2702475385607047518545671)
                      ·
                        rfl

theorem cell23_5263052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5263052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263052 prefixEnd_5263052 := by exact prefixLift 5263052
  have htrace : WordTrace (prefixWord ++ tailWord_5263052) baseStart_5263052 baseEnd_5263052 := by
    simpa [prefixWord, tailWord_5263052, baseEnd_5263052] using wordTrace_append hprefix tailTrace_5263052
  have hstable : (prefixWord ++ tailWord_5263052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263052).length < 2 ^ (prefixWord ++ tailWord_5263052).sum := by decide
  have hdescent : baseEnd_5263052 < baseStart_5263052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263084 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_5263084 : Nat := 118140960795 + 5263084 * 2 ^ 59
def prefixEnd_5263084 : Nat := 4983230072969 + 3 ^ 40 * 5263084 * 2
def baseEnd_5263084 : Nat := 900830605662663797781841

theorem tailTrace_5263084 : CollatzResearch.WordTrace tailWord_5263084 prefixEnd_5263084 900830605662663797781841 := by
  unfold tailWord_5263084
  simp only [CollatzResearch.WordTrace]
  refine ⟨95980221832376503015078153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127973629109835337353437537 95980221832376503015078153)
  ·
    refine ⟨71985166374282377261308615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95980221832376503015078153 71985166374282377261308615)
    ·
      refine ⟨107977749561423565891962923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71985166374282377261308615 107977749561423565891962923)
      ·
        refine ⟨161966624342135348837944385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107977749561423565891962923 161966624342135348837944385)
        ·
          refine ⟨121474968256601511628458289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161966624342135348837944385 121474968256601511628458289)
          ·
            refine ⟨91106226192451133721343717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121474968256601511628458289 91106226192451133721343717)
            ·
              refine ⟨17082417411084587572751947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91106226192451133721343717 17082417411084587572751947)
              ·
                refine ⟨25623626116626881359127921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17082417411084587572751947 25623626116626881359127921)
                ·
                  refine ⟨19217719587470161019345941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25623626116626881359127921 19217719587470161019345941)
                  ·
                    refine ⟨900830605662663797781841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19217719587470161019345941 900830605662663797781841)
                    ·
                      rfl

theorem cell23_5263084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_5263084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263084 prefixEnd_5263084 := by exact prefixLift 5263084
  have htrace : WordTrace (prefixWord ++ tailWord_5263084) baseStart_5263084 baseEnd_5263084 := by
    simpa [prefixWord, tailWord_5263084, baseEnd_5263084] using wordTrace_append hprefix tailTrace_5263084
  have hstable : (prefixWord ++ tailWord_5263084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263084).length < 2 ^ (prefixWord ++ tailWord_5263084).sum := by decide
  have hdescent : baseEnd_5263084 < baseStart_5263084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263151 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 2, 5, 2]
def baseStart_5263151 : Nat := 118140960795 + 5263151 * 2 ^ 59
def prefixEnd_5263151 : Nat := 4983230072969 + 3 ^ 40 * 5263151 * 2
def baseEnd_5263151 : Nat := 2702526220191842631207715

theorem tailTrace_5263151 : CollatzResearch.WordTrace tailWord_5263151 prefixEnd_5263151 2702526220191842631207715 := by
  unfold tailWord_5263151
  simp only [CollatzResearch.WordTrace]
  refine ⟨191962887355510276472845307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127975258237006850981896871 191962887355510276472845307)
  ·
    refine ⟨287944331033265414709267961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191962887355510276472845307 287944331033265414709267961)
    ·
      refine ⟨215958248274949061031950971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287944331033265414709267961 215958248274949061031950971)
      ·
        refine ⟨323937372412423591547926457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215958248274949061031950971 323937372412423591547926457)
        ·
          refine ⟨242953029309317693660944843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323937372412423591547926457 242953029309317693660944843)
          ·
            refine ⟨364429543963976540491417265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242953029309317693660944843 364429543963976540491417265)
            ·
              refine ⟨273322157972982405368562949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364429543963976540491417265 273322157972982405368562949)
              ·
                refine ⟨51247904619934201006605553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273322157972982405368562949 51247904619934201006605553)
                ·
                  refine ⟨38435928464950650754954165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51247904619934201006605553 38435928464950650754954165)
                  ·
                    refine ⟨3603368293589123508276953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38435928464950650754954165 3603368293589123508276953)
                    ·
                      refine ⟨2702526220191842631207715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603368293589123508276953 2702526220191842631207715)
                      ·
                        rfl

theorem cell23_5263151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 5, 2].length) (baseStart_5263151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263151 prefixEnd_5263151 := by exact prefixLift 5263151
  have htrace : WordTrace (prefixWord ++ tailWord_5263151) baseStart_5263151 baseEnd_5263151 := by
    simpa [prefixWord, tailWord_5263151, baseEnd_5263151] using wordTrace_append hprefix tailTrace_5263151
  have hstable : (prefixWord ++ tailWord_5263151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263151).length < 2 ^ (prefixWord ++ tailWord_5263151).sum := by decide
  have hdescent : baseEnd_5263151 < baseStart_5263151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263184 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_5263184 : Nat := 118140960795 + 5263184 * 2 ^ 59
def prefixEnd_5263184 : Nat := 4983230072969 + 3 ^ 40 * 5263184 * 2
def baseEnd_5263184 : Nat := 2702543165053441002095063

theorem tailTrace_5263184 : CollatzResearch.WordTrace tailWord_5263184 prefixEnd_5263184 2702543165053441002095063 := by
  unfold tailWord_5263184
  simp only [CollatzResearch.WordTrace]
  refine ⟨95982045482195361554398303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127976060642927148739197737 95982045482195361554398303)
  ·
    refine ⟨143973068223293042331597455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95982045482195361554398303 143973068223293042331597455)
    ·
      refine ⟨215959602334939563497396183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143973068223293042331597455 215959602334939563497396183)
      ·
        refine ⟨323939403502409345246094275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215959602334939563497396183 323939403502409345246094275)
        ·
          refine ⟨485909105253614017869141413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323939403502409345246094275 485909105253614017869141413)
          ·
            refine ⟨91107957235052628350464015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 485909105253614017869141413 91107957235052628350464015)
            ·
              refine ⟨136661935852578942525696023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91107957235052628350464015 136661935852578942525696023)
              ·
                refine ⟨204992903778868413788544035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136661935852578942525696023 204992903778868413788544035)
                ·
                  refine ⟨307489355668302620682816053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204992903778868413788544035 307489355668302620682816053)
                  ·
                    refine ⟨28827127093903370689014005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 307489355668302620682816053 28827127093903370689014005)
                    ·
                      refine ⟨2702543165053441002095063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28827127093903370689014005 2702543165053441002095063)
                      ·
                        rfl

theorem cell23_5263184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_5263184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263184 prefixEnd_5263184 := by exact prefixLift 5263184
  have htrace : WordTrace (prefixWord ++ tailWord_5263184) baseStart_5263184 baseEnd_5263184 := by
    simpa [prefixWord, tailWord_5263184, baseEnd_5263184] using wordTrace_append hprefix tailTrace_5263184
  have hstable : (prefixWord ++ tailWord_5263184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263184).length < 2 ^ (prefixWord ++ tailWord_5263184).sum := by decide
  have hdescent : baseEnd_5263184 < baseStart_5263184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263201 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_5263201 : Nat := 118140960795 + 5263201 * 2 ^ 59
def prefixEnd_5263201 : Nat := 4983230072969 + 3 ^ 40 * 5263201 * 2
def baseEnd_5263201 : Nat := 2702551894224567435582485

theorem tailTrace_5263201 : CollatzResearch.WordTrace tailWord_5263201 prefixEnd_5263201 2702551894224567435582485 := by
  unfold tailWord_5263201
  simp only [CollatzResearch.WordTrace]
  refine ⟨191964711005329135012165457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127976474003552756674776971 191964711005329135012165457)
  ·
    refine ⟨143973533253996851259124093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191964711005329135012165457 143973533253996851259124093)
    ·
      refine ⟨53990074970248819222171535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143973533253996851259124093 53990074970248819222171535)
      ·
        refine ⟨80985112455373228833257303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53990074970248819222171535 80985112455373228833257303)
        ·
          refine ⟨121477668683059843249885955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80985112455373228833257303 121477668683059843249885955)
          ·
            refine ⟨182216503024589764874828933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121477668683059843249885955 182216503024589764874828933)
            ·
              refine ⟨34165594317110580914030425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182216503024589764874828933 34165594317110580914030425)
              ·
                refine ⟨25624195737832935685522819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34165594317110580914030425 25624195737832935685522819)
                ·
                  refine ⟨38436293606749403528284229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25624195737832935685522819 38436293606749403528284229)
                  ·
                    refine ⟨7206805051265513161553293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38436293606749403528284229 7206805051265513161553293)
                    ·
                      refine ⟨2702551894224567435582485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7206805051265513161553293 2702551894224567435582485)
                      ·
                        rfl

theorem cell23_5263201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_5263201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263201 prefixEnd_5263201 := by exact prefixLift 5263201
  have htrace : WordTrace (prefixWord ++ tailWord_5263201) baseStart_5263201 baseEnd_5263201 := by
    simpa [prefixWord, tailWord_5263201, baseEnd_5263201] using wordTrace_append hprefix tailTrace_5263201
  have hstable : (prefixWord ++ tailWord_5263201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263201).length < 2 ^ (prefixWord ++ tailWord_5263201).sum := by decide
  have hdescent : baseEnd_5263201 < baseStart_5263201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263208 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 3, 4]
def baseStart_5263208 : Nat := 118140960795 + 5263208 * 2 ^ 59
def prefixEnd_5263208 : Nat := 4983230072969 + 3 ^ 40 * 5263208 * 2
def baseEnd_5263208 : Nat := 900851829529716302731651

theorem tailTrace_5263208 : CollatzResearch.WordTrace tailWord_5263208 prefixEnd_5263208 900851829529716302731651 := by
  unfold tailWord_5263208
  simp only [CollatzResearch.WordTrace]
  refine ⟨95982483158151887603835139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127976644210869183471780185 95982483158151887603835139)
  ·
    refine ⟨143973724737227831405752709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95982483158151887603835139 143973724737227831405752709)
    ·
      refine ⟨26995073388230218388578633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143973724737227831405752709 26995073388230218388578633)
      ·
        refine ⟨20246305041172663791433975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26995073388230218388578633 20246305041172663791433975)
        ·
          refine ⟨30369457561758995687150963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20246305041172663791433975 30369457561758995687150963)
          ·
            refine ⟨45554186342638493530726445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30369457561758995687150963 45554186342638493530726445)
            ·
              refine ⟨17082819878489435074022417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45554186342638493530726445 17082819878489435074022417)
              ·
                refine ⟨12812114908867076305516813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17082819878489435074022417 12812114908867076305516813)
                ·
                  refine ⟨4804543090825153614568805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12812114908867076305516813 4804543090825153614568805)
                  ·
                    refine ⟨900851829529716302731651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804543090825153614568805 900851829529716302731651)
                    ·
                      rfl

theorem cell23_5263208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_5263208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263208 prefixEnd_5263208 := by exact prefixLift 5263208
  have htrace : WordTrace (prefixWord ++ tailWord_5263208) baseStart_5263208 baseEnd_5263208 := by
    simpa [prefixWord, tailWord_5263208, baseEnd_5263208] using wordTrace_append hprefix tailTrace_5263208
  have hstable : (prefixWord ++ tailWord_5263208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263208).length < 2 ^ (prefixWord ++ tailWord_5263208).sum := by decide
  have hdescent : baseEnd_5263208 < baseStart_5263208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263221 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 8]
def baseStart_5263221 : Nat := 118140960795 + 5263221 * 2 ^ 59
def prefixEnd_5263221 : Nat := 4983230072969 + 3 ^ 40 * 5263221 * 2
def baseEnd_5263221 : Nat := 300284684870850817481377

theorem tailTrace_5263221 : CollatzResearch.WordTrace tailWord_5263221 prefixEnd_5263221 300284684870850817481377 := by
  unfold tailWord_5263221
  simp only [CollatzResearch.WordTrace]
  refine ⟨191965440465256678427893517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127976960310171118951929011 191965440465256678427893517)
  ·
    refine ⟨71987040174471254410460069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191965440465256678427893517 71987040174471254410460069)
    ·
      refine ⟨13497570032713360201961263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71987040174471254410460069 13497570032713360201961263)
      ·
        refine ⟨20246355049070040302941895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13497570032713360201961263 20246355049070040302941895)
        ·
          refine ⟨30369532573605060454412843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20246355049070040302941895 30369532573605060454412843)
          ·
            refine ⟨45554298860407590681619265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30369532573605060454412843 45554298860407590681619265)
            ·
              refine ⟨34165724145305693011214449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45554298860407590681619265 34165724145305693011214449)
              ·
                refine ⟨25624293108979269758410837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34165724145305693011214449 25624293108979269758410837)
                ·
                  refine ⟨300284684870850817481377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25624293108979269758410837 300284684870850817481377)
                  ·
                    rfl

theorem cell23_5263221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_5263221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263221 prefixEnd_5263221 := by exact prefixLift 5263221
  have htrace : WordTrace (prefixWord ++ tailWord_5263221) baseStart_5263221 baseEnd_5263221 := by
    simpa [prefixWord, tailWord_5263221, baseEnd_5263221] using wordTrace_append hprefix tailTrace_5263221
  have hstable : (prefixWord ++ tailWord_5263221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263221).length < 2 ^ (prefixWord ++ tailWord_5263221).sum := by decide
  have hdescent : baseEnd_5263221 < baseStart_5263221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263225 : List Nat := [1, 2, 1, 3, 2, 2, 4, 3, 1, 4]
def baseStart_5263225 : Nat := 118140960795 + 5263225 * 2 ^ 59
def prefixEnd_5263225 : Nat := 4983230072969 + 3 ^ 40 * 5263225 * 2
def baseEnd_5263225 : Nat := 900854739253425113894125

theorem tailTrace_5263225 : CollatzResearch.WordTrace tailWord_5263225 prefixEnd_5263225 900854739253425113894125 := by
  unfold tailWord_5263225
  simp only [CollatzResearch.WordTrace]
  refine ⟨191965586357242187111039129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127977057571494791407359419 191965586357242187111039129)
  ·
    refine ⟨143974189767931640333279347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191965586357242187111039129 143974189767931640333279347)
    ·
      refine ⟨215961284651897460499919021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143974189767931640333279347 215961284651897460499919021)
      ·
        refine ⟨80985481744461547687469633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215961284651897460499919021 80985481744461547687469633)
        ·
          refine ⟨60739111308346160765602225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80985481744461547687469633 60739111308346160765602225)
          ·
            refine ⟨45554333481259620574201669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60739111308346160765602225 45554333481259620574201669)
            ·
              refine ⟨8541437527736178857662813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45554333481259620574201669 8541437527736178857662813)
              ·
                refine ⟨3203039072901067071623555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8541437527736178857662813 3203039072901067071623555)
                ·
                  refine ⟨4804558609351600607435333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3203039072901067071623555 4804558609351600607435333)
                  ·
                    refine ⟨900854739253425113894125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804558609351600607435333 900854739253425113894125)
                    ·
                      rfl

theorem cell23_5263225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 4].length) (baseStart_5263225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263225 prefixEnd_5263225 := by exact prefixLift 5263225
  have htrace : WordTrace (prefixWord ++ tailWord_5263225) baseStart_5263225 baseEnd_5263225 := by
    simpa [prefixWord, tailWord_5263225, baseEnd_5263225] using wordTrace_append hprefix tailTrace_5263225
  have hstable : (prefixWord ++ tailWord_5263225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263225).length < 2 ^ (prefixWord ++ tailWord_5263225).sum := by decide
  have hdescent : baseEnd_5263225 < baseStart_5263225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263248 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 3, 1, 3]
def baseStart_5263248 : Nat := 118140960795 + 5263248 * 2 ^ 59
def prefixEnd_5263248 : Nat := 4983230072969 + 3 ^ 40 * 5263248 * 2
def baseEnd_5263248 : Nat := 2702576027815328751694769

theorem tailTrace_5263248 : CollatzResearch.WordTrace tailWord_5263248 prefixEnd_5263248 2702576027815328751694769 := by
  unfold tailWord_5263248
  simp only [CollatzResearch.WordTrace]
  refine ⟨95983212618079431019563199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127977616824105908026084265 95983212618079431019563199)
  ·
    refine ⟨143974818927119146529344799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95983212618079431019563199 143974818927119146529344799)
    ·
      refine ⟨215962228390678719794017199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143974818927119146529344799 215962228390678719794017199)
      ·
        refine ⟨323943342586018079691025799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215962228390678719794017199 323943342586018079691025799)
        ·
          refine ⟨485915013879027119536538699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323943342586018079691025799 485915013879027119536538699)
          ·
            refine ⟨728872520818540679304808049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485915013879027119536538699 728872520818540679304808049)
            ·
              refine ⟨546654390613905509478606037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728872520818540679304808049 546654390613905509478606037)
              ·
                refine ⟨12812212280013410378404829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 546654390613905509478606037 12812212280013410378404829)
                ·
                  refine ⟨4804579605005028891901811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12812212280013410378404829 4804579605005028891901811)
                  ·
                    refine ⟨7206869407507543337852717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4804579605005028891901811 7206869407507543337852717)
                    ·
                      refine ⟨2702576027815328751694769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7206869407507543337852717 2702576027815328751694769)
                      ·
                        rfl

theorem cell23_5263248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 1, 3].length) (baseStart_5263248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263248 prefixEnd_5263248 := by exact prefixLift 5263248
  have htrace : WordTrace (prefixWord ++ tailWord_5263248) baseStart_5263248 baseEnd_5263248 := by
    simpa [prefixWord, tailWord_5263248, baseEnd_5263248] using wordTrace_append hprefix tailTrace_5263248
  have hstable : (prefixWord ++ tailWord_5263248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263248).length < 2 ^ (prefixWord ++ tailWord_5263248).sum := by decide
  have hdescent : baseEnd_5263248 < baseStart_5263248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263268 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_5263268 : Nat := 118140960795 + 5263268 * 2 ^ 59
def prefixEnd_5263268 : Nat := 4983230072969 + 3 ^ 40 * 5263268 * 2
def baseEnd_5263268 : Nat := 900862099142806224481559

theorem tailTrace_5263268 : CollatzResearch.WordTrace tailWord_5263268 prefixEnd_5263268 900862099142806224481559 := by
  unfold tailWord_5263268
  simp only [CollatzResearch.WordTrace]
  refine ⟨95983577348043202727427229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127978103130724270303236305 95983577348043202727427229)
  ·
    refine ⟨35993841505516201022785211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95983577348043202727427229 35993841505516201022785211)
    ·
      refine ⟨53990762258274301534177817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35993841505516201022785211 53990762258274301534177817)
      ·
        refine ⟨40493071693705726150633363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53990762258274301534177817 40493071693705726150633363)
        ·
          refine ⟨60739607540558589225950045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40493071693705726150633363 60739607540558589225950045)
          ·
            refine ⟨22777352827709470959731267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60739607540558589225950045 22777352827709470959731267)
            ·
              refine ⟨34166029241564206439596901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22777352827709470959731267 34166029241564206439596901)
              ·
                refine ⟨6406130482793288707424419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34166029241564206439596901 6406130482793288707424419)
                ·
                  refine ⟨9609195724189933061136629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6406130482793288707424419 9609195724189933061136629)
                  ·
                    refine ⟨900862099142806224481559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9609195724189933061136629 900862099142806224481559)
                    ·
                      rfl

theorem cell23_5263268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_5263268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263268 prefixEnd_5263268 := by exact prefixLift 5263268
  have htrace : WordTrace (prefixWord ++ tailWord_5263268) baseStart_5263268 baseEnd_5263268 := by
    simpa [prefixWord, tailWord_5263268, baseEnd_5263268] using wordTrace_append hprefix tailTrace_5263268
  have hstable : (prefixWord ++ tailWord_5263268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263268).length < 2 ^ (prefixWord ++ tailWord_5263268).sum := by decide
  have hdescent : baseEnd_5263268 < baseStart_5263268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263288 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_5263288 : Nat := 118140960795 + 5263288 * 2 ^ 59
def prefixEnd_5263288 : Nat := 4983230072969 + 3 ^ 40 * 5263288 * 2
def baseEnd_5263288 : Nat := 2702596567041508595194585

theorem tailTrace_5263288 : CollatzResearch.WordTrace tailWord_5263288 prefixEnd_5263288 2702596567041508595194585 := by
  unfold tailWord_5263288
  simp only [CollatzResearch.WordTrace]
  refine ⟨95983942078006974435291259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127978589437342632580388345 95983942078006974435291259)
  ·
    refine ⟨143975913117010461652936889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95983942078006974435291259 143975913117010461652936889)
    ·
      refine ⟨107981934837757846239702667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143975913117010461652936889 107981934837757846239702667)
      ·
        refine ⟨161972902256636769359554001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107981934837757846239702667 161972902256636769359554001)
        ·
          refine ⟨121479676692477577019665501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161972902256636769359554001 121479676692477577019665501)
          ·
            refine ⟨45554878759679091382374563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121479676692477577019665501 45554878759679091382374563)
            ·
              refine ⟨68332318139518637073561845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45554878759679091382374563 68332318139518637073561845)
              ·
                refine ⟨6406154825579872225646423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68332318139518637073561845 6406154825579872225646423)
                ·
                  refine ⟨9609232238369808338469635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6406154825579872225646423 9609232238369808338469635)
                  ·
                    refine ⟨14413848357554712507704453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9609232238369808338469635 14413848357554712507704453)
                    ·
                      refine ⟨2702596567041508595194585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14413848357554712507704453 2702596567041508595194585)
                      ·
                        rfl

theorem cell23_5263288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_5263288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263288 prefixEnd_5263288 := by exact prefixLift 5263288
  have htrace : WordTrace (prefixWord ++ tailWord_5263288) baseStart_5263288 baseEnd_5263288 := by
    simpa [prefixWord, tailWord_5263288, baseEnd_5263288] using wordTrace_append hprefix tailTrace_5263288
  have hstable : (prefixWord ++ tailWord_5263288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263288).length < 2 ^ (prefixWord ++ tailWord_5263288).sum := by decide
  have hdescent : baseEnd_5263288 < baseStart_5263288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263291 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 5]
def baseStart_5263291 : Nat := 118140960795 + 5263291 * 2 ^ 59
def prefixEnd_5263291 : Nat := 4983230072969 + 3 ^ 40 * 5263291 * 2
def baseEnd_5263291 : Nat := 2702598107483472083457071

theorem tailTrace_5263291 : CollatzResearch.WordTrace tailWord_5263291 prefixEnd_5263291 2702598107483472083457071 := by
  unfold tailWord_5263291
  simp only [CollatzResearch.WordTrace]
  refine ⟨191967993575003080382941727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127978662383335386921961151 191967993575003080382941727)
  ·
    refine ⟨287951990362504620574412591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191967993575003080382941727 287951990362504620574412591)
    ·
      refine ⟨431927985543756930861618887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287951990362504620574412591 431927985543756930861618887)
      ·
        refine ⟨647891978315635396292428331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431927985543756930861618887 647891978315635396292428331)
        ·
          refine ⟨971837967473453094438642497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647891978315635396292428331 971837967473453094438642497)
          ·
            refine ⟨728878475605089820828981873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971837967473453094438642497 728878475605089820828981873)
            ·
              refine ⟨546658856703817365621736405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728878475605089820828981873 546658856703817365621736405)
              ·
                refine ⟨12812316953995719506759447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 546658856703817365621736405 12812316953995719506759447)
                ·
                  refine ⟨19218475430993579260139171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12812316953995719506759447 19218475430993579260139171)
                  ·
                    refine ⟨28827713146490368890208757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19218475430993579260139171 28827713146490368890208757)
                    ·
                      refine ⟨2702598107483472083457071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28827713146490368890208757 2702598107483472083457071)
                      ·
                        rfl

theorem cell23_5263291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 5].length) (baseStart_5263291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263291 prefixEnd_5263291 := by exact prefixLift 5263291
  have htrace : WordTrace (prefixWord ++ tailWord_5263291) baseStart_5263291 baseEnd_5263291 := by
    simpa [prefixWord, tailWord_5263291, baseEnd_5263291] using wordTrace_append hprefix tailTrace_5263291
  have hstable : (prefixWord ++ tailWord_5263291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263291).length < 2 ^ (prefixWord ++ tailWord_5263291).sum := by decide
  have hdescent : baseEnd_5263291 < baseStart_5263291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263301 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_5263301 : Nat := 118140960795 + 5263301 * 2 ^ 59
def prefixEnd_5263301 : Nat := 4983230072969 + 3 ^ 40 * 5263301 * 2
def baseEnd_5263301 : Nat := 2702603242290017044332025

theorem tailTrace_5263301 : CollatzResearch.WordTrace tailWord_5263301 prefixEnd_5263301 2702603242290017044332025 := by
  unfold tailWord_5263301
  simp only [CollatzResearch.WordTrace]
  refine ⟨191968358304966852090805757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127978905536644568060537171 191968358304966852090805757)
  ·
    refine ⟨71988134364362569534052159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191968358304966852090805757 71988134364362569534052159)
    ·
      refine ⟨107982201546543854301078239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71988134364362569534052159 107982201546543854301078239)
      ·
        refine ⟨161973302319815781451617359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107982201546543854301078239 161973302319815781451617359)
        ·
          refine ⟨242959953479723672177426039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161973302319815781451617359 242959953479723672177426039)
          ·
            refine ⟨364439930219585508266139059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242959953479723672177426039 364439930219585508266139059)
            ·
              refine ⟨546659895329378262399208589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364439930219585508266139059 546659895329378262399208589)
              ·
                refine ⟨204997460748516848399703221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 546659895329378262399208589 204997460748516848399703221)
                ·
                  refine ⟨19218511945173454537472177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204997460748516848399703221 19218511945173454537472177)
                  ·
                    refine ⟨14413883958880090903104133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19218511945173454537472177 14413883958880090903104133)
                    ·
                      refine ⟨2702603242290017044332025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14413883958880090903104133 2702603242290017044332025)
                      ·
                        rfl

theorem cell23_5263301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_5263301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263301 prefixEnd_5263301 := by exact prefixLift 5263301
  have htrace : WordTrace (prefixWord ++ tailWord_5263301) baseStart_5263301 baseEnd_5263301 := by
    simpa [prefixWord, tailWord_5263301, baseEnd_5263301] using wordTrace_append hprefix tailTrace_5263301
  have hstable : (prefixWord ++ tailWord_5263301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263301).length < 2 ^ (prefixWord ++ tailWord_5263301).sum := by decide
  have hdescent : baseEnd_5263301 < baseStart_5263301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263308 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5263308 : Nat := 118140960795 + 5263308 * 2 ^ 59
def prefixEnd_5263308 : Nat := 4983230072969 + 3 ^ 40 * 5263308 * 2
def baseEnd_5263308 : Nat := 2702606836654598516944493

theorem tailTrace_5263308 : CollatzResearch.WordTrace tailWord_5263308 prefixEnd_5263308 2702606836654598516944493 := by
  unfold tailWord_5263308
  simp only [CollatzResearch.WordTrace]
  refine ⟨95984306807970746143155289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127979075743960994857540385 95984306807970746143155289)
  ·
    refine ⟨71988230105978059607366467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95984306807970746143155289 71988230105978059607366467)
    ·
      refine ⟨107982345158967089411049701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71988230105978059607366467 107982345158967089411049701)
      ·
        refine ⟨20246689717306329264571819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107982345158967089411049701 20246689717306329264571819)
        ·
          refine ⟨30370034575959493896857729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20246689717306329264571819 30370034575959493896857729)
          ·
            refine ⟨22777525931969620422643297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30370034575959493896857729 22777525931969620422643297)
            ·
              refine ⟨17083144448977215316982473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22777525931969620422643297 17083144448977215316982473)
              ·
                refine ⟨12812358336732911487736855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17083144448977215316982473 12812358336732911487736855)
                ·
                  refine ⟨19218537505099367231605283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12812358336732911487736855 19218537505099367231605283)
                  ·
                    refine ⟨28827806257649050847407925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19218537505099367231605283 28827806257649050847407925)
                    ·
                      refine ⟨2702606836654598516944493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28827806257649050847407925 2702606836654598516944493)
                      ·
                        rfl

theorem cell23_5263308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5263308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263308 prefixEnd_5263308 := by exact prefixLift 5263308
  have htrace : WordTrace (prefixWord ++ tailWord_5263308) baseStart_5263308 baseEnd_5263308 := by
    simpa [prefixWord, tailWord_5263308, baseEnd_5263308] using wordTrace_append hprefix tailTrace_5263308
  have hstable : (prefixWord ++ tailWord_5263308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263308).length < 2 ^ (prefixWord ++ tailWord_5263308).sum := by decide
  have hdescent : baseEnd_5263308 < baseStart_5263308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263311 : List Nat := [1, 1, 2, 1, 1, 5, 4, 8]
def baseStart_5263311 : Nat := 118140960795 + 5263311 * 2 ^ 59
def prefixEnd_5263311 : Nat := 4983230072969 + 3 ^ 40 * 5263311 * 2
def baseEnd_5263311 : Nat := 100096606559131926118777

theorem tailTrace_5263311 : CollatzResearch.WordTrace tailWord_5263311 prefixEnd_5263311 100096606559131926118777 := by
  unfold tailWord_5263311
  simp only [CollatzResearch.WordTrace]
  refine ⟨191968723034930623798669787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127979148689953749199113191 191968723034930623798669787)
  ·
    refine ⟨287953084552395935698004681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191968723034930623798669787 287953084552395935698004681)
    ·
      refine ⟨215964813414296951773503511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287953084552395935698004681 215964813414296951773503511)
      ·
        refine ⟨323947220121445427660255267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215964813414296951773503511 323947220121445427660255267)
        ·
          refine ⟨485920830182168141490382901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323947220121445427660255267 485920830182168141490382901)
          ·
            refine ⟨45555077829578263264723397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 485920830182168141490382901 45555077829578263264723397)
            ·
              refine ⟨8541577093045924362135637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45555077829578263264723397 8541577093045924362135637)
              ·
                refine ⟨100096606559131926118777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8541577093045924362135637 100096606559131926118777)
                ·
                  rfl

theorem cell23_5263311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 8].length) (baseStart_5263311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263311 prefixEnd_5263311 := by exact prefixLift 5263311
  have htrace : WordTrace (prefixWord ++ tailWord_5263311) baseStart_5263311 baseEnd_5263311 := by
    simpa [prefixWord, tailWord_5263311, baseEnd_5263311] using wordTrace_append hprefix tailTrace_5263311
  have hstable : (prefixWord ++ tailWord_5263311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263311).length < 2 ^ (prefixWord ++ tailWord_5263311).sum := by decide
  have hdescent : baseEnd_5263311 < baseStart_5263311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263322 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_5263322 : Nat := 118140960795 + 5263322 * 2 ^ 59
def prefixEnd_5263322 : Nat := 4983230072969 + 3 ^ 40 * 5263322 * 2
def baseEnd_5263322 : Nat := 2702614025383761462169429

theorem tailTrace_5263322 : CollatzResearch.WordTrace tailWord_5263322 prefixEnd_5263322 2702614025383761462169429 := by
  unfold tailWord_5263322
  simp only [CollatzResearch.WordTrace]
  refine ⟨47992281059472693169330055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127979416158593848451546813 47992281059472693169330055)
  ·
    refine ⟨71988421589209039753995083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47992281059472693169330055 71988421589209039753995083)
    ·
      refine ⟨107982632383813559630992625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71988421589209039753995083 107982632383813559630992625)
      ·
        refine ⟨80986974287860169723244469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107982632383813559630992625 80986974287860169723244469)
        ·
          refine ⟨7592528839486890911554169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80986974287860169723244469 7592528839486890911554169)
          ·
            refine ⟨5694396629615168183665627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7592528839486890911554169 5694396629615168183665627)
            ·
              refine ⟨8541594944422752275498441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5694396629615168183665627 8541594944422752275498441)
              ·
                refine ⟨6406196208317064206623831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8541594944422752275498441 6406196208317064206623831)
                ·
                  refine ⟨9609294312475596309935747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6406196208317064206623831 9609294312475596309935747)
                  ·
                    refine ⟨14413941468713394464903621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9609294312475596309935747 14413941468713394464903621)
                    ·
                      refine ⟨2702614025383761462169429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14413941468713394464903621 2702614025383761462169429)
                      ·
                        rfl

theorem cell23_5263322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_5263322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263322 prefixEnd_5263322 := by exact prefixLift 5263322
  have htrace : WordTrace (prefixWord ++ tailWord_5263322) baseStart_5263322 baseEnd_5263322 := by
    simpa [prefixWord, tailWord_5263322, baseEnd_5263322] using wordTrace_append hprefix tailTrace_5263322
  have hstable : (prefixWord ++ tailWord_5263322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263322).length < 2 ^ (prefixWord ++ tailWord_5263322).sum := by decide
  have hdescent : baseEnd_5263322 < baseStart_5263322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263335 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5263335 : Nat := 118140960795 + 5263335 * 2 ^ 59
def prefixEnd_5263335 : Nat := 4983230072969 + 3 ^ 40 * 5263335 * 2
def baseEnd_5263335 : Nat := 2702620700632269911306869

theorem tailTrace_5263335 : CollatzResearch.WordTrace tailWord_5263335 prefixEnd_5263335 2702620700632269911306869 := by
  unfold tailWord_5263335
  simp only [CollatzResearch.WordTrace]
  refine ⟨191969598386843675897543459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127979732257895783931695639 191969598386843675897543459)
  ·
    refine ⟨287954397580265513846315189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191969598386843675897543459 287954397580265513846315189)
    ·
      refine ⟨26995724773149891923092049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 287954397580265513846315189 26995724773149891923092049)
      ·
        refine ⟨20246793579862418942319037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26995724773149891923092049 20246793579862418942319037)
        ·
          refine ⟨7592547592448407103369639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20246793579862418942319037 7592547592448407103369639)
          ·
            refine ⟨11388821388672610655054459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7592547592448407103369639 11388821388672610655054459)
            ·
              refine ⟨17083232083008915982581689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11388821388672610655054459 17083232083008915982581689)
              ·
                refine ⟨12812424062256686986936267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17083232083008915982581689 12812424062256686986936267)
                ·
                  refine ⟨19218636093385030480404401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12812424062256686986936267 19218636093385030480404401)
                  ·
                    refine ⟨14413977070038772860303301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19218636093385030480404401 14413977070038772860303301)
                    ·
                      refine ⟨2702620700632269911306869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14413977070038772860303301 2702620700632269911306869)
                      ·
                        rfl

theorem cell23_5263335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5263335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263335 prefixEnd_5263335 := by exact prefixLift 5263335
  have htrace : WordTrace (prefixWord ++ tailWord_5263335) baseStart_5263335 baseEnd_5263335 := by
    simpa [prefixWord, tailWord_5263335, baseEnd_5263335] using wordTrace_append hprefix tailTrace_5263335
  have hstable : (prefixWord ++ tailWord_5263335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263335).length < 2 ^ (prefixWord ++ tailWord_5263335).sum := by decide
  have hdescent : baseEnd_5263335 < baseStart_5263335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263355 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 3]
def baseStart_5263355 : Nat := 118140960795 + 5263355 * 2 ^ 59
def prefixEnd_5263355 : Nat := 4983230072969 + 3 ^ 40 * 5263355 * 2
def baseEnd_5263355 : Nat := 2702630970245359833056777

theorem tailTrace_5263355 : CollatzResearch.WordTrace tailWord_5263355 prefixEnd_5263355 2702630970245359833056777 := by
  unfold tailWord_5263355
  simp only [CollatzResearch.WordTrace]
  refine ⟨191970327846771219313271519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127980218564514146208847679 191970327846771219313271519)
  ·
    refine ⟨287955491770156828969907279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191970327846771219313271519 287955491770156828969907279)
    ·
      refine ⟨431933237655235243454860919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287955491770156828969907279 431933237655235243454860919)
      ·
        refine ⟨647899856482852865182291379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431933237655235243454860919 647899856482852865182291379)
        ·
          refine ⟨971849784724279297773437069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647899856482852865182291379 971849784724279297773437069)
          ·
            refine ⟨364443669271604736665038901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 971849784724279297773437069 364443669271604736665038901)
            ·
              refine ⟨34166593994212944062347397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 364443669271604736665038901 34166593994212944062347397)
              ·
                refine ⟨6406236373914927011690137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34166593994212944062347397 6406236373914927011690137)
                ·
                  refine ⟨4804677280436195258767603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6406236373914927011690137 4804677280436195258767603)
                  ·
                    refine ⟨7207015920654292888151405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4804677280436195258767603 7207015920654292888151405)
                    ·
                      refine ⟨2702630970245359833056777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7207015920654292888151405 2702630970245359833056777)
                      ·
                        rfl

theorem cell23_5263355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 3].length) (baseStart_5263355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263355 prefixEnd_5263355 := by exact prefixLift 5263355
  have htrace : WordTrace (prefixWord ++ tailWord_5263355) baseStart_5263355 baseEnd_5263355 := by
    simpa [prefixWord, tailWord_5263355, baseEnd_5263355] using wordTrace_append hprefix tailTrace_5263355
  have hstable : (prefixWord ++ tailWord_5263355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263355).length < 2 ^ (prefixWord ++ tailWord_5263355).sum := by decide
  have hdescent : baseEnd_5263355 < baseStart_5263355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263365 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 3, 3, 2]
def baseStart_5263365 : Nat := 118140960795 + 5263365 * 2 ^ 59
def prefixEnd_5263365 : Nat := 4983230072969 + 3 ^ 40 * 5263365 * 2
def baseEnd_5263365 : Nat := 2702636105051904793931731

theorem tailTrace_5263365 : CollatzResearch.WordTrace tailWord_5263365 prefixEnd_5263365 2702636105051904793931731 := by
  unfold tailWord_5263365
  simp only [CollatzResearch.WordTrace]
  refine ⟨191970692576734991021135549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127980461717823327347423699 191970692576734991021135549)
  ·
    refine ⟨71989009716275621632925831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191970692576734991021135549 71989009716275621632925831)
    ·
      refine ⟨107983514574413432449388747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71989009716275621632925831 107983514574413432449388747)
      ·
        refine ⟨161975271861620148674083121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107983514574413432449388747 161975271861620148674083121)
        ·
          refine ⟨121481453896215111505562341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161975271861620148674083121 121481453896215111505562341)
          ·
            refine ⟨22777772605540333407292939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121481453896215111505562341 22777772605540333407292939)
            ·
              refine ⟨34166658908310500110939409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22777772605540333407292939 34166658908310500110939409)
              ·
                refine ⟨25624994181232875083204557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34166658908310500110939409 25624994181232875083204557)
                ·
                  refine ⟨9609372817962328156201709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25624994181232875083204557 9609372817962328156201709)
                  ·
                    refine ⟨3603514806735873058575641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9609372817962328156201709 3603514806735873058575641)
                    ·
                      refine ⟨2702636105051904793931731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603514806735873058575641 2702636105051904793931731)
                      ·
                        rfl

theorem cell23_5263365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_5263365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263365 prefixEnd_5263365 := by exact prefixLift 5263365
  have htrace : WordTrace (prefixWord ++ tailWord_5263365) baseStart_5263365 baseEnd_5263365 := by
    simpa [prefixWord, tailWord_5263365, baseEnd_5263365] using wordTrace_append hprefix tailTrace_5263365
  have hstable : (prefixWord ++ tailWord_5263365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263365).length < 2 ^ (prefixWord ++ tailWord_5263365).sum := by decide
  have hdescent : baseEnd_5263365 < baseStart_5263365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263366 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5263366 : Nat := 118140960795 + 5263366 * 2 ^ 59
def prefixEnd_5263366 : Nat := 4983230072969 + 3 ^ 40 * 5263366 * 2
def baseEnd_5263366 : Nat := 900878872844186430006409

theorem tailTrace_5263366 : CollatzResearch.WordTrace tailWord_5263366 prefixEnd_5263366 900878872844186430006409 := by
  unfold tailWord_5263366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5999085282804105255997561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127980486033154245461281301 5999085282804105255997561)
  ·
    refine ⟨4499313962103078941998171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5999085282804105255997561 4499313962103078941998171)
    ·
      refine ⟨6748970943154618412997257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4499313962103078941998171 6748970943154618412997257)
      ·
        refine ⟨5061728207365963809747943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6748970943154618412997257 5061728207365963809747943)
        ·
          refine ⟨7592592311048945714621915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061728207365963809747943 7592592311048945714621915)
          ·
            refine ⟨11388888466573418571932873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7592592311048945714621915 11388888466573418571932873)
            ·
              refine ⟨8541666349930063928949655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11388888466573418571932873 8541666349930063928949655)
              ·
                refine ⟨12812499524895095893424483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8541666349930063928949655 12812499524895095893424483)
                ·
                  refine ⟨19218749287342643840136725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12812499524895095893424483 19218749287342643840136725)
                  ·
                    refine ⟨900878872844186430006409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19218749287342643840136725 900878872844186430006409)
                    ·
                      rfl

theorem cell23_5263366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5263366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263366 prefixEnd_5263366 := by exact prefixLift 5263366
  have htrace : WordTrace (prefixWord ++ tailWord_5263366) baseStart_5263366 baseEnd_5263366 := by
    simpa [prefixWord, tailWord_5263366, baseEnd_5263366] using wordTrace_append hprefix tailTrace_5263366
  have hstable : (prefixWord ++ tailWord_5263366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263366).length < 2 ^ (prefixWord ++ tailWord_5263366).sum := by decide
  have hdescent : baseEnd_5263366 < baseStart_5263366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263373 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5263373 : Nat := 118140960795 + 5263373 * 2 ^ 59
def prefixEnd_5263373 : Nat := 4983230072969 + 3 ^ 40 * 5263373 * 2
def baseEnd_5263373 : Nat := 2702640212897140762631695

theorem tailTrace_5263373 : CollatzResearch.WordTrace tailWord_5263373 prefixEnd_5263373 2702640212897140762631695 := by
  unfold tailWord_5263373
  simp only [CollatzResearch.WordTrace]
  refine ⟨191970984360706008387426773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127980656240470672258284515 191970984360706008387426773)
  ·
    refine ⟨4499319945954047071580315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 191970984360706008387426773 4499319945954047071580315)
    ·
      refine ⟨6748979918931070607370473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4499319945954047071580315 6748979918931070607370473)
      ·
        refine ⟨5061734939198302955527855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6748979918931070607370473 5061734939198302955527855)
        ·
          refine ⟨7592602408797454433291783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061734939198302955527855 7592602408797454433291783)
          ·
            refine ⟨11388903613196181649937675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7592602408797454433291783 11388903613196181649937675)
            ·
              refine ⟨17083355419794272474906513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11388903613196181649937675 17083355419794272474906513)
              ·
                refine ⟨12812516564845704356179885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17083355419794272474906513 12812516564845704356179885)
                ·
                  refine ⟨4804693711817139133567457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12812516564845704356179885 4804693711817139133567457)
                  ·
                    refine ⟨3603520283862854350175593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4804693711817139133567457 3603520283862854350175593)
                    ·
                      refine ⟨2702640212897140762631695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603520283862854350175593 2702640212897140762631695)
                      ·
                        rfl

theorem cell23_5263373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5263373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263373 prefixEnd_5263373 := by exact prefixLift 5263373
  have htrace : WordTrace (prefixWord ++ tailWord_5263373) baseStart_5263373 baseEnd_5263373 := by
    simpa [prefixWord, tailWord_5263373, baseEnd_5263373] using wordTrace_append hprefix tailTrace_5263373
  have hstable : (prefixWord ++ tailWord_5263373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263373).length < 2 ^ (prefixWord ++ tailWord_5263373).sum := by decide
  have hdescent : baseEnd_5263373 < baseStart_5263373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263395 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 1, 4, 2]
def baseStart_5263395 : Nat := 118140960795 + 5263395 * 2 ^ 59
def prefixEnd_5263395 : Nat := 4983230072969 + 3 ^ 40 * 5263395 * 2
def baseEnd_5263395 : Nat := 2702651509471539676556593

theorem tailTrace_5263395 : CollatzResearch.WordTrace tailWord_5263395 prefixEnd_5263395 2702651509471539676556593 := by
  unfold tailWord_5263395
  simp only [CollatzResearch.WordTrace]
  refine ⟨191971786766626306144727639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127981191177750870763151759 191971786766626306144727639)
  ·
    refine ⟨287957680149939459217091459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191971786766626306144727639 287957680149939459217091459)
    ·
      refine ⟨431936520224909188825637189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287957680149939459217091459 431936520224909188825637189)
      ·
        refine ⟨80988097542170472904806973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 431936520224909188825637189 80988097542170472904806973)
        ·
          refine ⟨30370536578313927339302615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80988097542170472904806973 30370536578313927339302615)
          ·
            refine ⟨45555804867470891008953923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30370536578313927339302615 45555804867470891008953923)
            ·
              refine ⟨68333707301206336513430885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45555804867470891008953923 68333707301206336513430885)
              ·
                refine ⟨12812570118976188096268291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68333707301206336513430885 12812570118976188096268291)
                ·
                  refine ⟨19218855178464282144402437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12812570118976188096268291 19218855178464282144402437)
                  ·
                    refine ⟨3603535345962052902075457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19218855178464282144402437 3603535345962052902075457)
                    ·
                      refine ⟨2702651509471539676556593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603535345962052902075457 2702651509471539676556593)
                      ·
                        rfl

theorem cell23_5263395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_5263395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263395 prefixEnd_5263395 := by exact prefixLift 5263395
  have htrace : WordTrace (prefixWord ++ tailWord_5263395) baseStart_5263395 baseEnd_5263395 := by
    simpa [prefixWord, tailWord_5263395, baseEnd_5263395] using wordTrace_append hprefix tailTrace_5263395
  have hstable : (prefixWord ++ tailWord_5263395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263395).length < 2 ^ (prefixWord ++ tailWord_5263395).sum := by decide
  have hdescent : baseEnd_5263395 < baseStart_5263395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263408 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_5263408 : Nat := 118140960795 + 5263408 * 2 ^ 59
def prefixEnd_5263408 : Nat := 4983230072969 + 3 ^ 40 * 5263408 * 2
def baseEnd_5263408 : Nat := 2702658184720048125694033

theorem tailTrace_5263408 : CollatzResearch.WordTrace tailWord_5263408 prefixEnd_5263408 2702658184720048125694033 := by
  unfold tailWord_5263408
  simp only [CollatzResearch.WordTrace]
  refine ⟨95986130457789604682475439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127981507277052806243300585 95986130457789604682475439)
  ·
    refine ⟨143979195686684407023713159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95986130457789604682475439 143979195686684407023713159)
    ·
      refine ⟨215968793530026610535569739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143979195686684407023713159 215968793530026610535569739)
      ·
        refine ⟨323953190295039915803354609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215968793530026610535569739 323953190295039915803354609)
        ·
          refine ⟨242964892721279936852515957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323953190295039915803354609 242964892721279936852515957)
          ·
            refine ⟨22777958692619994079923371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242964892721279936852515957 22777958692619994079923371)
            ·
              refine ⟨34166938038929991119885057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22777958692619994079923371 34166938038929991119885057)
              ·
                refine ⟨25625203529197493339913793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34166938038929991119885057 25625203529197493339913793)
                ·
                  refine ⟨19218902646898120004935345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25625203529197493339913793 19218902646898120004935345)
                  ·
                    refine ⟨14414176985173590003701509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19218902646898120004935345 14414176985173590003701509)
                    ·
                      refine ⟨2702658184720048125694033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14414176985173590003701509 2702658184720048125694033)
                      ·
                        rfl

theorem cell23_5263408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_5263408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263408 prefixEnd_5263408 := by exact prefixLift 5263408
  have htrace : WordTrace (prefixWord ++ tailWord_5263408) baseStart_5263408 baseEnd_5263408 := by
    simpa [prefixWord, tailWord_5263408, baseEnd_5263408] using wordTrace_append hprefix tailTrace_5263408
  have hstable : (prefixWord ++ tailWord_5263408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263408).length < 2 ^ (prefixWord ++ tailWord_5263408).sum := by decide
  have hdescent : baseEnd_5263408 < baseStart_5263408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263425 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5263425 : Nat := 118140960795 + 5263425 * 2 ^ 59
def prefixEnd_5263425 : Nat := 4983230072969 + 3 ^ 40 * 5263425 * 2
def baseEnd_5263425 : Nat := 2702666913891174559181455

theorem tailTrace_5263425 : CollatzResearch.WordTrace tailWord_5263425 prefixEnd_5263425 2702666913891174559181455 := by
  unfold tailWord_5263425
  simp only [CollatzResearch.WordTrace]
  refine ⟨191972880956517621268319729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127981920637678414178879819 191972880956517621268319729)
  ·
    refine ⟨143979660717388215951239797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191972880956517621268319729 143979660717388215951239797)
    ·
      refine ⟨13498093192255145245428731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143979660717388215951239797 13498093192255145245428731)
      ·
        refine ⟨20247139788382717868143097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13498093192255145245428731 20247139788382717868143097)
        ·
          refine ⟨15185354841287038401107323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20247139788382717868143097 15185354841287038401107323)
          ·
            refine ⟨22778032261930557601660985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15185354841287038401107323 22778032261930557601660985)
            ·
              refine ⟨17083524196447918201245739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22778032261930557601660985 17083524196447918201245739)
              ·
                refine ⟨25625286294671877301868609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17083524196447918201245739 25625286294671877301868609)
                ·
                  refine ⟨19218964721003907976401457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25625286294671877301868609 19218964721003907976401457)
                  ·
                    refine ⟨14414223540752930982301093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19218964721003907976401457 14414223540752930982301093)
                    ·
                      refine ⟨2702666913891174559181455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14414223540752930982301093 2702666913891174559181455)
                      ·
                        rfl

theorem cell23_5263425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5263425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263425 prefixEnd_5263425 := by exact prefixLift 5263425
  have htrace : WordTrace (prefixWord ++ tailWord_5263425) baseStart_5263425 baseEnd_5263425 := by
    simpa [prefixWord, tailWord_5263425, baseEnd_5263425] using wordTrace_append hprefix tailTrace_5263425
  have hstable : (prefixWord ++ tailWord_5263425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263425).length < 2 ^ (prefixWord ++ tailWord_5263425).sum := by decide
  have hdescent : baseEnd_5263425 < baseStart_5263425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263446 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5263446 : Nat := 118140960795 + 5263446 * 2 ^ 59
def prefixEnd_5263446 : Nat := 4983230072969 + 3 ^ 40 * 5263446 * 2
def baseEnd_5263446 : Nat := 2702677696984918977018859

theorem tailTrace_5263446 : CollatzResearch.WordTrace tailWord_5263446 prefixEnd_5263446 2702677696984918977018859 := by
  unfold tailWord_5263446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11998352930590096365927137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127982431259627694569889461 11998352930590096365927137)
  ·
    refine ⟨8998764697942572274445353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11998352930590096365927137 8998764697942572274445353)
    ·
      refine ⟨6749073523456929205834015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8998764697942572274445353 6749073523456929205834015)
      ·
        refine ⟨10123610285185393808751023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6749073523456929205834015 10123610285185393808751023)
        ·
          refine ⟨15185415427778090713126535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10123610285185393808751023 15185415427778090713126535)
          ·
            refine ⟨22778123141667136069689803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15185415427778090713126535 22778123141667136069689803)
            ·
              refine ⟨34167184712500704104534705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22778123141667136069689803 34167184712500704104534705)
              ·
                refine ⟨25625388534375528078401029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34167184712500704104534705 25625388534375528078401029)
                ·
                  refine ⟨4804760350195411514700193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25625388534375528078401029 4804760350195411514700193)
                  ·
                    refine ⟨3603570262646558636025145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4804760350195411514700193 3603570262646558636025145)
                    ·
                      refine ⟨2702677696984918977018859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603570262646558636025145 2702677696984918977018859)
                      ·
                        rfl

theorem cell23_5263446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5263446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263446 prefixEnd_5263446 := by exact prefixLift 5263446
  have htrace : WordTrace (prefixWord ++ tailWord_5263446) baseStart_5263446 baseEnd_5263446 := by
    simpa [prefixWord, tailWord_5263446, baseEnd_5263446] using wordTrace_append hprefix tailTrace_5263446
  have hstable : (prefixWord ++ tailWord_5263446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263446).length < 2 ^ (prefixWord ++ tailWord_5263446).sum := by decide
  have hdescent : baseEnd_5263446 < baseStart_5263446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263448 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 1, 7]
def baseStart_5263448 : Nat := 118140960795 + 5263448 * 2 ^ 59
def prefixEnd_5263448 : Nat := 4983230072969 + 3 ^ 40 * 5263448 * 2
def baseEnd_5263448 : Nat := 900892907982075989731283

theorem tailTrace_5263448 : CollatzResearch.WordTrace tailWord_5263448 prefixEnd_5263448 900892907982075989731283 := by
  unfold tailWord_5263448
  simp only [CollatzResearch.WordTrace]
  refine ⟨95986859917717148098203499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127982479890289530797604665 95986859917717148098203499)
  ·
    refine ⟨143980289876575722147305249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95986859917717148098203499 143980289876575722147305249)
    ·
      refine ⟨107985217407431791610478937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143980289876575722147305249 107985217407431791610478937)
      ·
        refine ⟨80988913055573843707859203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107985217407431791610478937 80988913055573843707859203)
        ·
          refine ⟨121483369583360765561788805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80988913055573843707859203 121483369583360765561788805)
          ·
            refine ⟨22778131796880143542835401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121483369583360765561788805 22778131796880143542835401)
            ·
              refine ⟨17083598847660107657126551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22778131796880143542835401 17083598847660107657126551)
              ·
                refine ⟨25625398271490161485689827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17083598847660107657126551 25625398271490161485689827)
                ·
                  refine ⟨38438097407235242228534741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25625398271490161485689827 38438097407235242228534741)
                  ·
                    refine ⟨900892907982075989731283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38438097407235242228534741 900892907982075989731283)
                    ·
                      rfl

theorem cell23_5263448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_5263448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263448 prefixEnd_5263448 := by exact prefixLift 5263448
  have htrace : WordTrace (prefixWord ++ tailWord_5263448) baseStart_5263448 baseEnd_5263448 := by
    simpa [prefixWord, tailWord_5263448, baseEnd_5263448] using wordTrace_append hprefix tailTrace_5263448
  have hstable : (prefixWord ++ tailWord_5263448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263448).length < 2 ^ (prefixWord ++ tailWord_5263448).sum := by decide
  have hdescent : baseEnd_5263448 < baseStart_5263448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263452 : List Nat := [2, 2, 4, 1, 1, 2, 3, 3, 5]
def baseStart_5263452 : Nat := 118140960795 + 5263452 * 2 ^ 59
def prefixEnd_5263452 : Nat := 4983230072969 + 3 ^ 40 * 5263452 * 2
def baseEnd_5263452 : Nat := 300297864207649550393759

theorem tailTrace_5263452 : CollatzResearch.WordTrace tailWord_5263452 prefixEnd_5263452 300297864207649550393759 := by
  unfold tailWord_5263452
  simp only [CollatzResearch.WordTrace]
  refine ⟨95986932863709902439776305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127982577151613203253035073 95986932863709902439776305)
  ·
    refine ⟨71990199647782426829832229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95986932863709902439776305 71990199647782426829832229)
    ·
      refine ⟨13498162433959205030593543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71990199647782426829832229 13498162433959205030593543)
      ·
        refine ⟨20247243650938807545890315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13498162433959205030593543 20247243650938807545890315)
        ·
          refine ⟨30370865476408211318835473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20247243650938807545890315 30370865476408211318835473)
          ·
            refine ⟨22778149107306158489126605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30370865476408211318835473 22778149107306158489126605)
            ·
              refine ⟨8541805915239809433422477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22778149107306158489126605 8541805915239809433422477)
              ·
                refine ⟨3203177218214928537533429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8541805915239809433422477 3203177218214928537533429)
                ·
                  refine ⟨300297864207649550393759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3203177218214928537533429 300297864207649550393759)
                  ·
                    rfl

theorem cell23_5263452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_5263452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263452 prefixEnd_5263452 := by exact prefixLift 5263452
  have htrace : WordTrace (prefixWord ++ tailWord_5263452) baseStart_5263452 baseEnd_5263452 := by
    simpa [prefixWord, tailWord_5263452, baseEnd_5263452] using wordTrace_append hprefix tailTrace_5263452
  have hstable : (prefixWord ++ tailWord_5263452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263452).length < 2 ^ (prefixWord ++ tailWord_5263452).sum := by decide
  have hdescent : baseEnd_5263452 < baseStart_5263452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263495 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 3, 4]
def baseStart_5263495 : Nat := 118140960795 + 5263495 * 2 ^ 59
def prefixEnd_5263495 : Nat := 4983230072969 + 3 ^ 40 * 5263495 * 2
def baseEnd_5263495 : Nat := 900900952512329761768711

theorem tailTrace_5263495 : CollatzResearch.WordTrace tailWord_5263495 prefixEnd_5263495 900900952512329761768711 := by
  unfold tailWord_5263495
  simp only [CollatzResearch.WordTrace]
  refine ⟨191975434066264023223367939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127983622710842682148911959 191975434066264023223367939)
  ·
    refine ⟨287963151099396034835051909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191975434066264023223367939 287963151099396034835051909)
    ·
      refine ⟨53993090831136756531572233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287963151099396034835051909 53993090831136756531572233)
      ·
        refine ⟨40494818123352567398679175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53993090831136756531572233 40494818123352567398679175)
        ·
          refine ⟨60742227185028851098018763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40494818123352567398679175 60742227185028851098018763)
          ·
            refine ⟨91113340777543276647028145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60742227185028851098018763 91113340777543276647028145)
            ·
              refine ⟨68335005583157457485271109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91113340777543276647028145 68335005583157457485271109)
              ·
                refine ⟨12812813546842023278488333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68335005583157457485271109 12812813546842023278488333)
                ·
                  refine ⟨4804805080065758729433125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12812813546842023278488333 4804805080065758729433125)
                  ·
                    refine ⟨900900952512329761768711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804805080065758729433125 900900952512329761768711)
                    ·
                      rfl

theorem cell23_5263495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_5263495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263495 prefixEnd_5263495 := by exact prefixLift 5263495
  have htrace : WordTrace (prefixWord ++ tailWord_5263495) baseStart_5263495 baseEnd_5263495 := by
    simpa [prefixWord, tailWord_5263495, baseEnd_5263495] using wordTrace_append hprefix tailTrace_5263495
  have hstable : (prefixWord ++ tailWord_5263495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263495).length < 2 ^ (prefixWord ++ tailWord_5263495).sum := by decide
  have hdescent : baseEnd_5263495 < baseStart_5263495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263525 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 6]
def baseStart_5263525 : Nat := 118140960795 + 5263525 * 2 ^ 59
def prefixEnd_5263525 : Nat := 4983230072969 + 3 ^ 40 * 5263525 * 2
def baseEnd_5263525 : Nat := 300302029106291574214555

theorem tailTrace_5263525 : CollatzResearch.WordTrace tailWord_5263525 prefixEnd_5263525 300302029106291574214555 := by
  unfold tailWord_5263525
  simp only [CollatzResearch.WordTrace]
  refine ⟨191976528256155338346960029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127984352170770225564640019 191976528256155338346960029)
  ·
    refine ⟨71991198096058251880110011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191976528256155338346960029 71991198096058251880110011)
    ·
      refine ⟨107986797144087377820165017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71991198096058251880110011 107986797144087377820165017)
      ·
        refine ⟨80990097858065533365123763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107986797144087377820165017 80990097858065533365123763)
        ·
          refine ⟨121485146787098300047685645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80990097858065533365123763 121485146787098300047685645)
          ·
            refine ⟨45556930045161862517882117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121485146787098300047685645 45556930045161862517882117)
            ·
              refine ⟨8541924383467849222102897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45556930045161862517882117 8541924383467849222102897)
              ·
                refine ⟨6406443287600886916577173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8541924383467849222102897 6406443287600886916577173)
                ·
                  refine ⟨300302029106291574214555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6406443287600886916577173 300302029106291574214555)
                  ·
                    rfl

theorem cell23_5263525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_5263525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263525 prefixEnd_5263525 := by exact prefixLift 5263525
  have htrace : WordTrace (prefixWord ++ tailWord_5263525) baseStart_5263525 baseEnd_5263525 := by
    simpa [prefixWord, tailWord_5263525, baseEnd_5263525] using wordTrace_append hprefix tailTrace_5263525
  have hstable : (prefixWord ++ tailWord_5263525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263525).length < 2 ^ (prefixWord ++ tailWord_5263525).sum := by decide
  have hdescent : baseEnd_5263525 < baseStart_5263525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263552 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 5, 1, 3]
def baseStart_5263552 : Nat := 118140960795 + 5263552 * 2 ^ 59
def prefixEnd_5263552 : Nat := 4983230072969 + 3 ^ 40 * 5263552 * 2
def baseEnd_5263552 : Nat := 2702732125934295562293371

theorem tailTrace_5263552 : CollatzResearch.WordTrace tailWord_5263552 prefixEnd_5263552 2702732125934295562293371 := by
  unfold tailWord_5263552
  simp only [CollatzResearch.WordTrace]
  refine ⟨95988756513528760979096455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127985008684705014638795273 95988756513528760979096455)
  ·
    refine ⟨143983134770293141468644683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95988756513528760979096455 143983134770293141468644683)
    ·
      refine ⟨215974702155439712202967025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143983134770293141468644683 215974702155439712202967025)
      ·
        refine ⟨161981026616579784152225269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215974702155439712202967025 161981026616579784152225269)
        ·
          refine ⟨15185721245304354764271119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161981026616579784152225269 15185721245304354764271119)
          ·
            refine ⟨22778581867956532146406679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15185721245304354764271119 22778581867956532146406679)
            ·
              refine ⟨34167872801934798219610019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22778581867956532146406679 34167872801934798219610019)
              ·
                refine ⟨51251809202902197329415029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34167872801934798219610019 51251809202902197329415029)
                ·
                  refine ⟨4804857112772080999632659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51251809202902197329415029 4804857112772080999632659)
                  ·
                    refine ⟨7207285669158121499448989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4804857112772080999632659 7207285669158121499448989)
                    ·
                      refine ⟨2702732125934295562293371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7207285669158121499448989 2702732125934295562293371)
                      ·
                        rfl

theorem cell23_5263552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_5263552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263552 prefixEnd_5263552 := by exact prefixLift 5263552
  have htrace : WordTrace (prefixWord ++ tailWord_5263552) baseStart_5263552 baseEnd_5263552 := by
    simpa [prefixWord, tailWord_5263552, baseEnd_5263552] using wordTrace_append hprefix tailTrace_5263552
  have hstable : (prefixWord ++ tailWord_5263552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263552).length < 2 ^ (prefixWord ++ tailWord_5263552).sum := by decide
  have hdescent : baseEnd_5263552 < baseStart_5263552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263562 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_5263562 : Nat := 118140960795 + 5263562 * 2 ^ 59
def prefixEnd_5263562 : Nat := 4983230072969 + 3 ^ 40 * 5263562 * 2
def baseEnd_5263562 : Nat := 2702737260740840523168325

theorem tailTrace_5263562 : CollatzResearch.WordTrace tailWord_5263562 prefixEnd_5263562 2702737260740840523168325 := by
  unfold tailWord_5263562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47994469439255323416514235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127985251838014195777371293 47994469439255323416514235)
  ·
    refine ⟨71991704158882985124771353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47994469439255323416514235 71991704158882985124771353)
    ·
      refine ⟨53993778119162238843578515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71991704158882985124771353 53993778119162238843578515)
      ·
        refine ⟨80990667178743358265367773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53993778119162238843578515 80990667178743358265367773)
        ·
          refine ⟨30371500192028759349512915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80990667178743358265367773 30371500192028759349512915)
          ·
            refine ⟨45557250288043139024269373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30371500192028759349512915 45557250288043139024269373)
            ·
              refine ⟨17083968858016177134101015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45557250288043139024269373 17083968858016177134101015)
              ·
                refine ⟨25625953287024265701151523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17083968858016177134101015 25625953287024265701151523)
                ·
                  refine ⟨38438929930536398551727285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25625953287024265701151523 38438929930536398551727285)
                  ·
                    refine ⟨3603649680987787364224433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38438929930536398551727285 3603649680987787364224433)
                    ·
                      refine ⟨2702737260740840523168325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603649680987787364224433 2702737260740840523168325)
                      ·
                        rfl

theorem cell23_5263562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_5263562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263562 prefixEnd_5263562 := by exact prefixLift 5263562
  have htrace : WordTrace (prefixWord ++ tailWord_5263562) baseStart_5263562 baseEnd_5263562 := by
    simpa [prefixWord, tailWord_5263562, baseEnd_5263562] using wordTrace_append hprefix tailTrace_5263562
  have hstable : (prefixWord ++ tailWord_5263562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263562).length < 2 ^ (prefixWord ++ tailWord_5263562).sum := by decide
  have hdescent : baseEnd_5263562 < baseStart_5263562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263569 : List Nat := [1, 2, 2, 1, 2, 2, 3, 5, 1, 1, 3]
def baseStart_5263569 : Nat := 118140960795 + 5263569 * 2 ^ 59
def prefixEnd_5263569 : Nat := 4983230072969 + 3 ^ 40 * 5263569 * 2
def baseEnd_5263569 : Nat := 2702740855105421995780793

theorem tailTrace_5263569 : CollatzResearch.WordTrace tailWord_5263569 prefixEnd_5263569 2702740855105421995780793 := by
  unfold tailWord_5263569
  simp only [CollatzResearch.WordTrace]
  refine ⟨191978133067995933861561761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127985422045330622574374507 191978133067995933861561761)
  ·
    refine ⟨143983599800996950396171321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191978133067995933861561761 143983599800996950396171321)
    ·
      refine ⟨107987699850747712797128491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143983599800996950396171321 107987699850747712797128491)
      ·
        refine ⟨161981549776121569195692737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107987699850747712797128491 161981549776121569195692737)
        ·
          refine ⟨121486162332091176896769553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161981549776121569195692737 121486162332091176896769553)
          ·
            refine ⟨91114621749068382672577165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121486162332091176896769553 91114621749068382672577165)
            ·
              refine ⟨34167983155900643502216437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91114621749068382672577165 34167983155900643502216437)
              ·
                refine ⟨3203248420865685328332791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34167983155900643502216437 3203248420865685328332791)
                ·
                  refine ⟨4804872631298527992499187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3203248420865685328332791 4804872631298527992499187)
                  ·
                    refine ⟨7207308946947791988748781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4804872631298527992499187 7207308946947791988748781)
                    ·
                      refine ⟨2702740855105421995780793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7207308946947791988748781 2702740855105421995780793)
                      ·
                        rfl

theorem cell23_5263569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_5263569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263569 prefixEnd_5263569 := by exact prefixLift 5263569
  have htrace : WordTrace (prefixWord ++ tailWord_5263569) baseStart_5263569 baseEnd_5263569 := by
    simpa [prefixWord, tailWord_5263569, baseEnd_5263569] using wordTrace_append hprefix tailTrace_5263569
  have hstable : (prefixWord ++ tailWord_5263569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263569).length < 2 ^ (prefixWord ++ tailWord_5263569).sum := by decide
  have hdescent : baseEnd_5263569 < baseStart_5263569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263595 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 5]
def baseStart_5263595 : Nat := 118140960795 + 5263595 * 2 ^ 59
def prefixEnd_5263595 : Nat := 4983230072969 + 3 ^ 40 * 5263595 * 2
def baseEnd_5263595 : Nat := 2702754205602438894055673

theorem tailTrace_5263595 : CollatzResearch.WordTrace tailWord_5263595 prefixEnd_5263595 2702754205602438894055673 := by
  unfold tailWord_5263595
  simp only [CollatzResearch.WordTrace]
  refine ⟨191979081365901740302008239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127986054243934493534672159 191979081365901740302008239)
  ·
    refine ⟨287968622048852610453012359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191979081365901740302008239 287968622048852610453012359)
    ·
      refine ⟨431952933073278915679518539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287968622048852610453012359 431952933073278915679518539)
      ·
        refine ⟨647929399609918373519277809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431952933073278915679518539 647929399609918373519277809)
        ·
          refine ⟨485947049707438780139458357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 647929399609918373519277809 485947049707438780139458357)
          ·
            refine ⟨45557535910072385638074221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 485947049707438780139458357 45557535910072385638074221)
            ·
              refine ⟨17084075966277144614277833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45557535910072385638074221 17084075966277144614277833)
              ·
                refine ⟨12813056974707858460708375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17084075966277144614277833 12813056974707858460708375)
                ·
                  refine ⟨19219585462061787691062563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12813056974707858460708375 19219585462061787691062563)
                  ·
                    refine ⟨28829378193092681536593845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19219585462061787691062563 28829378193092681536593845)
                    ·
                      refine ⟨2702754205602438894055673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28829378193092681536593845 2702754205602438894055673)
                      ·
                        rfl

theorem cell23_5263595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 5].length) (baseStart_5263595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263595 prefixEnd_5263595 := by exact prefixLift 5263595
  have htrace : WordTrace (prefixWord ++ tailWord_5263595) baseStart_5263595 baseEnd_5263595 := by
    simpa [prefixWord, tailWord_5263595, baseEnd_5263595] using wordTrace_append hprefix tailTrace_5263595
  have hstable : (prefixWord ++ tailWord_5263595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263595).length < 2 ^ (prefixWord ++ tailWord_5263595).sum := by decide
  have hdescent : baseEnd_5263595 < baseStart_5263595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263602 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_5263602 : Nat := 118140960795 + 5263602 * 2 ^ 59
def prefixEnd_5263602 : Nat := 4983230072969 + 3 ^ 40 * 5263602 * 2
def baseEnd_5263602 : Nat := 900919266655673455556047

theorem tailTrace_5263602 : CollatzResearch.WordTrace tailWord_5263602 prefixEnd_5263602 900919266655673455556047 := by
  unfold tailWord_5263602
  simp only [CollatzResearch.WordTrace]
  refine ⟨47994834169219095124378265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127986224451250920331675373 47994834169219095124378265)
  ·
    refine ⟨35996125626914321343283699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47994834169219095124378265 35996125626914321343283699)
    ·
      refine ⟨53994188440371482014925549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35996125626914321343283699 53994188440371482014925549)
      ·
        refine ⟨20247820665139305755597081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53994188440371482014925549 20247820665139305755597081)
        ·
          refine ⟨15185865498854479316697811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20247820665139305755597081 15185865498854479316697811)
          ·
            refine ⟨22778798248281718975046717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15185865498854479316697811 22778798248281718975046717)
            ·
              refine ⟨8542049343105644615642519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22778798248281718975046717 8542049343105644615642519)
              ·
                refine ⟨12813074014658466923463779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8542049343105644615642519 12813074014658466923463779)
                ·
                  refine ⟨19219611021987700385195669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12813074014658466923463779 19219611021987700385195669)
                  ·
                    refine ⟨900919266655673455556047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19219611021987700385195669 900919266655673455556047)
                    ·
                      rfl

theorem cell23_5263602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_5263602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263602 prefixEnd_5263602 := by exact prefixLift 5263602
  have htrace : WordTrace (prefixWord ++ tailWord_5263602) baseStart_5263602 baseEnd_5263602 := by
    simpa [prefixWord, tailWord_5263602, baseEnd_5263602] using wordTrace_append hprefix tailTrace_5263602
  have hstable : (prefixWord ++ tailWord_5263602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263602).length < 2 ^ (prefixWord ++ tailWord_5263602).sum := by decide
  have hdescent : baseEnd_5263602 < baseStart_5263602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263620 : List Nat := [2, 3, 2, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_5263620 : Nat := 118140960795 + 5263620 * 2 ^ 59
def prefixEnd_5263620 : Nat := 4983230072969 + 3 ^ 40 * 5263620 * 2
def baseEnd_5263620 : Nat := 2702767042618801296243059

theorem tailTrace_5263620 : CollatzResearch.WordTrace tailWord_5263620 prefixEnd_5263620 2702767042618801296243059 := by
  unfold tailWord_5263620
  simp only [CollatzResearch.WordTrace]
  refine ⟨95989996595405584785834157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127986662127207446381112209 95989996595405584785834157)
  ·
    refine ⟨35996248723277094294687809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95989996595405584785834157 35996248723277094294687809)
    ·
      refine ⟨26997186542457820721015857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35996248723277094294687809 26997186542457820721015857)
      ·
        refine ⟨20247889906843365540761893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26997186542457820721015857 20247889906843365540761893)
        ·
          refine ⟨3796479357533131038892855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20247889906843365540761893 3796479357533131038892855)
          ·
            refine ⟨5694719036299696558339283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796479357533131038892855 5694719036299696558339283)
            ·
              refine ⟨8542078554449544837508925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5694719036299696558339283 8542078554449544837508925)
              ·
                refine ⟨3203279457918579314065847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8542078554449544837508925 3203279457918579314065847)
                ·
                  refine ⟨4804919186877868971098771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3203279457918579314065847 4804919186877868971098771)
                  ·
                    refine ⟨7207378780316803456648157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4804919186877868971098771 7207378780316803456648157)
                    ·
                      refine ⟨2702767042618801296243059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7207378780316803456648157 2702767042618801296243059)
                      ·
                        rfl

theorem cell23_5263620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_5263620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263620 prefixEnd_5263620 := by exact prefixLift 5263620
  have htrace : WordTrace (prefixWord ++ tailWord_5263620) baseStart_5263620 baseEnd_5263620 := by
    simpa [prefixWord, tailWord_5263620, baseEnd_5263620] using wordTrace_append hprefix tailTrace_5263620
  have hstable : (prefixWord ++ tailWord_5263620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263620).length < 2 ^ (prefixWord ++ tailWord_5263620).sum := by decide
  have hdescent : baseEnd_5263620 < baseStart_5263620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263653 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_5263653 : Nat := 118140960795 + 5263653 * 2 ^ 59
def prefixEnd_5263653 : Nat := 4983230072969 + 3 ^ 40 * 5263653 * 2
def baseEnd_5263653 : Nat := 900927995826799889043469

theorem tailTrace_5263653 : CollatzResearch.WordTrace tailWord_5263653 prefixEnd_5263653 900927995826799889043469 := by
  unfold tailWord_5263653
  simp only [CollatzResearch.WordTrace]
  refine ⟨191981196799691616207619613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127987464533127744138413075 191981196799691616207619613)
  ·
    refine ⟨71992948799884356077857355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191981196799691616207619613 71992948799884356077857355)
    ·
      refine ⟨107989423199826534116786033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71992948799884356077857355 107989423199826534116786033)
      ·
        refine ⟨80992067399869900587589525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107989423199826534116786033 80992067399869900587589525)
        ·
          refine ⟨3796503159368901590043259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80992067399869900587589525 3796503159368901590043259)
          ·
            refine ⟨5694754739053352385064889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796503159368901590043259 5694754739053352385064889)
            ·
              refine ⟨4271066054290014288798667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5694754739053352385064889 4271066054290014288798667)
              ·
                refine ⟨6406599081435021433198001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4271066054290014288798667 6406599081435021433198001)
                ·
                  refine ⟨4804949311076266074898501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6406599081435021433198001 4804949311076266074898501)
                  ·
                    refine ⟨900927995826799889043469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804949311076266074898501 900927995826799889043469)
                    ·
                      rfl

theorem cell23_5263653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_5263653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263653 prefixEnd_5263653 := by exact prefixLift 5263653
  have htrace : WordTrace (prefixWord ++ tailWord_5263653) baseStart_5263653 baseEnd_5263653 := by
    simpa [prefixWord, tailWord_5263653, baseEnd_5263653] using wordTrace_append hprefix tailTrace_5263653
  have hstable : (prefixWord ++ tailWord_5263653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263653).length < 2 ^ (prefixWord ++ tailWord_5263653).sum := by decide
  have hdescent : baseEnd_5263653 < baseStart_5263653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263669 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_5263669 : Nat := 118140960795 + 5263669 * 2 ^ 59
def prefixEnd_5263669 : Nat := 4983230072969 + 3 ^ 40 * 5263669 * 2
def baseEnd_5263669 : Nat := 2702792203170871604530333

theorem tailTrace_5263669 : CollatzResearch.WordTrace tailWord_5263669 prefixEnd_5263669 2702792203170871604530333 := by
  unfold tailWord_5263669
  simp only [CollatzResearch.WordTrace]
  refine ⟨191981780367633650940202061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127987853578422433960134707 191981780367633650940202061)
  ·
    refine ⟨71993167637862619102575773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191981780367633650940202061 71993167637862619102575773)
    ·
      refine ⟨26997437864198482163465915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71993167637862619102575773 26997437864198482163465915)
      ·
        refine ⟨40496156796297723245198873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26997437864198482163465915 40496156796297723245198873)
        ·
          refine ⟨30372117597223292433899155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40496156796297723245198873 30372117597223292433899155)
          ·
            refine ⟨45558176395834938650848733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30372117597223292433899155 45558176395834938650848733)
            ·
              refine ⟨17084316148438101994068275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45558176395834938650848733 17084316148438101994068275)
              ·
                refine ⟨25626474222657152991102413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17084316148438101994068275 25626474222657152991102413)
                ·
                  refine ⟨9609927833496432371663405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25626474222657152991102413 9609927833496432371663405)
                  ·
                    refine ⟨3603722937561162139373777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9609927833496432371663405 3603722937561162139373777)
                    ·
                      refine ⟨2702792203170871604530333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603722937561162139373777 2702792203170871604530333)
                      ·
                        rfl

theorem cell23_5263669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_5263669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263669 prefixEnd_5263669 := by exact prefixLift 5263669
  have htrace : WordTrace (prefixWord ++ tailWord_5263669) baseStart_5263669 baseEnd_5263669 := by
    simpa [prefixWord, tailWord_5263669, baseEnd_5263669] using wordTrace_append hprefix tailTrace_5263669
  have hstable : (prefixWord ++ tailWord_5263669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263669).length < 2 ^ (prefixWord ++ tailWord_5263669).sum := by decide
  have hdescent : baseEnd_5263669 < baseStart_5263669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263705 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 7]
def baseStart_5263705 : Nat := 118140960795 + 5263705 * 2 ^ 59
def prefixEnd_5263705 : Nat := 4983230072969 + 3 ^ 40 * 5263705 * 2
def baseEnd_5263705 : Nat := 300312298719381495964463

theorem tailTrace_5263705 : CollatzResearch.WordTrace tailWord_5263705 prefixEnd_5263705 300312298719381495964463 := by
  unfold tailWord_5263705
  simp only [CollatzResearch.WordTrace]
  refine ⟨191983093395503229088512569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127988728930335486059008379 191983093395503229088512569)
  ·
    refine ⟨143987320046627421816384427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191983093395503229088512569 143987320046627421816384427)
    ·
      refine ⟨215980980069941132724576641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143987320046627421816384427 215980980069941132724576641)
      ·
        refine ⟨161985735052455849543432481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215980980069941132724576641 161985735052455849543432481)
        ·
          refine ⟨121489301289341887157574361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161985735052455849543432481 121489301289341887157574361)
          ·
            refine ⟨91116975967006415368180771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121489301289341887157574361 91116975967006415368180771)
            ·
              refine ⟨136675463950509623052271157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91116975967006415368180771 136675463950509623052271157)
              ·
                refine ⟨12813324745360277161150421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136675463950509623052271157 12813324745360277161150421)
                ·
                  refine ⟨300312298719381495964463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12813324745360277161150421 300312298719381495964463)
                  ·
                    rfl

theorem cell23_5263705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 7].length) (baseStart_5263705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263705 prefixEnd_5263705 := by exact prefixLift 5263705
  have htrace : WordTrace (prefixWord ++ tailWord_5263705) baseStart_5263705 baseEnd_5263705 := by
    simpa [prefixWord, tailWord_5263705, baseEnd_5263705] using wordTrace_append hprefix tailTrace_5263705
  have hstable : (prefixWord ++ tailWord_5263705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263705).length < 2 ^ (prefixWord ++ tailWord_5263705).sum := by decide
  have hdescent : baseEnd_5263705 < baseStart_5263705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263716 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_5263716 : Nat := 118140960795 + 5263716 * 2 ^ 59
def prefixEnd_5263716 : Nat := 4983230072969 + 3 ^ 40 * 5263716 * 2
def baseEnd_5263716 : Nat := 2702816336761632920642617

theorem tailTrace_5263716 : CollatzResearch.WordTrace tailWord_5263716 prefixEnd_5263716 2702816336761632920642617 := by
  unfold tailWord_5263716
  simp only [CollatzResearch.WordTrace]
  refine ⟨95991747299231688983581501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127988996398975585311442001 95991747299231688983581501)
  ·
    refine ⟨35996905237211883368843063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95991747299231688983581501 35996905237211883368843063)
    ·
      refine ⟨53995357855817825053264595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35996905237211883368843063 53995357855817825053264595)
      ·
        refine ⟨80993036783726737579896893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53995357855817825053264595 80993036783726737579896893)
        ·
          refine ⟨30372388793897526592461335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80993036783726737579896893 30372388793897526592461335)
          ·
            refine ⟨45558583190846289888692003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30372388793897526592461335 45558583190846289888692003)
            ·
              refine ⟨68337874786269434833038005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45558583190846289888692003 68337874786269434833038005)
              ·
                refine ⟨6406675761212759515597313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68337874786269434833038005 6406675761212759515597313)
                ·
                  refine ⟨4805006820909569636697985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6406675761212759515597313 4805006820909569636697985)
                  ·
                    refine ⟨3603755115682177227523489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4805006820909569636697985 3603755115682177227523489)
                    ·
                      refine ⟨2702816336761632920642617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603755115682177227523489 2702816336761632920642617)
                      ·
                        rfl

theorem cell23_5263716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_5263716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263716 prefixEnd_5263716 := by exact prefixLift 5263716
  have htrace : WordTrace (prefixWord ++ tailWord_5263716) baseStart_5263716 baseEnd_5263716 := by
    simpa [prefixWord, tailWord_5263716, baseEnd_5263716] using wordTrace_append hprefix tailTrace_5263716
  have hstable : (prefixWord ++ tailWord_5263716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263716).length < 2 ^ (prefixWord ++ tailWord_5263716).sum := by decide
  have hdescent : baseEnd_5263716 < baseStart_5263716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263722 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 9]
def baseStart_5263722 : Nat := 118140960795 + 5263722 * 2 ^ 59
def prefixEnd_5263722 : Nat := 4983230072969 + 3 ^ 40 * 5263722 * 2
def baseEnd_5263722 : Nat := 300313268627284433018621

theorem tailTrace_5263722 : CollatzResearch.WordTrace tailWord_5263722 prefixEnd_5263722 300313268627284433018621 := by
  unfold tailWord_5263722
  simp only [CollatzResearch.WordTrace]
  refine ⟨47995928359110410247970355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127989142290961093994587613 47995928359110410247970355)
  ·
    refine ⟨71993892538665615371955533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47995928359110410247970355 71993892538665615371955533)
    ·
      refine ⟨26997709701999605764483325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71993892538665615371955533 26997709701999605764483325)
      ·
        refine ⟨10124141138249852161681247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26997709701999605764483325 10124141138249852161681247)
        ·
          refine ⟨15186211707374778242521871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10124141138249852161681247 15186211707374778242521871)
          ·
            refine ⟨22779317561062167363782807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15186211707374778242521871 22779317561062167363782807)
            ·
              refine ⟨34168976341593251045674211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22779317561062167363782807 34168976341593251045674211)
              ·
                refine ⟨51253464512389876568511317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34168976341593251045674211 51253464512389876568511317)
                ·
                  refine ⟨300313268627284433018621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51253464512389876568511317 300313268627284433018621)
                  ·
                    rfl

theorem cell23_5263722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_5263722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263722 prefixEnd_5263722 := by exact prefixLift 5263722
  have htrace : WordTrace (prefixWord ++ tailWord_5263722) baseStart_5263722 baseEnd_5263722 := by
    simpa [prefixWord, tailWord_5263722, baseEnd_5263722] using wordTrace_append hprefix tailTrace_5263722
  have hstable : (prefixWord ++ tailWord_5263722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263722).length < 2 ^ (prefixWord ++ tailWord_5263722).sum := by decide
  have hdescent : baseEnd_5263722 < baseStart_5263722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263739 : List Nat := [1, 1, 1, 1, 1, 8, 2, 3, 5]
def baseStart_5263739 : Nat := 118140960795 + 5263739 * 2 ^ 59
def prefixEnd_5263739 : Nat := 4983230072969 + 3 ^ 40 * 5263739 * 2
def baseEnd_5263739 : Nat := 300314238535187370072779

theorem tailTrace_5263739 : CollatzResearch.WordTrace tailWord_5263739 prefixEnd_5263739 300314238535187370072779 := by
  unfold tailWord_5263739
  simp only [CollatzResearch.WordTrace]
  refine ⟨191984333477380052895250271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127989555651586701930166847 191984333477380052895250271)
  ·
    refine ⟨287976500216070079342875407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191984333477380052895250271 287976500216070079342875407)
    ·
      refine ⟨431964750324105119014313111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287976500216070079342875407 431964750324105119014313111)
      ·
        refine ⟨647947125486157678521469667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431964750324105119014313111 647947125486157678521469667)
        ·
          refine ⟨971920688229236517782204501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647947125486157678521469667 971920688229236517782204501)
          ·
            refine ⟨11389695565186365442760209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 971920688229236517782204501 11389695565186365442760209)
            ·
              refine ⟨8542271673889774082070157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11389695565186365442760209 8542271673889774082070157)
              ·
                refine ⟨3203351877708665280776309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8542271673889774082070157 3203351877708665280776309)
                ·
                  refine ⟨300314238535187370072779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3203351877708665280776309 300314238535187370072779)
                  ·
                    rfl

theorem cell23_5263739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 5].length) (baseStart_5263739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263739 prefixEnd_5263739 := by exact prefixLift 5263739
  have htrace : WordTrace (prefixWord ++ tailWord_5263739) baseStart_5263739 baseEnd_5263739 := by
    simpa [prefixWord, tailWord_5263739, baseEnd_5263739] using wordTrace_append hprefix tailTrace_5263739
  have hstable : (prefixWord ++ tailWord_5263739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263739).length < 2 ^ (prefixWord ++ tailWord_5263739).sum := by decide
  have hdescent : baseEnd_5263739 < baseStart_5263739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263752 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 4, 5]
def baseStart_5263752 : Nat := 118140960795 + 5263752 * 2 ^ 59
def prefixEnd_5263752 : Nat := 4983230072969 + 3 ^ 40 * 5263752 * 2
def baseEnd_5263752 : Nat := 900944940688398259930817

theorem tailTrace_5263752 : CollatzResearch.WordTrace tailWord_5263752 prefixEnd_5263752 900944940688398259930817 := by
  unfold tailWord_5263752
  simp only [CollatzResearch.WordTrace]
  refine ⟨95992403813166478057736755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127989871750888637410315673 95992403813166478057736755)
  ·
    refine ⟨143988605719749717086605133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95992403813166478057736755 143988605719749717086605133)
    ·
      refine ⟨53995727144906143907476925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143988605719749717086605133 53995727144906143907476925)
      ·
        refine ⟨20248397679339803965303847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53995727144906143907476925 20248397679339803965303847)
        ·
          refine ⟨30372596519009705947955771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20248397679339803965303847 30372596519009705947955771)
          ·
            refine ⟨45558894778514558921933657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30372596519009705947955771 45558894778514558921933657)
            ·
              refine ⟨34169171083885919191450243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45558894778514558921933657 34169171083885919191450243)
              ·
                refine ⟨51253756625828878787175365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34169171083885919191450243 51253756625828878787175365)
                ·
                  refine ⟨9610079367342914772595381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51253756625828878787175365 9610079367342914772595381)
                  ·
                    refine ⟨900944940688398259930817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9610079367342914772595381 900944940688398259930817)
                    ·
                      rfl

theorem cell23_5263752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_5263752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263752 prefixEnd_5263752 := by exact prefixLift 5263752
  have htrace : WordTrace (prefixWord ++ tailWord_5263752) baseStart_5263752 baseEnd_5263752 := by
    simpa [prefixWord, tailWord_5263752, baseEnd_5263752] using wordTrace_append hprefix tailTrace_5263752
  have hstable : (prefixWord ++ tailWord_5263752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263752).length < 2 ^ (prefixWord ++ tailWord_5263752).sum := by decide
  have hdescent : baseEnd_5263752 < baseStart_5263752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263816 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 3, 4]
def baseStart_5263816 : Nat := 118140960795 + 5263816 * 2 ^ 59
def prefixEnd_5263816 : Nat := 4983230072969 + 3 ^ 40 * 5263816 * 2
def baseEnd_5263816 : Nat := 900955894942360843130719

theorem tailTrace_5263816 : CollatzResearch.WordTrace tailWord_5263816 prefixEnd_5263816 900955894942360843130719 := by
  unfold tailWord_5263816
  simp only [CollatzResearch.WordTrace]
  refine ⟨95993570949050547522901651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127991427932067396697202201 95993570949050547522901651)
  ·
    refine ⟨143990356423575821284352477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95993570949050547522901651 143990356423575821284352477)
    ·
      refine ⟨53996383658840932981632179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143990356423575821284352477 53996383658840932981632179)
      ·
        refine ⟨80994575488261399472448269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53996383658840932981632179 80994575488261399472448269)
        ·
          refine ⟨30372965808098024802168101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80994575488261399472448269 30372965808098024802168101)
          ·
            refine ⟨5694931089018379650406519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30372965808098024802168101 5694931089018379650406519)
            ·
              refine ⟨8542396633527569475609779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5694931089018379650406519 8542396633527569475609779)
              ·
                refine ⟨12813594950291354213414669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8542396633527569475609779 12813594950291354213414669)
                ·
                  refine ⟨4805098106359257830030501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12813594950291354213414669 4805098106359257830030501)
                  ·
                    refine ⟨900955894942360843130719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4805098106359257830030501 900955894942360843130719)
                    ·
                      rfl

theorem cell23_5263816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_5263816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263816 prefixEnd_5263816 := by exact prefixLift 5263816
  have htrace : WordTrace (prefixWord ++ tailWord_5263816) baseStart_5263816 baseEnd_5263816 := by
    simpa [prefixWord, tailWord_5263816, baseEnd_5263816] using wordTrace_append hprefix tailTrace_5263816
  have hstable : (prefixWord ++ tailWord_5263816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263816).length < 2 ^ (prefixWord ++ tailWord_5263816).sum := by decide
  have hdescent : baseEnd_5263816 < baseStart_5263816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263829 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 6]
def baseStart_5263829 : Nat := 118140960795 + 5263829 * 2 ^ 59
def prefixEnd_5263829 : Nat := 4983230072969 + 3 ^ 40 * 5263829 * 2
def baseEnd_5263829 : Nat := 300319373341732330947733

theorem tailTrace_5263829 : CollatzResearch.WordTrace tailWord_5263829 prefixEnd_5263829 300319373341732330947733 := by
  unfold tailWord_5263829
  simp only [CollatzResearch.WordTrace]
  refine ⟨191987616047053998266026541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127991744031369332177351027 191987616047053998266026541)
  ·
    refine ⟨71995356017645249349759953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191987616047053998266026541 71995356017645249349759953)
    ·
      refine ⟨53996517013233937012319965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71995356017645249349759953 53996517013233937012319965)
      ·
        refine ⟨20248693879962726379619987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53996517013233937012319965 20248693879962726379619987)
        ·
          refine ⟨30373040819944089569429981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20248693879962726379619987 30373040819944089569429981)
          ·
            refine ⟨11389890307479033588536243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30373040819944089569429981 11389890307479033588536243)
            ·
              refine ⟨17084835461218550382804365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11389890307479033588536243 17084835461218550382804365)
              ·
                refine ⟨6406813297956956393551637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17084835461218550382804365 6406813297956956393551637)
                ·
                  refine ⟨300319373341732330947733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6406813297956956393551637 300319373341732330947733)
                  ·
                    rfl

theorem cell23_5263829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_5263829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263829 prefixEnd_5263829 := by exact prefixLift 5263829
  have htrace : WordTrace (prefixWord ++ tailWord_5263829) baseStart_5263829 baseEnd_5263829 := by
    simpa [prefixWord, tailWord_5263829, baseEnd_5263829] using wordTrace_append hprefix tailTrace_5263829
  have hstable : (prefixWord ++ tailWord_5263829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263829).length < 2 ^ (prefixWord ++ tailWord_5263829).sum := by decide
  have hdescent : baseEnd_5263829 < baseStart_5263829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263909 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_5263909 : Nat := 118140960795 + 5263909 * 2 ^ 59
def prefixEnd_5263909 : Nat := 4983230072969 + 3 ^ 40 * 5263909 * 2
def baseEnd_5263909 : Nat := 2702915438527950665529229

theorem tailTrace_5263909 : CollatzResearch.WordTrace tailWord_5263909 prefixEnd_5263909 2702915438527950665529229 := by
  unfold tailWord_5263909
  simp only [CollatzResearch.WordTrace]
  refine ⟨191990533886764171928938781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127993689257842781285959187 191990533886764171928938781)
  ·
    refine ⟨71996450207536564473352043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191990533886764171928938781 71996450207536564473352043)
    ·
      refine ⟨107994675311304846710028065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71996450207536564473352043 107994675311304846710028065)
      ·
        refine ⟨80996006483478635032521049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107994675311304846710028065 80996006483478635032521049)
        ·
          refine ⟨60747004862608976274390787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80996006483478635032521049 60747004862608976274390787)
          ·
            refine ⟨91120507293913464411586181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60747004862608976274390787 91120507293913464411586181)
            ·
              refine ⟨17085095117608774577172409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91120507293913464411586181 17085095117608774577172409)
              ·
                refine ⟨12813821338206580932879307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17085095117608774577172409 12813821338206580932879307)
                ·
                  refine ⟨19220732007309871399318961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12813821338206580932879307 19220732007309871399318961)
                  ·
                    refine ⟨14415549005482403549489221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19220732007309871399318961 14415549005482403549489221)
                    ·
                      refine ⟨2702915438527950665529229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14415549005482403549489221 2702915438527950665529229)
                      ·
                        rfl

theorem cell23_5263909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_5263909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263909 prefixEnd_5263909 := by exact prefixLift 5263909
  have htrace : WordTrace (prefixWord ++ tailWord_5263909) baseStart_5263909 baseEnd_5263909 := by
    simpa [prefixWord, tailWord_5263909, baseEnd_5263909] using wordTrace_append hprefix tailTrace_5263909
  have hstable : (prefixWord ++ tailWord_5263909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263909).length < 2 ^ (prefixWord ++ tailWord_5263909).sum := by decide
  have hdescent : baseEnd_5263909 < baseStart_5263909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263930 : List Nat := [3, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2]
def baseStart_5263930 : Nat := 118140960795 + 5263930 * 2 ^ 59
def prefixEnd_5263930 : Nat := 4983230072969 + 3 ^ 40 * 5263930 * 2
def baseEnd_5263930 : Nat := 2702926221621695083366633

theorem tailTrace_5263930 : CollatzResearch.WordTrace tailWord_5263930 prefixEnd_5263930 2702926221621695083366633 := by
  unfold tailWord_5263930
  simp only [CollatzResearch.WordTrace]
  refine ⟨47997824954922023128863311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127994199879792061676968829 47997824954922023128863311)
  ·
    refine ⟨71996737432383034693294967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47997824954922023128863311 71996737432383034693294967)
    ·
      refine ⟨107995106148574552039942451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71996737432383034693294967 107995106148574552039942451)
      ·
        refine ⟨161992659222861828059913677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107995106148574552039942451 161992659222861828059913677)
        ·
          refine ⟨60747247208573185522467629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161992659222861828059913677 60747247208573185522467629)
          ·
            refine ⟨22780217703214944570925361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60747247208573185522467629 22780217703214944570925361)
            ·
              refine ⟨17085163277411208428194021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22780217703214944570925361 17085163277411208428194021)
              ·
                refine ⟨3203468114514601580286379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17085163277411208428194021 3203468114514601580286379)
                ·
                  refine ⟨4805202171771902370429569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3203468114514601580286379 4805202171771902370429569)
                  ·
                    refine ⟨3603901628828926777822177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4805202171771902370429569 3603901628828926777822177)
                    ·
                      refine ⟨2702926221621695083366633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603901628828926777822177 2702926221621695083366633)
                      ·
                        rfl

theorem cell23_5263930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_5263930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263930 prefixEnd_5263930 := by exact prefixLift 5263930
  have htrace : WordTrace (prefixWord ++ tailWord_5263930) baseStart_5263930 baseEnd_5263930 := by
    simpa [prefixWord, tailWord_5263930, baseEnd_5263930] using wordTrace_append hprefix tailTrace_5263930
  have hstable : (prefixWord ++ tailWord_5263930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263930).length < 2 ^ (prefixWord ++ tailWord_5263930).sum := by decide
  have hdescent : baseEnd_5263930 < baseStart_5263930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263946 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_5263946 : Nat := 118140960795 + 5263946 * 2 ^ 59
def prefixEnd_5263946 : Nat := 4983230072969 + 3 ^ 40 * 5263946 * 2
def baseEnd_5263946 : Nat := 2702934437312167020766559

theorem tailTrace_5263946 : CollatzResearch.WordTrace tailWord_5263946 prefixEnd_5263946 2702934437312167020766559 := by
  unfold tailWord_5263946
  simp only [CollatzResearch.WordTrace]
  refine ⟨47997970846907531812008923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127994588925086751498690461 47997970846907531812008923)
  ·
    refine ⟨71996956270361297718013385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47997970846907531812008923 71996956270361297718013385)
    ·
      refine ⟨53997717202770973288510039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71996956270361297718013385 53997717202770973288510039)
      ·
        refine ⟨80996575804156459932765059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53997717202770973288510039 80996575804156459932765059)
        ·
          refine ⟨121494863706234689899147589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80996575804156459932765059 121494863706234689899147589)
          ·
            refine ⟨22780286944919004356090173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121494863706234689899147589 22780286944919004356090173)
            ·
              refine ⟨8542607604344626633533815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22780286944919004356090173 8542607604344626633533815)
              ·
                refine ⟨12813911406516939950300723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8542607604344626633533815 12813911406516939950300723)
                ·
                  refine ⟨19220867109775409925451085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12813911406516939950300723 19220867109775409925451085)
                  ·
                    refine ⟨7207825166165778722044157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19220867109775409925451085 7207825166165778722044157)
                    ·
                      refine ⟨2702934437312167020766559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7207825166165778722044157 2702934437312167020766559)
                      ·
                        rfl

theorem cell23_5263946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_5263946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263946 prefixEnd_5263946 := by exact prefixLift 5263946
  have htrace : WordTrace (prefixWord ++ tailWord_5263946) baseStart_5263946 baseEnd_5263946 := by
    simpa [prefixWord, tailWord_5263946, baseEnd_5263946] using wordTrace_append hprefix tailTrace_5263946
  have hstable : (prefixWord ++ tailWord_5263946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263946).length < 2 ^ (prefixWord ++ tailWord_5263946).sum := by decide
  have hdescent : baseEnd_5263946 < baseStart_5263946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263952 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_5263952 : Nat := 118140960795 + 5263952 * 2 ^ 59
def prefixEnd_5263952 : Nat := 4983230072969 + 3 ^ 40 * 5263952 * 2
def baseEnd_5263952 : Nat := 2702937518196093997291531

theorem tailTrace_5263952 : CollatzResearch.WordTrace tailWord_5263952 prefixEnd_5263952 2702937518196093997291531 := by
  unfold tailWord_5263952
  simp only [CollatzResearch.WordTrace]
  refine ⟨95996051112804195136377055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127994734817072260181836073 95996051112804195136377055)
  ·
    refine ⟨143994076669206292704565583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95996051112804195136377055 143994076669206292704565583)
    ·
      refine ⟨215991115003809439056848375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143994076669206292704565583 215991115003809439056848375)
      ·
        refine ⟨323986672505714158585272563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215991115003809439056848375 323986672505714158585272563)
        ·
          refine ⟨485980008758571237877908845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323986672505714158585272563 485980008758571237877908845)
          ·
            refine ⟨182242503284464214204215817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 485980008758571237877908845 182242503284464214204215817)
            ·
              refine ⟨136681877463348160653161863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182242503284464214204215817 136681877463348160653161863)
              ·
                refine ⟨205022816195022240979742795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136681877463348160653161863 205022816195022240979742795)
                ·
                  refine ⟨307534224292533361469614193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205022816195022240979742795 307534224292533361469614193)
                  ·
                    refine ⟨230650668219400021102210645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 307534224292533361469614193 230650668219400021102210645)
                    ·
                      refine ⟨2702937518196093997291531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 230650668219400021102210645 2702937518196093997291531)
                      ·
                        rfl

theorem cell23_5263952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_5263952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263952 prefixEnd_5263952 := by exact prefixLift 5263952
  have htrace : WordTrace (prefixWord ++ tailWord_5263952) baseStart_5263952 baseEnd_5263952 := by
    simpa [prefixWord, tailWord_5263952, baseEnd_5263952] using wordTrace_append hprefix tailTrace_5263952
  have hstable : (prefixWord ++ tailWord_5263952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263952).length < 2 ^ (prefixWord ++ tailWord_5263952).sum := by decide
  have hdescent : baseEnd_5263952 < baseStart_5263952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263964 : List Nat := [2, 2, 4, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_5263964 : Nat := 118140960795 + 5263964 * 2 ^ 59
def prefixEnd_5263964 : Nat := 4983230072969 + 3 ^ 40 * 5263964 * 2
def baseEnd_5263964 : Nat := 2702943679963947950341477

theorem tailTrace_5263964 : CollatzResearch.WordTrace tailWord_5263964 prefixEnd_5263964 2702943679963947950341477 := by
  unfold tailWord_5263964
  simp only [CollatzResearch.WordTrace]
  refine ⟨95996269950782458161095473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127995026601043277548127297 95996269950782458161095473)
  ·
    refine ⟨71997202463086843620821605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95996269950782458161095473 71997202463086843620821605)
    ·
      refine ⟨13499475461828783178904051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71997202463086843620821605 13499475461828783178904051)
      ·
        refine ⟨20249213192743174768356077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13499475461828783178904051 20249213192743174768356077)
        ·
          refine ⟨7593454947278690538133529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20249213192743174768356077 7593454947278690538133529)
          ·
            refine ⟨5695091210459017903600147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7593454947278690538133529 5695091210459017903600147)
            ·
              refine ⟨8542636815688526855400221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5695091210459017903600147 8542636815688526855400221)
              ·
                refine ⟨3203488805883197570775083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8542636815688526855400221 3203488805883197570775083)
                ·
                  refine ⟨4805233208824796356162625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3203488805883197570775083 4805233208824796356162625)
                  ·
                    refine ⟨3603924906618597267121969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4805233208824796356162625 3603924906618597267121969)
                    ·
                      refine ⟨2702943679963947950341477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603924906618597267121969 2702943679963947950341477)
                      ·
                        rfl

theorem cell23_5263964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_5263964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263964 prefixEnd_5263964 := by exact prefixLift 5263964
  have htrace : WordTrace (prefixWord ++ tailWord_5263964) baseStart_5263964 baseEnd_5263964 := by
    simpa [prefixWord, tailWord_5263964, baseEnd_5263964] using wordTrace_append hprefix tailTrace_5263964
  have hstable : (prefixWord ++ tailWord_5263964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263964).length < 2 ^ (prefixWord ++ tailWord_5263964).sum := by decide
  have hdescent : baseEnd_5263964 < baseStart_5263964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5263997 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_5263997 : Nat := 118140960795 + 5263997 * 2 ^ 59
def prefixEnd_5263997 : Nat := 4983230072969 + 3 ^ 40 * 5263997 * 2
def baseEnd_5263997 : Nat := 2702960624825546321228825

theorem tailTrace_5263997 : CollatzResearch.WordTrace tailWord_5263997 prefixEnd_5263997 2702960624825546321228825 := by
  unfold tailWord_5263997
  simp only [CollatzResearch.WordTrace]
  refine ⟨191993743510445362958142245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127995829006963575305428163 191993743510445362958142245)
  ·
    refine ⟨35998826908208505554651671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191993743510445362958142245 35998826908208505554651671)
    ·
      refine ⟨53998240362312758331977507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35998826908208505554651671 53998240362312758331977507)
      ·
        refine ⟨80997360543469137497966261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53998240362312758331977507 80997360543469137497966261)
        ·
          refine ⟨7593502550950231640434337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80997360543469137497966261 7593502550950231640434337)
          ·
            refine ⟨5695126913212673730325753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7593502550950231640434337 5695126913212673730325753)
            ·
              refine ⟨4271345184909505297744315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5695126913212673730325753 4271345184909505297744315)
              ·
                refine ⟨6407017777364257946616473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4271345184909505297744315 6407017777364257946616473)
                ·
                  refine ⟨4805263333023193459962355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6407017777364257946616473 4805263333023193459962355)
                  ·
                    refine ⟨7207894999534790189943533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4805263333023193459962355 7207894999534790189943533)
                    ·
                      refine ⟨2702960624825546321228825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7207894999534790189943533 2702960624825546321228825)
                      ·
                        rfl

theorem cell23_5263997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_5263997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5263997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5263997 prefixEnd_5263997 := by exact prefixLift 5263997
  have htrace : WordTrace (prefixWord ++ tailWord_5263997) baseStart_5263997 baseEnd_5263997 := by
    simpa [prefixWord, tailWord_5263997, baseEnd_5263997] using wordTrace_append hprefix tailTrace_5263997
  have hstable : (prefixWord ++ tailWord_5263997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5263997).length < 2 ^ (prefixWord ++ tailWord_5263997).sum := by decide
  have hdescent : baseEnd_5263997 < baseStart_5263997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5263997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264019 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 3]
def baseStart_5264019 : Nat := 118140960795 + 5264019 * 2 ^ 59
def prefixEnd_5264019 : Nat := 4983230072969 + 3 ^ 40 * 5264019 * 2
def baseEnd_5264019 : Nat := 2702971921399945235153723

theorem tailTrace_5264019 : CollatzResearch.WordTrace tailWord_5264019 prefixEnd_5264019 2702971921399945235153723 := by
  unfold tailWord_5264019
  simp only [CollatzResearch.WordTrace]
  refine ⟨191994545916365660715443111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127996363944243773810295407 191994545916365660715443111)
  ·
    refine ⟨287991818874548491073164667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191994545916365660715443111 287991818874548491073164667)
    ·
      refine ⟨431987728311822736609747001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287991818874548491073164667 431987728311822736609747001)
      ·
        refine ⟨323990796233867052457310251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431987728311822736609747001 323990796233867052457310251)
        ·
          refine ⟨485986194350800578685965377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323990796233867052457310251 485986194350800578685965377)
          ·
            refine ⟨364489645763100434014474033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485986194350800578685965377 364489645763100434014474033)
            ·
              refine ⟨273367234322325325510855525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364489645763100434014474033 273367234322325325510855525)
              ·
                refine ⟨51256356435435998533285411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273367234322325325510855525 51256356435435998533285411)
                ·
                  refine ⟨76884534653153997799928117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51256356435435998533285411 76884534653153997799928117)
                  ·
                    refine ⟨7207925123733187293743261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76884534653153997799928117 7207925123733187293743261)
                    ·
                      refine ⟨2702971921399945235153723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7207925123733187293743261 2702971921399945235153723)
                      ·
                        rfl

theorem cell23_5264019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_5264019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264019 prefixEnd_5264019 := by exact prefixLift 5264019
  have htrace : WordTrace (prefixWord ++ tailWord_5264019) baseStart_5264019 baseEnd_5264019 := by
    simpa [prefixWord, tailWord_5264019, baseEnd_5264019] using wordTrace_append hprefix tailTrace_5264019
  have hstable : (prefixWord ++ tailWord_5264019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264019).length < 2 ^ (prefixWord ++ tailWord_5264019).sum := by decide
  have hdescent : baseEnd_5264019 < baseStart_5264019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264020 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_5264020 : Nat := 118140960795 + 5264020 * 2 ^ 59
def prefixEnd_5264020 : Nat := 4983230072969 + 3 ^ 40 * 5264020 * 2
def baseEnd_5264020 : Nat := 2702972434880599731241219

theorem tailTrace_5264020 : CollatzResearch.WordTrace tailWord_5264020 prefixEnd_5264020 2702972434880599731241219 := by
  unfold tailWord_5264020
  simp only [CollatzResearch.WordTrace]
  refine ⟨95997291194681018943114757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127996388259574691924153009 95997291194681018943114757)
  ·
    refine ⟨17999492099002691051834017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95997291194681018943114757 17999492099002691051834017)
    ·
      refine ⟨13499619074252018288875513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17999492099002691051834017 13499619074252018288875513)
      ·
        refine ⟨10124714305689013716656635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13499619074252018288875513 10124714305689013716656635)
        ·
          refine ⟨15187071458533520574984953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10124714305689013716656635 15187071458533520574984953)
          ·
            refine ⟨11390303593900140431238715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15187071458533520574984953 11390303593900140431238715)
            ·
              refine ⟨17085455390850210646858073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11390303593900140431238715 17085455390850210646858073)
              ·
                refine ⟨12814091543137657985143555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17085455390850210646858073 12814091543137657985143555)
                ·
                  refine ⟨19221137314706486977715333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12814091543137657985143555 19221137314706486977715333)
                  ·
                    refine ⟨3603963246507466308321625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19221137314706486977715333 3603963246507466308321625)
                    ·
                      refine ⟨2702972434880599731241219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3603963246507466308321625 2702972434880599731241219)
                      ·
                        rfl

theorem cell23_5264020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_5264020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264020 prefixEnd_5264020 := by exact prefixLift 5264020
  have htrace : WordTrace (prefixWord ++ tailWord_5264020) baseStart_5264020 baseEnd_5264020 := by
    simpa [prefixWord, tailWord_5264020, baseEnd_5264020] using wordTrace_append hprefix tailTrace_5264020
  have hstable : (prefixWord ++ tailWord_5264020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264020).length < 2 ^ (prefixWord ++ tailWord_5264020).sum := by decide
  have hdescent : baseEnd_5264020 < baseStart_5264020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264036 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_5264036 : Nat := 118140960795 + 5264036 * 2 ^ 59
def prefixEnd_5264036 : Nat := 4983230072969 + 3 ^ 40 * 5264036 * 2
def baseEnd_5264036 : Nat := 2702980650571071668641145

theorem tailTrace_5264036 : CollatzResearch.WordTrace tailWord_5264036 prefixEnd_5264036 2702980650571071668641145 := by
  unfold tailWord_5264036
  simp only [CollatzResearch.WordTrace]
  refine ⟨95997582978652036309405981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127996777304869381745874641 95997582978652036309405981)
  ·
    refine ⟨35999093616994513616027243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95997582978652036309405981 35999093616994513616027243)
    ·
      refine ⟨53998640425491770424040865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35999093616994513616027243 53998640425491770424040865)
      ·
        refine ⟨40498980319118827818030649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53998640425491770424040865 40498980319118827818030649)
        ·
          refine ⟨30374235239339120863522987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40498980319118827818030649 30374235239339120863522987)
          ·
            refine ⟨45561352859008681295284481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30374235239339120863522987 45561352859008681295284481)
            ·
              refine ⟨34171014644256510971463361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45561352859008681295284481 34171014644256510971463361)
              ·
                refine ⟨25628260983192383228597521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34171014644256510971463361 25628260983192383228597521)
                ·
                  refine ⟨19221195737394287421448141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25628260983192383228597521 19221195737394287421448141)
                  ·
                    refine ⟨7207948401522857783043053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19221195737394287421448141 7207948401522857783043053)
                    ·
                      refine ⟨2702980650571071668641145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7207948401522857783043053 2702980650571071668641145)
                      ·
                        rfl

theorem cell23_5264036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_5264036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264036 prefixEnd_5264036 := by exact prefixLift 5264036
  have htrace : WordTrace (prefixWord ++ tailWord_5264036) baseStart_5264036 baseEnd_5264036 := by
    simpa [prefixWord, tailWord_5264036, baseEnd_5264036] using wordTrace_append hprefix tailTrace_5264036
  have hstable : (prefixWord ++ tailWord_5264036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264036).length < 2 ^ (prefixWord ++ tailWord_5264036).sum := by decide
  have hdescent : baseEnd_5264036 < baseStart_5264036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264053 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_5264053 : Nat := 118140960795 + 5264053 * 2 ^ 59
def prefixEnd_5264053 : Nat := 4983230072969 + 3 ^ 40 * 5264053 * 2
def baseEnd_5264053 : Nat := 2702989379742198102128567

theorem tailTrace_5264053 : CollatzResearch.WordTrace tailWord_5264053 prefixEnd_5264053 2702989379742198102128567 := by
  unfold tailWord_5264053
  simp only [CollatzResearch.WordTrace]
  refine ⟨191995785998242484522180813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127997190665494989681453875 191995785998242484522180813)
  ·
    refine ⟨71998419749340931695817805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191995785998242484522180813 71998419749340931695817805)
    ·
      refine ⟨26999407406002849385931677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71998419749340931695817805 26999407406002849385931677)
      ·
        refine ⟨10124777777251068519724379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26999407406002849385931677 10124777777251068519724379)
        ·
          refine ⟨15187166665876602779586569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10124777777251068519724379 15187166665876602779586569)
          ·
            refine ⟨11390374999407452084689927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15187166665876602779586569 11390374999407452084689927)
            ·
              refine ⟨17085562499111178127034891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11390374999407452084689927 17085562499111178127034891)
              ·
                refine ⟨25628343748666767190552337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17085562499111178127034891 25628343748666767190552337)
                ·
                  refine ⟨19221257811500075392914253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25628343748666767190552337 19221257811500075392914253)
                  ·
                    refine ⟨7207971679312528272342845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19221257811500075392914253 7207971679312528272342845)
                    ·
                      refine ⟨2702989379742198102128567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7207971679312528272342845 2702989379742198102128567)
                      ·
                        rfl

theorem cell23_5264053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_5264053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264053 prefixEnd_5264053 := by exact prefixLift 5264053
  have htrace : WordTrace (prefixWord ++ tailWord_5264053) baseStart_5264053 baseEnd_5264053 := by
    simpa [prefixWord, tailWord_5264053, baseEnd_5264053] using wordTrace_append hprefix tailTrace_5264053
  have hstable : (prefixWord ++ tailWord_5264053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264053).length < 2 ^ (prefixWord ++ tailWord_5264053).sum := by decide
  have hdescent : baseEnd_5264053 < baseStart_5264053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264077 : List Nat := [1, 6, 2, 1, 2, 1, 2, 3, 5]
def baseStart_5264077 : Nat := 118140960795 + 5264077 * 2 ^ 59
def prefixEnd_5264077 : Nat := 4983230072969 + 3 ^ 40 * 5264077 * 2
def baseEnd_5264077 : Nat := 300333522586434000914273

theorem tailTrace_5264077 : CollatzResearch.WordTrace tailWord_5264077 prefixEnd_5264077 300333522586434000914273 := by
  unfold tailWord_5264077
  simp only [CollatzResearch.WordTrace]
  refine ⟨191996661350155536621054485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127997774233437024414036323 191996661350155536621054485)
  ·
    refine ⟨8999843500788540779111929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191996661350155536621054485 8999843500788540779111929)
    ·
      refine ⟨6749882625591405584333947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8999843500788540779111929 6749882625591405584333947)
      ·
        refine ⟨10124823938387108376500921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6749882625591405584333947 10124823938387108376500921)
        ·
          refine ⟨7593617953790331282375691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10124823938387108376500921 7593617953790331282375691)
          ·
            refine ⟨11390426930685496923563537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7593617953790331282375691 11390426930685496923563537)
            ·
              refine ⟨8542820198014122692672653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11390426930685496923563537 8542820198014122692672653)
              ·
                refine ⟨3203557574255296009752245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8542820198014122692672653 3203557574255296009752245)
                ·
                  refine ⟨300333522586434000914273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3203557574255296009752245 300333522586434000914273)
                  ·
                    rfl

theorem cell23_5264077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_5264077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264077 prefixEnd_5264077 := by exact prefixLift 5264077
  have htrace : WordTrace (prefixWord ++ tailWord_5264077) baseStart_5264077 baseEnd_5264077 := by
    simpa [prefixWord, tailWord_5264077, baseEnd_5264077] using wordTrace_append hprefix tailTrace_5264077
  have hstable : (prefixWord ++ tailWord_5264077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264077).length < 2 ^ (prefixWord ++ tailWord_5264077).sum := by decide
  have hdescent : baseEnd_5264077 < baseStart_5264077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264089 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_5264089 : Nat := 118140960795 + 5264089 * 2 ^ 59
def prefixEnd_5264089 : Nat := 4983230072969 + 3 ^ 40 * 5264089 * 2
def baseEnd_5264089 : Nat := 2703007865045759961278401

theorem tailTrace_5264089 : CollatzResearch.WordTrace tailWord_5264089 prefixEnd_5264089 2703007865045759961278401 := by
  unfold tailWord_5264089
  simp only [CollatzResearch.WordTrace]
  refine ⟨191997099026112062670491321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127998066017408041780327547 191997099026112062670491321)
  ·
    refine ⟨143997824269584047002868491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191997099026112062670491321 143997824269584047002868491)
    ·
      refine ⟨215996736404376070504302737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143997824269584047002868491 215996736404376070504302737)
      ·
        refine ⟨161997552303282052878227053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215996736404376070504302737 161997552303282052878227053)
        ·
          refine ⟨60749082113730769829335145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161997552303282052878227053 60749082113730769829335145)
          ·
            refine ⟨45561811585298077372001359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60749082113730769829335145 45561811585298077372001359)
            ·
              refine ⟨68342717377947116058002039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45561811585298077372001359 68342717377947116058002039)
              ·
                refine ⟨102514076066920674087003059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68342717377947116058002039 102514076066920674087003059)
                ·
                  refine ⟨153771114100381011130504589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102514076066920674087003059 153771114100381011130504589)
                  ·
                    refine ⟨57664167787642879173939221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153771114100381011130504589 57664167787642879173939221)
                    ·
                      refine ⟨2703007865045759961278401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57664167787642879173939221 2703007865045759961278401)
                      ·
                        rfl

theorem cell23_5264089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_5264089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264089 prefixEnd_5264089 := by exact prefixLift 5264089
  have htrace : WordTrace (prefixWord ++ tailWord_5264089) baseStart_5264089 baseEnd_5264089 := by
    simpa [prefixWord, tailWord_5264089, baseEnd_5264089] using wordTrace_append hprefix tailTrace_5264089
  have hstable : (prefixWord ++ tailWord_5264089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264089).length < 2 ^ (prefixWord ++ tailWord_5264089).sum := by decide
  have hdescent : baseEnd_5264089 < baseStart_5264089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264096 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 3]
def baseStart_5264096 : Nat := 118140960795 + 5264096 * 2 ^ 59
def prefixEnd_5264096 : Nat := 4983230072969 + 3 ^ 40 * 5264096 * 2
def baseEnd_5264096 : Nat := 2703011459410341433890869

theorem tailTrace_5264096 : CollatzResearch.WordTrace tailWord_5264096 prefixEnd_5264096 2703011459410341433890869 := by
  unfold tailWord_5264096
  simp only [CollatzResearch.WordTrace]
  refine ⟨95998677168543351432998071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127998236224724468577330761 95998677168543351432998071)
  ·
    refine ⟨143998015752815027149497107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95998677168543351432998071 143998015752815027149497107)
    ·
      refine ⟨215997023629222540724245661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143998015752815027149497107 215997023629222540724245661)
      ·
        refine ⟨80998883860958452771592123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215997023629222540724245661 80998883860958452771592123)
        ·
          refine ⟨121498325791437679157388185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80998883860958452771592123 121498325791437679157388185)
          ·
            refine ⟨91123744343578259368041139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121498325791437679157388185 91123744343578259368041139)
            ·
              refine ⟨136685616515367389052061709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91123744343578259368041139 136685616515367389052061709)
              ·
                refine ⟨51257106193262770894523141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136685616515367389052061709 51257106193262770894523141)
                ·
                  refine ⟨9610707411236769542723089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51257106193262770894523141 9610707411236769542723089)
                  ·
                    refine ⟨7208030558427577157042317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9610707411236769542723089 7208030558427577157042317)
                    ·
                      refine ⟨2703011459410341433890869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208030558427577157042317 2703011459410341433890869)
                      ·
                        rfl

theorem cell23_5264096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_5264096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264096 prefixEnd_5264096 := by exact prefixLift 5264096
  have htrace : WordTrace (prefixWord ++ tailWord_5264096) baseStart_5264096 baseEnd_5264096 := by
    simpa [prefixWord, tailWord_5264096, baseEnd_5264096] using wordTrace_append hprefix tailTrace_5264096
  have hstable : (prefixWord ++ tailWord_5264096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264096).length < 2 ^ (prefixWord ++ tailWord_5264096).sum := by decide
  have hdescent : baseEnd_5264096 < baseStart_5264096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264119 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_5264119 : Nat := 118140960795 + 5264119 * 2 ^ 59
def prefixEnd_5264119 : Nat := 4983230072969 + 3 ^ 40 * 5264119 * 2
def baseEnd_5264119 : Nat := 2703023269465394843903263

theorem tailTrace_5264119 : CollatzResearch.WordTrace tailWord_5264119 prefixEnd_5264119 2703023269465394843903263 := by
  unfold tailWord_5264119
  simp only [CollatzResearch.WordTrace]
  refine ⟨191998193216003377794083411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127998795477335585196055607 191998193216003377794083411)
  ·
    refine ⟨287997289824005066691125117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191998193216003377794083411 287997289824005066691125117)
    ·
      refine ⟨107998983684001900009171919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287997289824005066691125117 107998983684001900009171919)
      ·
        refine ⟨161998475526002850013757879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107998983684001900009171919 161998475526002850013757879)
        ·
          refine ⟨242997713289004275020636819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161998475526002850013757879 242997713289004275020636819)
          ·
            refine ⟨364496569933506412530955229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242997713289004275020636819 364496569933506412530955229)
            ·
              refine ⟨136686213725064904699108211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364496569933506412530955229 136686213725064904699108211)
              ·
                refine ⟨205029320587597357048662317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136686213725064904699108211 205029320587597357048662317)
                ·
                  refine ⟨76885995220349008893248369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205029320587597357048662317 76885995220349008893248369)
                  ·
                    refine ⟨57664496415261756669936277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76885995220349008893248369 57664496415261756669936277)
                    ·
                      refine ⟨2703023269465394843903263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57664496415261756669936277 2703023269465394843903263)
                      ·
                        rfl

theorem cell23_5264119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_5264119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264119 prefixEnd_5264119 := by exact prefixLift 5264119
  have htrace : WordTrace (prefixWord ++ tailWord_5264119) baseStart_5264119 baseEnd_5264119 := by
    simpa [prefixWord, tailWord_5264119, baseEnd_5264119] using wordTrace_append hprefix tailTrace_5264119
  have hstable : (prefixWord ++ tailWord_5264119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264119).length < 2 ^ (prefixWord ++ tailWord_5264119).sum := by decide
  have hdescent : baseEnd_5264119 < baseStart_5264119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264160 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5264160 : Nat := 118140960795 + 5264160 * 2 ^ 59
def prefixEnd_5264160 : Nat := 4983230072969 + 3 ^ 40 * 5264160 * 2
def baseEnd_5264160 : Nat := 2703044322172229183490575

theorem tailTrace_5264160 : CollatzResearch.WordTrace tailWord_5264160 prefixEnd_5264160 2703044322172229183490575 := by
  unfold tailWord_5264160
  simp only [CollatzResearch.WordTrace]
  refine ⟨95999844304427420898162967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127999792405903227864217289 95999844304427420898162967)
  ·
    refine ⟨143999766456641131347244451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95999844304427420898162967 143999766456641131347244451)
    ·
      refine ⟨215999649684961697020866677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143999766456641131347244451 215999649684961697020866677)
      ·
        refine ⟨20249967157965159095706251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215999649684961697020866677 20249967157965159095706251)
        ·
          refine ⟨30374950736947738643559377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20249967157965159095706251 30374950736947738643559377)
          ·
            refine ⟨22781213052710803982669533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30374950736947738643559377 22781213052710803982669533)
            ·
              refine ⟨8542954894766551493501075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22781213052710803982669533 8542954894766551493501075)
              ·
                refine ⟨12814432342149827240251613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8542954894766551493501075 12814432342149827240251613)
                ·
                  refine ⟨4805412128306185215094355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12814432342149827240251613 4805412128306185215094355)
                  ·
                    refine ⟨7208118192459277822641533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4805412128306185215094355 7208118192459277822641533)
                    ·
                      refine ⟨2703044322172229183490575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208118192459277822641533 2703044322172229183490575)
                      ·
                        rfl

theorem cell23_5264160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5264160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264160 prefixEnd_5264160 := by exact prefixLift 5264160
  have htrace : WordTrace (prefixWord ++ tailWord_5264160) baseStart_5264160 baseEnd_5264160 := by
    simpa [prefixWord, tailWord_5264160, baseEnd_5264160] using wordTrace_append hprefix tailTrace_5264160
  have hstable : (prefixWord ++ tailWord_5264160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264160).length < 2 ^ (prefixWord ++ tailWord_5264160).sum := by decide
  have hdescent : baseEnd_5264160 < baseStart_5264160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264180 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_5264180 : Nat := 118140960795 + 5264180 * 2 ^ 59
def prefixEnd_5264180 : Nat := 4983230072969 + 3 ^ 40 * 5264180 * 2
def baseEnd_5264180 : Nat := 901018197261773035080161

theorem tailTrace_5264180 : CollatzResearch.WordTrace tailWord_5264180 prefixEnd_5264180 901018197261773035080161 := by
  unfold tailWord_5264180
  simp only [CollatzResearch.WordTrace]
  refine ⟨96000209034391192606026997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128000278712521590141369329 96000209034391192606026997)
  ·
    refine ⟨9000019596974174306815031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96000209034391192606026997 9000019596974174306815031)
    ·
      refine ⟨13500029395461261460222547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9000019596974174306815031 13500029395461261460222547)
      ·
        refine ⟨20250044093191892190333821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13500029395461261460222547 20250044093191892190333821)
        ·
          refine ⟨7593766534946959571375183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20250044093191892190333821 7593766534946959571375183)
          ·
            refine ⟨11390649802420439357062775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7593766534946959571375183 11390649802420439357062775)
            ·
              refine ⟨17085974703630659035594163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11390649802420439357062775 17085974703630659035594163)
              ·
                refine ⟨25628962055445988553391245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17085974703630659035594163 25628962055445988553391245)
                ·
                  refine ⟨9610860770792245707521717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25628962055445988553391245 9610860770792245707521717)
                  ·
                    refine ⟨901018197261773035080161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9610860770792245707521717 901018197261773035080161)
                    ·
                      rfl

theorem cell23_5264180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_5264180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264180 prefixEnd_5264180 := by exact prefixLift 5264180
  have htrace : WordTrace (prefixWord ++ tailWord_5264180) baseStart_5264180 baseEnd_5264180 := by
    simpa [prefixWord, tailWord_5264180, baseEnd_5264180] using wordTrace_append hprefix tailTrace_5264180
  have hstable : (prefixWord ++ tailWord_5264180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264180).length < 2 ^ (prefixWord ++ tailWord_5264180).sum := by decide
  have hdescent : baseEnd_5264180 < baseStart_5264180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264200 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_5264200 : Nat := 118140960795 + 5264200 * 2 ^ 59
def prefixEnd_5264200 : Nat := 4983230072969 + 3 ^ 40 * 5264200 * 2
def baseEnd_5264200 : Nat := 2703064861398409026990391

theorem tailTrace_5264200 : CollatzResearch.WordTrace tailWord_5264200 prefixEnd_5264200 2703064861398409026990391 := by
  unfold tailWord_5264200
  simp only [CollatzResearch.WordTrace]
  refine ⟨96000573764354964313891027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128000765019139952418521369 96000573764354964313891027)
  ·
    refine ⟨144000860646532446470836541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96000573764354964313891027 144000860646532446470836541)
    ·
      refine ⟨54000322742449667426563703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144000860646532446470836541 54000322742449667426563703)
      ·
        refine ⟨81000484113674501139845555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54000322742449667426563703 81000484113674501139845555)
        ·
          refine ⟨121500726170511751709768333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81000484113674501139845555 121500726170511751709768333)
          ·
            refine ⟨45562772313941906891163125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121500726170511751709768333 45562772313941906891163125)
            ·
              refine ⟨4271509904432053771046543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45562772313941906891163125 4271509904432053771046543)
              ·
                refine ⟨6407264856648080656569815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4271509904432053771046543 6407264856648080656569815)
                ·
                  refine ⟨9610897284972120984854723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6407264856648080656569815 9610897284972120984854723)
                  ·
                    refine ⟨14416345927458181477282085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9610897284972120984854723 14416345927458181477282085)
                    ·
                      refine ⟨2703064861398409026990391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14416345927458181477282085 2703064861398409026990391)
                      ·
                        rfl

theorem cell23_5264200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_5264200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264200 prefixEnd_5264200 := by exact prefixLift 5264200
  have htrace : WordTrace (prefixWord ++ tailWord_5264200) baseStart_5264200 baseEnd_5264200 := by
    simpa [prefixWord, tailWord_5264200, baseEnd_5264200] using wordTrace_append hprefix tailTrace_5264200
  have hstable : (prefixWord ++ tailWord_5264200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264200).length < 2 ^ (prefixWord ++ tailWord_5264200).sum := by decide
  have hdescent : baseEnd_5264200 < baseStart_5264200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264210 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_5264210 : Nat := 118140960795 + 5264210 * 2 ^ 59
def prefixEnd_5264210 : Nat := 4983230072969 + 3 ^ 40 * 5264210 * 2
def baseEnd_5264210 : Nat := 901023332068317995955115

theorem tailTrace_5264210 : CollatzResearch.WordTrace tailWord_5264210 prefixEnd_5264210 901023332068317995955115 := by
  unfold tailWord_5264210
  simp only [CollatzResearch.WordTrace]
  refine ⟨48000378064668425083911521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128001008172449133557097389 48000378064668425083911521)
  ·
    refine ⟨36000283548501318812933641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48000378064668425083911521 36000283548501318812933641)
    ·
      refine ⟨27000212661375989109700231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36000283548501318812933641 27000212661375989109700231)
      ·
        refine ⟨40500318992063983664550347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27000212661375989109700231 40500318992063983664550347)
        ·
          refine ⟨60750478488095975496825521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40500318992063983664550347 60750478488095975496825521)
          ·
            refine ⟨45562858866071981622619141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60750478488095975496825521 45562858866071981622619141)
            ·
              refine ⟨8543036037388496554241089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45562858866071981622619141 8543036037388496554241089)
              ·
                refine ⟨6407277028041372415680817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8543036037388496554241089 6407277028041372415680817)
                ·
                  refine ⟨4805457771031029311760613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6407277028041372415680817 4805457771031029311760613)
                  ·
                    refine ⟨901023332068317995955115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4805457771031029311760613 901023332068317995955115)
                    ·
                      rfl

theorem cell23_5264210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_5264210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264210 prefixEnd_5264210 := by exact prefixLift 5264210
  have htrace : WordTrace (prefixWord ++ tailWord_5264210) baseStart_5264210 baseEnd_5264210 := by
    simpa [prefixWord, tailWord_5264210, baseEnd_5264210] using wordTrace_append hprefix tailTrace_5264210
  have hstable : (prefixWord ++ tailWord_5264210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264210).length < 2 ^ (prefixWord ++ tailWord_5264210).sum := by decide
  have hdescent : baseEnd_5264210 < baseStart_5264210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264220 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_5264220 : Nat := 118140960795 + 5264220 * 2 ^ 59
def prefixEnd_5264220 : Nat := 4983230072969 + 3 ^ 40 * 5264220 * 2
def baseEnd_5264220 : Nat := 2703075131011498948740299

theorem tailTrace_5264220 : CollatzResearch.WordTrace tailWord_5264220 prefixEnd_5264220 2703075131011498948740299 := by
  unfold tailWord_5264220
  simp only [CollatzResearch.WordTrace]
  refine ⟨96000938494318736021755057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128001251325758314695673409 96000938494318736021755057)
  ·
    refine ⟨72000703870739052016316293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96000938494318736021755057 72000703870739052016316293)
    ·
      refine ⟨13500131975763572253059305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72000703870739052016316293 13500131975763572253059305)
      ·
        refine ⟨10125098981822679189794479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13500131975763572253059305 10125098981822679189794479)
        ·
          refine ⟨15187648472734018784691719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10125098981822679189794479 15187648472734018784691719)
          ·
            refine ⟨22781472709101028177037579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15187648472734018784691719 22781472709101028177037579)
            ·
              refine ⟨34172209063651542265556369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22781472709101028177037579 34172209063651542265556369)
              ·
                refine ⟨25629156797738656699167277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34172209063651542265556369 25629156797738656699167277)
                ·
                  refine ⟨9610933799151996262187729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25629156797738656699167277 9610933799151996262187729)
                  ·
                    refine ⟨7208200349363997196640797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9610933799151996262187729 7208200349363997196640797)
                    ·
                      refine ⟨2703075131011498948740299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208200349363997196640797 2703075131011498948740299)
                      ·
                        rfl

theorem cell23_5264220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_5264220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264220 prefixEnd_5264220 := by exact prefixLift 5264220
  have htrace : WordTrace (prefixWord ++ tailWord_5264220) baseStart_5264220 baseEnd_5264220 := by
    simpa [prefixWord, tailWord_5264220, baseEnd_5264220] using wordTrace_append hprefix tailTrace_5264220
  have hstable : (prefixWord ++ tailWord_5264220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264220).length < 2 ^ (prefixWord ++ tailWord_5264220).sum := by decide
  have hdescent : baseEnd_5264220 < baseStart_5264220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264233 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 3]
def baseStart_5264233 : Nat := 118140960795 + 5264233 * 2 ^ 59
def prefixEnd_5264233 : Nat := 4983230072969 + 3 ^ 40 * 5264233 * 2
def baseEnd_5264233 : Nat := 2703081806260007397877739

theorem tailTrace_5264233 : CollatzResearch.WordTrace tailWord_5264233 prefixEnd_5264233 2703081806260007397877739 := by
  unfold tailWord_5264233
  simp only [CollatzResearch.WordTrace]
  refine ⟨192002351137590375263733353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128001567425060250175822235 192002351137590375263733353)
  ·
    refine ⟨144001763353192781447800015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192002351137590375263733353 144001763353192781447800015)
    ·
      refine ⟨216002645029789172171700023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144001763353192781447800015 216002645029789172171700023)
      ·
        refine ⟨324003967544683758257550035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216002645029789172171700023 324003967544683758257550035)
        ·
          refine ⟨486005951317025637386325053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324003967544683758257550035 486005951317025637386325053)
          ·
            refine ⟨182252231743884614019871895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 486005951317025637386325053 182252231743884614019871895)
            ·
              refine ⟨273378347615826921029807843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182252231743884614019871895 273378347615826921029807843)
              ·
                refine ⟨410067521423740381544711765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273378347615826921029807843 410067521423740381544711765)
                ·
                  refine ⟨4805478766684457596227091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 410067521423740381544711765 4805478766684457596227091)
                  ·
                    refine ⟨7208218150026686394340637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4805478766684457596227091 7208218150026686394340637)
                    ·
                      refine ⟨2703081806260007397877739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208218150026686394340637 2703081806260007397877739)
                      ·
                        rfl

theorem cell23_5264233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 3].length) (baseStart_5264233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264233 prefixEnd_5264233 := by exact prefixLift 5264233
  have htrace : WordTrace (prefixWord ++ tailWord_5264233) baseStart_5264233 baseEnd_5264233 := by
    simpa [prefixWord, tailWord_5264233, baseEnd_5264233] using wordTrace_append hprefix tailTrace_5264233
  have hstable : (prefixWord ++ tailWord_5264233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264233).length < 2 ^ (prefixWord ++ tailWord_5264233).sum := by decide
  have hdescent : baseEnd_5264233 < baseStart_5264233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264236 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_5264236 : Nat := 118140960795 + 5264236 * 2 ^ 59
def prefixEnd_5264236 : Nat := 4983230072969 + 3 ^ 40 * 5264236 * 2
def baseEnd_5264236 : Nat := 901027782233990295380075

theorem tailTrace_5264236 : CollatzResearch.WordTrace tailWord_5264236 prefixEnd_5264236 901027782233990295380075 := by
  unfold tailWord_5264236
  simp only [CollatzResearch.WordTrace]
  refine ⟨96001230278289753388046281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128001640371053004517395041 96001230278289753388046281)
  ·
    refine ⟨72000922708717315041034711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96001230278289753388046281 72000922708717315041034711)
    ·
      refine ⟨108001384063075972561552067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72000922708717315041034711 108001384063075972561552067)
      ·
        refine ⟨162002076094613958842328101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108001384063075972561552067 162002076094613958842328101)
        ·
          refine ⟨30375389267740117282936519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162002076094613958842328101 30375389267740117282936519)
          ·
            refine ⟨45563083901610175924404779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30375389267740117282936519 45563083901610175924404779)
            ·
              refine ⟨68344625852415263886607169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45563083901610175924404779 68344625852415263886607169)
              ·
                refine ⟨51258469389311447914955377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68344625852415263886607169 51258469389311447914955377)
                ·
                  refine ⟨38443852041983585936216533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51258469389311447914955377 38443852041983585936216533)
                  ·
                    refine ⟨901027782233990295380075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38443852041983585936216533 901027782233990295380075)
                    ·
                      rfl

theorem cell23_5264236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_5264236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264236 prefixEnd_5264236 := by exact prefixLift 5264236
  have htrace : WordTrace (prefixWord ++ tailWord_5264236) baseStart_5264236 baseEnd_5264236 := by
    simpa [prefixWord, tailWord_5264236, baseEnd_5264236] using wordTrace_append hprefix tailTrace_5264236
  have hstable : (prefixWord ++ tailWord_5264236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264236).length < 2 ^ (prefixWord ++ tailWord_5264236).sum := by decide
  have hdescent : baseEnd_5264236 < baseStart_5264236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264254 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5264254 : Nat := 118140960795 + 5264254 * 2 ^ 59
def prefixEnd_5264254 : Nat := 4983230072969 + 3 ^ 40 * 5264254 * 2
def baseEnd_5264254 : Nat := 2703092589353751815715143

theorem tailTrace_5264254 : CollatzResearch.WordTrace tailWord_5264254 prefixEnd_5264254 2703092589353751815715143 := by
  unfold tailWord_5264254
  simp only [CollatzResearch.WordTrace]
  refine ⟨24000389633814286981280977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128002078047009530566831877 24000389633814286981280977)
  ·
    refine ⟨18000292225360715235960733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24000389633814286981280977 18000292225360715235960733)
    ·
      refine ⟨6750109584510268213485275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18000292225360715235960733 6750109584510268213485275)
      ·
        refine ⟨10125164376765402320227913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6750109584510268213485275 10125164376765402320227913)
        ·
          refine ⟨7593873282574051740170935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10125164376765402320227913 7593873282574051740170935)
          ·
            refine ⟨11390809923861077610256403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7593873282574051740170935 11390809923861077610256403)
            ·
              refine ⟨17086214885791616415384605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11390809923861077610256403 17086214885791616415384605)
              ·
                refine ⟨6407330582171856155769227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17086214885791616415384605 6407330582171856155769227)
                ·
                  refine ⟨9610995873257784233653841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6407330582171856155769227 9610995873257784233653841)
                  ·
                    refine ⟨7208246904943338175240381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9610995873257784233653841 7208246904943338175240381)
                    ·
                      refine ⟨2703092589353751815715143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208246904943338175240381 2703092589353751815715143)
                      ·
                        rfl

theorem cell23_5264254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5264254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264254 prefixEnd_5264254 := by exact prefixLift 5264254
  have htrace : WordTrace (prefixWord ++ tailWord_5264254) baseStart_5264254 baseEnd_5264254 := by
    simpa [prefixWord, tailWord_5264254, baseEnd_5264254] using wordTrace_append hprefix tailTrace_5264254
  have hstable : (prefixWord ++ tailWord_5264254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264254).length < 2 ^ (prefixWord ++ tailWord_5264254).sum := by decide
  have hdescent : baseEnd_5264254 < baseStart_5264254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264256 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_5264256 : Nat := 118140960795 + 5264256 * 2 ^ 59
def prefixEnd_5264256 : Nat := 4983230072969 + 3 ^ 40 * 5264256 * 2
def baseEnd_5264256 : Nat := 2703093616315060807890133

theorem tailTrace_5264256 : CollatzResearch.WordTrace tailWord_5264256 prefixEnd_5264256 2703093616315060807890133 := by
  unfold tailWord_5264256
  simp only [CollatzResearch.WordTrace]
  refine ⟨96001595008253525095910311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128002126677671366794547081 96001595008253525095910311)
  ·
    refine ⟨144002392512380287643865467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96001595008253525095910311 144002392512380287643865467)
    ·
      refine ⟨216003588768570431465798201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144002392512380287643865467 216003588768570431465798201)
      ·
        refine ⟨162002691576427823599348651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216003588768570431465798201 162002691576427823599348651)
        ·
          refine ⟨243004037364641735399022977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162002691576427823599348651 243004037364641735399022977)
          ·
            refine ⟨182253028023481301549267233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243004037364641735399022977 182253028023481301549267233)
            ·
              refine ⟨136689771017610976161950425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182253028023481301549267233 136689771017610976161950425)
              ·
                refine ⟨102517328263208232121462819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136689771017610976161950425 102517328263208232121462819)
                ·
                  refine ⟨153775992394812348182194229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102517328263208232121462819 153775992394812348182194229)
                  ·
                    refine ⟨14416499287013657642080709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153775992394812348182194229 14416499287013657642080709)
                    ·
                      refine ⟨2703093616315060807890133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14416499287013657642080709 2703093616315060807890133)
                      ·
                        rfl

theorem cell23_5264256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_5264256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264256 prefixEnd_5264256 := by exact prefixLift 5264256
  have htrace : WordTrace (prefixWord ++ tailWord_5264256) baseStart_5264256 baseEnd_5264256 := by
    simpa [prefixWord, tailWord_5264256, baseEnd_5264256] using wordTrace_append hprefix tailTrace_5264256
  have hstable : (prefixWord ++ tailWord_5264256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264256).length < 2 ^ (prefixWord ++ tailWord_5264256).sum := by decide
  have hdescent : baseEnd_5264256 < baseStart_5264256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264284 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5264284 : Nat := 118140960795 + 5264284 * 2 ^ 59
def prefixEnd_5264284 : Nat := 4983230072969 + 3 ^ 40 * 5264284 * 2
def baseEnd_5264284 : Nat := 2703107993773386698340005

theorem tailTrace_5264284 : CollatzResearch.WordTrace tailWord_5264284 prefixEnd_5264284 2703107993773386698340005 := by
  unfold tailWord_5264284
  simp only [CollatzResearch.WordTrace]
  refine ⟨96002105630202805486919953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128002807506937073982559937 96002105630202805486919953)
  ·
    refine ⟨72001579222652104115189965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96002105630202805486919953 72001579222652104115189965)
    ·
      refine ⟨27000592208494539043196237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72001579222652104115189965 27000592208494539043196237)
      ·
        refine ⟨10125222078185452141198589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27000592208494539043196237 10125222078185452141198589)
        ·
          refine ⟨3796958279319544552949471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10125222078185452141198589 3796958279319544552949471)
          ·
            refine ⟨5695437418979316829424207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796958279319544552949471 5695437418979316829424207)
            ·
              refine ⟨8543156128468975244136311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5695437418979316829424207 8543156128468975244136311)
              ·
                refine ⟨12814734192703462866204467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8543156128468975244136311 12814734192703462866204467)
                ·
                  refine ⟨19222101289055194299306701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12814734192703462866204467 19222101289055194299306701)
                  ·
                    refine ⟨7208287983395697862240013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19222101289055194299306701 7208287983395697862240013)
                    ·
                      refine ⟨2703107993773386698340005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208287983395697862240013 2703107993773386698340005)
                      ·
                        rfl

theorem cell23_5264284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5264284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264284 prefixEnd_5264284 := by exact prefixLift 5264284
  have htrace : WordTrace (prefixWord ++ tailWord_5264284) baseStart_5264284 baseEnd_5264284 := by
    simpa [prefixWord, tailWord_5264284, baseEnd_5264284] using wordTrace_append hprefix tailTrace_5264284
  have hstable : (prefixWord ++ tailWord_5264284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264284).length < 2 ^ (prefixWord ++ tailWord_5264284).sum := by decide
  have hdescent : baseEnd_5264284 < baseStart_5264284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264380 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_5264380 : Nat := 118140960795 + 5264380 * 2 ^ 59
def prefixEnd_5264380 : Nat := 4983230072969 + 3 ^ 40 * 5264380 * 2
def baseEnd_5264380 : Nat := 2703157287916218322739563

theorem tailTrace_5264380 : CollatzResearch.WordTrace tailWord_5264380 prefixEnd_5264380 2703157287916218322739563 := by
  unfold tailWord_5264380
  simp only [CollatzResearch.WordTrace]
  refine ⟨96003856334028909684667297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128005141778705212912889729 96003856334028909684667297)
  ·
    refine ⟨72002892250521682263500473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96003856334028909684667297 72002892250521682263500473)
    ·
      refine ⟨54002169187891261697625355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72002892250521682263500473 54002169187891261697625355)
      ·
        refine ⟨81003253781836892546438033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54002169187891261697625355 81003253781836892546438033)
        ·
          refine ⟨60752440336377669409828525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81003253781836892546438033 60752440336377669409828525)
          ·
            refine ⟨22782165126141626028685697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60752440336377669409828525 22782165126141626028685697)
            ·
              refine ⟨17086623844606219521514273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22782165126141626028685697 17086623844606219521514273)
              ·
                refine ⟨12814967883454664641135705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17086623844606219521514273 12814967883454664641135705)
                ·
                  refine ⟨9611225912590998480851779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12814967883454664641135705 9611225912590998480851779)
                  ·
                    refine ⟨14416838868886497721277669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9611225912590998480851779 14416838868886497721277669)
                    ·
                      refine ⟨2703157287916218322739563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14416838868886497721277669 2703157287916218322739563)
                      ·
                        rfl

theorem cell23_5264380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_5264380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264380 prefixEnd_5264380 := by exact prefixLift 5264380
  have htrace : WordTrace (prefixWord ++ tailWord_5264380) baseStart_5264380 baseEnd_5264380 := by
    simpa [prefixWord, tailWord_5264380, baseEnd_5264380] using wordTrace_append hprefix tailTrace_5264380
  have hstable : (prefixWord ++ tailWord_5264380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264380).length < 2 ^ (prefixWord ++ tailWord_5264380).sum := by decide
  have hdescent : baseEnd_5264380 < baseStart_5264380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264383 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 3]
def baseStart_5264383 : Nat := 118140960795 + 5264383 * 2 ^ 59
def prefixEnd_5264383 : Nat := 4983230072969 + 3 ^ 40 * 5264383 * 2
def baseEnd_5264383 : Nat := 2703158828358181811002049

theorem tailTrace_5264383 : CollatzResearch.WordTrace tailWord_5264383 prefixEnd_5264383 2703158828358181811002049 := by
  unfold tailWord_5264383
  simp only [CollatzResearch.WordTrace]
  refine ⟨192007822087046950881693803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128005214724697967254462535 192007822087046950881693803)
  ·
    refine ⟨288011733130570426322540705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192007822087046950881693803 288011733130570426322540705)
    ·
      refine ⟨216008799847927819741905529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288011733130570426322540705 216008799847927819741905529)
      ·
        refine ⟨162006599885945864806429147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216008799847927819741905529 162006599885945864806429147)
        ·
          refine ⟨243009899828918797209643721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162006599885945864806429147 243009899828918797209643721)
          ·
            refine ⟨182257424871689097907232791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243009899828918797209643721 182257424871689097907232791)
            ·
              refine ⟨273386137307533646860849187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182257424871689097907232791 273386137307533646860849187)
              ·
                refine ⟨410079205961300470291273781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273386137307533646860849187 410079205961300470291273781)
                ·
                  refine ⟨38444925558871919089806917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 410079205961300470291273781 38444925558871919089806917)
                  ·
                    refine ⟨7208423542288484829338797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38444925558871919089806917 7208423542288484829338797)
                    ·
                      refine ⟨2703158828358181811002049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208423542288484829338797 2703158828358181811002049)
                      ·
                        rfl

theorem cell23_5264383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_5264383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264383 prefixEnd_5264383 := by exact prefixLift 5264383
  have htrace : WordTrace (prefixWord ++ tailWord_5264383) baseStart_5264383 baseEnd_5264383 := by
    simpa [prefixWord, tailWord_5264383, baseEnd_5264383] using wordTrace_append hprefix tailTrace_5264383
  have hstable : (prefixWord ++ tailWord_5264383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264383).length < 2 ^ (prefixWord ++ tailWord_5264383).sum := by decide
  have hdescent : baseEnd_5264383 < baseStart_5264383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264407 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 3, 4]
def baseStart_5264407 : Nat := 118140960795 + 5264407 * 2 ^ 59
def prefixEnd_5264407 : Nat := 4983230072969 + 3 ^ 40 * 5264407 * 2
def baseEnd_5264407 : Nat := 901057050631296572367313

theorem tailTrace_5264407 : CollatzResearch.WordTrace tailWord_5264407 prefixEnd_5264407 901057050631296572367313 := by
  unfold tailWord_5264407
  simp only [CollatzResearch.WordTrace]
  refine ⟨192008697438960002980567475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128005798292640001987044983 192008697438960002980567475)
  ·
    refine ⟨288013046158440004470851213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192008697438960002980567475 288013046158440004470851213)
    ·
      refine ⟨108004892309415001676569205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288013046158440004470851213 108004892309415001676569205)
      ·
        refine ⟨10125458654007656407178363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108004892309415001676569205 10125458654007656407178363)
        ·
          refine ⟨15188187981011484610767545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10125458654007656407178363 15188187981011484610767545)
          ·
            refine ⟨11391140985758613458075659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15188187981011484610767545 11391140985758613458075659)
            ·
              refine ⟨17086711478637920187113489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11391140985758613458075659 17086711478637920187113489)
              ·
                refine ⟨12815033608978440140335117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17086711478637920187113489 12815033608978440140335117)
                ·
                  refine ⟨4805637603366915052625669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12815033608978440140335117 4805637603366915052625669)
                  ·
                    refine ⟨901057050631296572367313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4805637603366915052625669 901057050631296572367313)
                    ·
                      rfl

theorem cell23_5264407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_5264407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264407 prefixEnd_5264407 := by exact prefixLift 5264407
  have htrace : WordTrace (prefixWord ++ tailWord_5264407) baseStart_5264407 baseEnd_5264407 := by
    simpa [prefixWord, tailWord_5264407, baseEnd_5264407] using wordTrace_append hprefix tailTrace_5264407
  have hstable : (prefixWord ++ tailWord_5264407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264407).length < 2 ^ (prefixWord ++ tailWord_5264407).sum := by decide
  have hdescent : baseEnd_5264407 < baseStart_5264407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264417 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_5264417 : Nat := 118140960795 + 5264417 * 2 ^ 59
def prefixEnd_5264417 : Nat := 4983230072969 + 3 ^ 40 * 5264417 * 2
def baseEnd_5264417 : Nat := 2703176286700434677976893

theorem tailTrace_5264417 : CollatzResearch.WordTrace tailWord_5264417 prefixEnd_5264417 2703176286700434677976893 := by
  unfold tailWord_5264417
  simp only [CollatzResearch.WordTrace]
  refine ⟨192009062168923774688431505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128006041445949183125621003 192009062168923774688431505)
  ·
    refine ⟨144006796626692831016323629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192009062168923774688431505 144006796626692831016323629)
    ·
      refine ⟨54002548735009811631121361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144006796626692831016323629 54002548735009811631121361)
      ·
        refine ⟨40501911551257358723341021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54002548735009811631121361 40501911551257358723341021)
        ·
          refine ⟨15188216831721509521252883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40501911551257358723341021 15188216831721509521252883)
          ·
            refine ⟨22782325247582264281879325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15188216831721509521252883 22782325247582264281879325)
            ·
              refine ⟨8543371967843349105704747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22782325247582264281879325 8543371967843349105704747)
              ·
                refine ⟨12815057951765023658557121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8543371967843349105704747 12815057951765023658557121)
                ·
                  refine ⟨9611293463823767743917841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12815057951765023658557121 9611293463823767743917841)
                  ·
                    refine ⟨7208470097867825807938381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9611293463823767743917841 7208470097867825807938381)
                    ·
                      refine ⟨2703176286700434677976893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208470097867825807938381 2703176286700434677976893)
                      ·
                        rfl

theorem cell23_5264417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_5264417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264417 prefixEnd_5264417 := by exact prefixLift 5264417
  have htrace : WordTrace (prefixWord ++ tailWord_5264417) baseStart_5264417 baseEnd_5264417 := by
    simpa [prefixWord, tailWord_5264417, baseEnd_5264417] using wordTrace_append hprefix tailTrace_5264417
  have hstable : (prefixWord ++ tailWord_5264417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264417).length < 2 ^ (prefixWord ++ tailWord_5264417).sum := by decide
  have hdescent : baseEnd_5264417 < baseStart_5264417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264480 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 6, 4]
def baseStart_5264480 : Nat := 118140960795 + 5264480 * 2 ^ 59
def prefixEnd_5264480 : Nat := 4983230072969 + 3 ^ 40 * 5264480 * 2
def baseEnd_5264480 : Nat := 901069545327222643829701

theorem tailTrace_5264480 : CollatzResearch.WordTrace tailWord_5264480 prefixEnd_5264480 901069545327222643829701 := by
  unfold tailWord_5264480
  simp only [CollatzResearch.WordTrace]
  refine ⟨96005679983847768223987447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128007573311797024298649929 96005679983847768223987447)
  ·
    refine ⟨144008519975771652335981171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96005679983847768223987447 144008519975771652335981171)
    ·
      refine ⟨216012779963657478503971757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144008519975771652335981171 216012779963657478503971757)
      ·
        refine ⟨81004792486371554438989409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216012779963657478503971757 81004792486371554438989409)
        ·
          refine ⟨60753594364778665829242057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81004792486371554438989409 60753594364778665829242057)
          ·
            refine ⟨45565195773583999371931543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60753594364778665829242057 45565195773583999371931543)
            ·
              refine ⟨68347793660375999057897315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45565195773583999371931543 68347793660375999057897315)
              ·
                refine ⟨102521690490563998586845973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68347793660375999057897315 102521690490563998586845973)
                ·
                  refine ⟨4805704241745187433758405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102521690490563998586845973 4805704241745187433758405)
                  ·
                    refine ⟨901069545327222643829701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4805704241745187433758405 901069545327222643829701)
                    ·
                      rfl

theorem cell23_5264480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 4].length) (baseStart_5264480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264480 prefixEnd_5264480 := by exact prefixLift 5264480
  have htrace : WordTrace (prefixWord ++ tailWord_5264480) baseStart_5264480 baseEnd_5264480 := by
    simpa [prefixWord, tailWord_5264480, baseEnd_5264480] using wordTrace_append hprefix tailTrace_5264480
  have hstable : (prefixWord ++ tailWord_5264480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264480).length < 2 ^ (prefixWord ++ tailWord_5264480).sum := by decide
  have hdescent : baseEnd_5264480 < baseStart_5264480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264487 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_5264487 : Nat := 118140960795 + 5264487 * 2 ^ 59
def prefixEnd_5264487 : Nat := 4983230072969 + 3 ^ 40 * 5264487 * 2
def baseEnd_5264487 : Nat := 2703212230346249404101571

theorem tailTrace_5264487 : CollatzResearch.WordTrace tailWord_5264487 prefixEnd_5264487 2703212230346249404101571 := by
  unfold tailWord_5264487
  simp only [CollatzResearch.WordTrace]
  refine ⟨192011615278670176643479715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128007743519113451095653143 192011615278670176643479715)
  ·
    refine ⟨288017422918005264965219573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192011615278670176643479715 288017422918005264965219573)
    ·
      refine ⟨27001633398562993590489335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288017422918005264965219573 27001633398562993590489335)
      ·
        refine ⟨40502450097844490385734003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27001633398562993590489335 40502450097844490385734003)
        ·
          refine ⟨60753675146766735578601005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40502450097844490385734003 60753675146766735578601005)
          ·
            refine ⟨22782628180037525841975377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60753675146766735578601005 22782628180037525841975377)
            ·
              refine ⟨17086971135028144381481533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22782628180037525841975377 17086971135028144381481533)
              ·
                refine ⟨6407614175635554143055575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17086971135028144381481533 6407614175635554143055575)
                ·
                  refine ⟨9611421263453331214583363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6407614175635554143055575 9611421263453331214583363)
                  ·
                    refine ⟨14417131895179996821875045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9611421263453331214583363 14417131895179996821875045)
                    ·
                      refine ⟨2703212230346249404101571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14417131895179996821875045 2703212230346249404101571)
                      ·
                        rfl

theorem cell23_5264487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_5264487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264487 prefixEnd_5264487 := by exact prefixLift 5264487
  have htrace : WordTrace (prefixWord ++ tailWord_5264487) baseStart_5264487 baseEnd_5264487 := by
    simpa [prefixWord, tailWord_5264487, baseEnd_5264487] using wordTrace_append hprefix tailTrace_5264487
  have hstable : (prefixWord ++ tailWord_5264487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264487).length < 2 ^ (prefixWord ++ tailWord_5264487).sum := by decide
  have hdescent : baseEnd_5264487 < baseStart_5264487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264504 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 3, 2, 2]
def baseStart_5264504 : Nat := 118140960795 + 5264504 * 2 ^ 59
def prefixEnd_5264504 : Nat := 4983230072969 + 3 ^ 40 * 5264504 * 2
def baseEnd_5264504 : Nat := 2703220959517375837588993

theorem tailTrace_5264504 : CollatzResearch.WordTrace tailWord_5264504 prefixEnd_5264504 2703220959517375837588993 := by
  unfold tailWord_5264504
  simp only [CollatzResearch.WordTrace]
  refine ⟨96006117659804294273424283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128008156879739059031232377 96006117659804294273424283)
  ·
    refine ⟨144009176489706441410136425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96006117659804294273424283 144009176489706441410136425)
    ·
      refine ⟨108006882367279831057602319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144009176489706441410136425 108006882367279831057602319)
      ·
        refine ⟨162010323550919746586403479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108006882367279831057602319 162010323550919746586403479)
        ·
          refine ⟨243015485326379619879605219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162010323550919746586403479 243015485326379619879605219)
          ·
            refine ⟨364523227989569429819407829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243015485326379619879605219 364523227989569429819407829)
            ·
              refine ⟨8543513156005533511392371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 364523227989569429819407829 8543513156005533511392371)
              ·
                refine ⟨12815269734008300267088557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8543513156005533511392371 12815269734008300267088557)
                ·
                  refine ⟨4805726150253112600158209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12815269734008300267088557 4805726150253112600158209)
                  ·
                    refine ⟨3604294612689834450118657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4805726150253112600158209 3604294612689834450118657)
                    ·
                      refine ⟨2703220959517375837588993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604294612689834450118657 2703220959517375837588993)
                      ·
                        rfl

theorem cell23_5264504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_5264504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264504 prefixEnd_5264504 := by exact prefixLift 5264504
  have htrace : WordTrace (prefixWord ++ tailWord_5264504) baseStart_5264504 baseEnd_5264504 := by
    simpa [prefixWord, tailWord_5264504, baseEnd_5264504] using wordTrace_append hprefix tailTrace_5264504
  have hstable : (prefixWord ++ tailWord_5264504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264504).length < 2 ^ (prefixWord ++ tailWord_5264504).sum := by decide
  have hdescent : baseEnd_5264504 < baseStart_5264504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264594 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_5264594 : Nat := 118140960795 + 5264594 * 2 ^ 59
def prefixEnd_5264594 : Nat := 4983230072969 + 3 ^ 40 * 5264594 * 2
def baseEnd_5264594 : Nat := 2703267172776280485463579

theorem tailTrace_5264594 : CollatzResearch.WordTrace tailWord_5264594 prefixEnd_5264594 2703267172776280485463579 := by
  unfold tailWord_5264594
  simp only [CollatzResearch.WordTrace]
  refine ⟨48003879472320633479406209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128010345259521689278416557 48003879472320633479406209)
  ·
    refine ⟨36002909604240475109554657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48003879472320633479406209 36002909604240475109554657)
    ·
      refine ⟨27002182203180356332165993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36002909604240475109554657 27002182203180356332165993)
      ·
        refine ⟨20251636652385267249124495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27002182203180356332165993 20251636652385267249124495)
        ·
          refine ⟨30377454978577900873686743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20251636652385267249124495 30377454978577900873686743)
          ·
            refine ⟨45566182467866851310530115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30377454978577900873686743 45566182467866851310530115)
            ·
              refine ⟨68349273701800276965795173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45566182467866851310530115 68349273701800276965795173)
              ·
                refine ⟨12815488819087551931086595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68349273701800276965795173 12815488819087551931086595)
                ·
                  refine ⟨19223233228631327896629893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12815488819087551931086595 19223233228631327896629893)
                  ·
                    refine ⟨3604356230368373980618105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19223233228631327896629893 3604356230368373980618105)
                    ·
                      refine ⟨2703267172776280485463579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604356230368373980618105 2703267172776280485463579)
                      ·
                        rfl

theorem cell23_5264594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_5264594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264594 prefixEnd_5264594 := by exact prefixLift 5264594
  have htrace : WordTrace (prefixWord ++ tailWord_5264594) baseStart_5264594 baseEnd_5264594 := by
    simpa [prefixWord, tailWord_5264594, baseEnd_5264594] using wordTrace_append hprefix tailTrace_5264594
  have hstable : (prefixWord ++ tailWord_5264594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264594).length < 2 ^ (prefixWord ++ tailWord_5264594).sum := by decide
  have hdescent : baseEnd_5264594 < baseStart_5264594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264605 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_5264605 : Nat := 118140960795 + 5264605 * 2 ^ 59
def prefixEnd_5264605 : Nat := 4983230072969 + 3 ^ 40 * 5264605 * 2
def baseEnd_5264605 : Nat := 2703272821063479942426029

theorem tailTrace_5264605 : CollatzResearch.WordTrace tailWord_5264605 prefixEnd_5264605 2703272821063479942426029 := by
  unfold tailWord_5264605
  simp only [CollatzResearch.WordTrace]
  refine ⟨192015919092242682796275269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128010612728161788530850179 192015919092242682796275269)
  ·
    refine ⟨36002984829795503024301613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192015919092242682796275269 36002984829795503024301613)
    ·
      refine ⟨13501119311173313634113105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36002984829795503024301613 13501119311173313634113105)
      ·
        refine ⟨10125839483379985225584829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13501119311173313634113105 10125839483379985225584829)
        ·
          refine ⟨3797189806267494459594311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10125839483379985225584829 3797189806267494459594311)
          ·
            refine ⟨5695784709401241689391467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797189806267494459594311 5695784709401241689391467)
            ·
              refine ⟨8543677064101862534087201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5695784709401241689391467 8543677064101862534087201)
              ·
                refine ⟨6407757798076396900565401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8543677064101862534087201 6407757798076396900565401)
                ·
                  refine ⟨4805818348557297675424051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6407757798076396900565401 4805818348557297675424051)
                  ·
                    refine ⟨7208727522835946513136077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4805818348557297675424051 7208727522835946513136077)
                    ·
                      refine ⟨2703272821063479942426029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208727522835946513136077 2703272821063479942426029)
                      ·
                        rfl

theorem cell23_5264605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_5264605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264605 prefixEnd_5264605 := by exact prefixLift 5264605
  have htrace : WordTrace (prefixWord ++ tailWord_5264605) baseStart_5264605 baseEnd_5264605 := by
    simpa [prefixWord, tailWord_5264605, baseEnd_5264605] using wordTrace_append hprefix tailTrace_5264605
  have hstable : (prefixWord ++ tailWord_5264605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264605).length < 2 ^ (prefixWord ++ tailWord_5264605).sum := by decide
  have hdescent : baseEnd_5264605 < baseStart_5264605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264627 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 3]
def baseStart_5264627 : Nat := 118140960795 + 5264627 * 2 ^ 59
def prefixEnd_5264627 : Nat := 4983230072969 + 3 ^ 40 * 5264627 * 2
def baseEnd_5264627 : Nat := 2703284117637878856350927

theorem tailTrace_5264627 : CollatzResearch.WordTrace tailWord_5264627 prefixEnd_5264627 2703284117637878856350927 := by
  unfold tailWord_5264627
  simp only [CollatzResearch.WordTrace]
  refine ⟨192016721498162980553576135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128011147665441987035717423 192016721498162980553576135)
  ·
    refine ⟨288025082247244470830364203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192016721498162980553576135 288025082247244470830364203)
    ·
      refine ⟨432037623370866706245546305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288025082247244470830364203 432037623370866706245546305)
      ·
        refine ⟨324028217528150029684159729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432037623370866706245546305 324028217528150029684159729)
        ·
          refine ⟨243021163146112522263119797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324028217528150029684159729 243021163146112522263119797)
          ·
            refine ⟨22783234044948048962167481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 243021163146112522263119797 22783234044948048962167481)
            ·
              refine ⟨17087425533711036721625611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22783234044948048962167481 17087425533711036721625611)
              ·
                refine ⟨25631138300566555082438417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17087425533711036721625611 25631138300566555082438417)
                ·
                  refine ⟨19223353725424916311828813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25631138300566555082438417 19223353725424916311828813)
                  ·
                    refine ⟨7208757647034343616935805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19223353725424916311828813 7208757647034343616935805)
                    ·
                      refine ⟨2703284117637878856350927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208757647034343616935805 2703284117637878856350927)
                      ·
                        rfl

theorem cell23_5264627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_5264627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264627 prefixEnd_5264627 := by exact prefixLift 5264627
  have htrace : WordTrace (prefixWord ++ tailWord_5264627) baseStart_5264627 baseEnd_5264627 := by
    simpa [prefixWord, tailWord_5264627, baseEnd_5264627] using wordTrace_append hprefix tailTrace_5264627
  have hstable : (prefixWord ++ tailWord_5264627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264627).length < 2 ^ (prefixWord ++ tailWord_5264627).sum := by decide
  have hdescent : baseEnd_5264627 < baseStart_5264627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264640 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_5264640 : Nat := 118140960795 + 5264640 * 2 ^ 59
def prefixEnd_5264640 : Nat := 4983230072969 + 3 ^ 40 * 5264640 * 2
def baseEnd_5264640 : Nat := 2703290792886387305488367

theorem tailTrace_5264640 : CollatzResearch.WordTrace tailWord_5264640 prefixEnd_5264640 2703290792886387305488367 := by
  unfold tailWord_5264640
  simp only [CollatzResearch.WordTrace]
  refine ⟨96008597823557941886899687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128011463764743922515866249 96008597823557941886899687)
  ·
    refine ⟨144012896735336912830349531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96008597823557941886899687 144012896735336912830349531)
    ·
      refine ⟨216019345103005369245524297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144012896735336912830349531 216019345103005369245524297)
      ·
        refine ⟨162014508827254026934143223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216019345103005369245524297 162014508827254026934143223)
        ·
          refine ⟨243021763240881040401214835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162014508827254026934143223 243021763240881040401214835)
          ·
            refine ⟨364532644861321560601822253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243021763240881040401214835 364532644861321560601822253)
            ·
              refine ⟨136699741822995585225683345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364532644861321560601822253 136699741822995585225683345)
              ·
                refine ⟨102524806367246688919262509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136699741822995585225683345 102524806367246688919262509)
                ·
                  refine ⟨38446802387717508344723441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102524806367246688919262509 38446802387717508344723441)
                  ·
                    refine ⟨28835101790788131258542581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38446802387717508344723441 28835101790788131258542581)
                    ·
                      refine ⟨2703290792886387305488367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28835101790788131258542581 2703290792886387305488367)
                      ·
                        rfl

theorem cell23_5264640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_5264640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264640 prefixEnd_5264640 := by exact prefixLift 5264640
  have htrace : WordTrace (prefixWord ++ tailWord_5264640) baseStart_5264640 baseEnd_5264640 := by
    simpa [prefixWord, tailWord_5264640, baseEnd_5264640] using wordTrace_append hprefix tailTrace_5264640
  have hstable : (prefixWord ++ tailWord_5264640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264640).length < 2 ^ (prefixWord ++ tailWord_5264640).sum := by decide
  have hdescent : baseEnd_5264640 < baseStart_5264640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264674 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_5264674 : Nat := 118140960795 + 5264674 * 2 ^ 59
def prefixEnd_5264674 : Nat := 4983230072969 + 3 ^ 40 * 5264674 * 2
def baseEnd_5264674 : Nat := 2703308251228640172463211

theorem tailTrace_5264674 : CollatzResearch.WordTrace tailWord_5264674 prefixEnd_5264674 2703308251228640172463211 := by
  unfold tailWord_5264674
  simp only [CollatzResearch.WordTrace]
  refine ⟨48004608932248176895134269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128012290485995138387024717 48004608932248176895134269)
  ·
    refine ⟨18001728349593066335675351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48004608932248176895134269 18001728349593066335675351)
    ·
      refine ⟨27002592524389599503513027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18001728349593066335675351 27002592524389599503513027)
      ·
        refine ⟨40503888786584399255269541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27002592524389599503513027 40503888786584399255269541)
        ·
          refine ⟨7594479147484574860363039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40503888786584399255269541 7594479147484574860363039)
          ·
            refine ⟨11391718721226862290544559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7594479147484574860363039 11391718721226862290544559)
            ·
              refine ⟨17087578081840293435816839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11391718721226862290544559 17087578081840293435816839)
              ·
                refine ⟨25631367122760440153725259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17087578081840293435816839 25631367122760440153725259)
                ·
                  refine ⟨38447050684140660230587889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25631367122760440153725259 38447050684140660230587889)
                  ·
                    refine ⟨28835288013105495172940917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38447050684140660230587889 28835288013105495172940917)
                    ·
                      refine ⟨2703308251228640172463211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28835288013105495172940917 2703308251228640172463211)
                      ·
                        rfl

theorem cell23_5264674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_5264674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264674 prefixEnd_5264674 := by exact prefixLift 5264674
  have htrace : WordTrace (prefixWord ++ tailWord_5264674) baseStart_5264674 baseEnd_5264674 := by
    simpa [prefixWord, tailWord_5264674, baseEnd_5264674] using wordTrace_append hprefix tailTrace_5264674
  have hstable : (prefixWord ++ tailWord_5264674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264674).length < 2 ^ (prefixWord ++ tailWord_5264674).sum := by decide
  have hdescent : baseEnd_5264674 < baseStart_5264674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264687 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 3]
def baseStart_5264687 : Nat := 118140960795 + 5264687 * 2 ^ 59
def prefixEnd_5264687 : Nat := 4983230072969 + 3 ^ 40 * 5264687 * 2
def baseEnd_5264687 : Nat := 2703314926477148621600651

theorem tailTrace_5264687 : CollatzResearch.WordTrace tailWord_5264687 prefixEnd_5264687 2703314926477148621600651 := by
  unfold tailWord_5264687
  simp only [CollatzResearch.WordTrace]
  refine ⟨192018909877945610800760315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128012606585297073867173543 192018909877945610800760315)
  ·
    refine ⟨288028364816918416201140473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192018909877945610800760315 288028364816918416201140473)
    ·
      refine ⟨216021273612688812150855355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288028364816918416201140473 216021273612688812150855355)
      ·
        refine ⟨324031910419033218226283033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216021273612688812150855355 324031910419033218226283033)
        ·
          refine ⟨243023932814274913669712275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324031910419033218226283033 243023932814274913669712275)
          ·
            refine ⟨364535899221412370504568413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243023932814274913669712275 364535899221412370504568413)
            ·
              refine ⟨136700962208029638939213155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364535899221412370504568413 136700962208029638939213155)
              ·
                refine ⟨205051443312044458408819733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136700962208029638939213155 205051443312044458408819733)
                ·
                  refine ⟨9611786405252083987913425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205051443312044458408819733 9611786405252083987913425)
                  ·
                    refine ⟨7208839803939062990935069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9611786405252083987913425 7208839803939062990935069)
                    ·
                      refine ⟨2703314926477148621600651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208839803939062990935069 2703314926477148621600651)
                      ·
                        rfl

theorem cell23_5264687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_5264687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264687 prefixEnd_5264687 := by exact prefixLift 5264687
  have htrace : WordTrace (prefixWord ++ tailWord_5264687) baseStart_5264687 baseEnd_5264687 := by
    simpa [prefixWord, tailWord_5264687, baseEnd_5264687] using wordTrace_append hprefix tailTrace_5264687
  have hstable : (prefixWord ++ tailWord_5264687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264687).length < 2 ^ (prefixWord ++ tailWord_5264687).sum := by decide
  have hdescent : baseEnd_5264687 < baseStart_5264687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264704 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 3]
def baseStart_5264704 : Nat := 118140960795 + 5264704 * 2 ^ 59
def prefixEnd_5264704 : Nat := 4983230072969 + 3 ^ 40 * 5264704 * 2
def baseEnd_5264704 : Nat := 2703323655648275055088073

theorem tailTrace_5264704 : CollatzResearch.WordTrace tailWord_5264704 prefixEnd_5264704 2703323655648275055088073 := by
  unfold tailWord_5264704
  simp only [CollatzResearch.WordTrace]
  refine ⟨96009764959442011352064583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128013019945922681802752777 96009764959442011352064583)
  ·
    refine ⟨144014647439163017028096875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96009764959442011352064583 144014647439163017028096875)
    ·
      refine ⟨216021971158744525542145313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144014647439163017028096875 216021971158744525542145313)
      ·
        refine ⟨162016478369058394156608985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216021971158744525542145313 162016478369058394156608985)
        ·
          refine ⟨121512358776793795617456739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162016478369058394156608985 121512358776793795617456739)
          ·
            refine ⟨182268538165190693426185109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121512358776793795617456739 182268538165190693426185109)
            ·
              refine ⟨8543837726493313754352427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182268538165190693426185109 8543837726493313754352427)
              ·
                refine ⟨12815756589739970631528641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8543837726493313754352427 12815756589739970631528641)
                ·
                  refine ⟨9611817442304977973646481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12815756589739970631528641 9611817442304977973646481)
                  ·
                    refine ⟨7208863081728733480234861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9611817442304977973646481 7208863081728733480234861)
                    ·
                      refine ⟨2703323655648275055088073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7208863081728733480234861 2703323655648275055088073)
                      ·
                        rfl

theorem cell23_5264704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_5264704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264704 prefixEnd_5264704 := by exact prefixLift 5264704
  have htrace : WordTrace (prefixWord ++ tailWord_5264704) baseStart_5264704 baseEnd_5264704 := by
    simpa [prefixWord, tailWord_5264704, baseEnd_5264704] using wordTrace_append hprefix tailTrace_5264704
  have hstable : (prefixWord ++ tailWord_5264704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264704).length < 2 ^ (prefixWord ++ tailWord_5264704).sum := by decide
  have hdescent : baseEnd_5264704 < baseStart_5264704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264724 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 6]
def baseStart_5264724 : Nat := 118140960795 + 5264724 * 2 ^ 59
def prefixEnd_5264724 : Nat := 4983230072969 + 3 ^ 40 * 5264724 * 2
def baseEnd_5264724 : Nat := 300370436140151664093109

theorem tailTrace_5264724 : CollatzResearch.WordTrace tailWord_5264724 prefixEnd_5264724 300370436140151664093109 := by
  unfold tailWord_5264724
  simp only [CollatzResearch.WordTrace]
  refine ⟨96010129689405783059928613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128013506252541044079904817 96010129689405783059928613)
  ·
    refine ⟨18001899316763584323736615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96010129689405783059928613 18001899316763584323736615)
    ·
      refine ⟨27002848975145376485604923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18001899316763584323736615 27002848975145376485604923)
      ·
        refine ⟨40504273462718064728407385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27002848975145376485604923 40504273462718064728407385)
        ·
          refine ⟨30378205097038548546305539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40504273462718064728407385 30378205097038548546305539)
          ·
            refine ⟨45567307645557822819458309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30378205097038548546305539 45567307645557822819458309)
            ·
              refine ⟨8543870183542091778648433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45567307645557822819458309 8543870183542091778648433)
              ·
                refine ⟨6407902637656568833986325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8543870183542091778648433 6407902637656568833986325)
                ·
                  refine ⟨300370436140151664093109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6407902637656568833986325 300370436140151664093109)
                  ·
                    rfl

theorem cell23_5264724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_5264724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264724 prefixEnd_5264724 := by exact prefixLift 5264724
  have htrace : WordTrace (prefixWord ++ tailWord_5264724) baseStart_5264724 baseEnd_5264724 := by
    simpa [prefixWord, tailWord_5264724, baseEnd_5264724] using wordTrace_append hprefix tailTrace_5264724
  have hstable : (prefixWord ++ tailWord_5264724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264724).length < 2 ^ (prefixWord ++ tailWord_5264724).sum := by decide
  have hdescent : baseEnd_5264724 < baseStart_5264724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264754 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_5264754 : Nat := 118140960795 + 5264754 * 2 ^ 59
def prefixEnd_5264754 : Nat := 4983230072969 + 3 ^ 40 * 5264754 * 2
def baseEnd_5264754 : Nat := 901116443226999953154281

theorem tailTrace_5264754 : CollatzResearch.WordTrace tailWord_5264754 prefixEnd_5264754 901116443226999953154281 := by
  unfold tailWord_5264754
  simp only [CollatzResearch.WordTrace]
  refine ⟨48005338392175720310862329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128014235712468587495632877 48005338392175720310862329)
  ·
    refine ⟨36004003794131790233146747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48005338392175720310862329 36004003794131790233146747)
    ·
      refine ⟨54006005691197685349720121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36004003794131790233146747 54006005691197685349720121)
      ·
        refine ⟨40504504268398264012290091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54006005691197685349720121 40504504268398264012290091)
        ·
          refine ⟨60756756402597396018435137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40504504268398264012290091 60756756402597396018435137)
          ·
            refine ⟨45567567301948047013826353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60756756402597396018435137 45567567301948047013826353)
            ·
              refine ⟨34175675476461035260369765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45567567301948047013826353 34175675476461035260369765)
              ·
                refine ⟨6407939151836444111319331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34175675476461035260369765 6407939151836444111319331)
                ·
                  refine ⟨9611908727754666166978997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6407939151836444111319331 9611908727754666166978997)
                  ·
                    refine ⟨901116443226999953154281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9611908727754666166978997 901116443226999953154281)
                    ·
                      rfl

theorem cell23_5264754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_5264754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264754 prefixEnd_5264754 := by exact prefixLift 5264754
  have htrace : WordTrace (prefixWord ++ tailWord_5264754) baseStart_5264754 baseEnd_5264754 := by
    simpa [prefixWord, tailWord_5264754, baseEnd_5264754] using wordTrace_append hprefix tailTrace_5264754
  have hstable : (prefixWord ++ tailWord_5264754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264754).length < 2 ^ (prefixWord ++ tailWord_5264754).sum := by decide
  have hdescent : baseEnd_5264754 < baseStart_5264754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264761 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 2, 3, 2]
def baseStart_5264761 : Nat := 118140960795 + 5264761 * 2 ^ 59
def prefixEnd_5264761 : Nat := 4983230072969 + 3 ^ 40 * 5264761 * 2
def baseEnd_5264761 : Nat := 2703352924045581332075311

theorem tailTrace_5264761 : CollatzResearch.WordTrace tailWord_5264761 prefixEnd_5264761 2703352924045581332075311 := by
  unfold tailWord_5264761
  simp only [CollatzResearch.WordTrace]
  refine ⟨192021608879677521438954137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128014405919785014292636091 192021608879677521438954137)
  ·
    refine ⟨144016206659758141079215603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192021608879677521438954137 144016206659758141079215603)
    ·
      refine ⟨216024309989637211618823405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144016206659758141079215603 216024309989637211618823405)
      ·
        refine ⟨81009116246113954357058777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216024309989637211618823405 81009116246113954357058777)
        ·
          refine ⟨60756837184585465767794083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81009116246113954357058777 60756837184585465767794083)
          ·
            refine ⟨91135255776878198651691125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60756837184585465767794083 91135255776878198651691125)
            ·
              refine ⟨8543930229082331123596043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91135255776878198651691125 8543930229082331123596043)
              ·
                refine ⟨12815895343623496685394065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8543930229082331123596043 12815895343623496685394065)
                ·
                  refine ⟨9611921507717622514045549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12815895343623496685394065 9611921507717622514045549)
                  ·
                    refine ⟨3604470565394108442767081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9611921507717622514045549 3604470565394108442767081)
                    ·
                      refine ⟨2703352924045581332075311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604470565394108442767081 2703352924045581332075311)
                      ·
                        rfl

theorem cell23_5264761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_5264761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264761 prefixEnd_5264761 := by exact prefixLift 5264761
  have htrace : WordTrace (prefixWord ++ tailWord_5264761) baseStart_5264761 baseEnd_5264761 := by
    simpa [prefixWord, tailWord_5264761, baseEnd_5264761] using wordTrace_append hprefix tailTrace_5264761
  have hstable : (prefixWord ++ tailWord_5264761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264761).length < 2 ^ (prefixWord ++ tailWord_5264761).sum := by decide
  have hdescent : baseEnd_5264761 < baseStart_5264761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264771 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 1, 5]
def baseStart_5264771 : Nat := 118140960795 + 5264771 * 2 ^ 59
def prefixEnd_5264771 : Nat := 4983230072969 + 3 ^ 40 * 5264771 * 2
def baseEnd_5264771 : Nat := 901119352950708764316755

theorem tailTrace_5264771 : CollatzResearch.WordTrace tailWord_5264771 prefixEnd_5264771 901119352950708764316755 := by
  unfold tailWord_5264771
  simp only [CollatzResearch.WordTrace]
  refine ⟨192021973609641293146818167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128014649073094195431212111 192021973609641293146818167)
  ·
    refine ⟨288032960414461939720227251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192021973609641293146818167 288032960414461939720227251)
    ·
      refine ⟨432049440621692909580340877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288032960414461939720227251 432049440621692909580340877)
      ·
        refine ⟨162018540233134841092627829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432049440621692909580340877 162018540233134841092627829)
        ·
          refine ⟨15189238146856391352433859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162018540233134841092627829 15189238146856391352433859)
          ·
            refine ⟨22783857220284587028650789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15189238146856391352433859 22783857220284587028650789)
            ·
              refine ⟨4271973228803360067872023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22783857220284587028650789 4271973228803360067872023)
              ·
                refine ⟨6407959843205040101808035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4271973228803360067872023 6407959843205040101808035)
                ·
                  refine ⟨9611939764807560152712053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6407959843205040101808035 9611939764807560152712053)
                  ·
                    refine ⟨901119352950708764316755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9611939764807560152712053 901119352950708764316755)
                    ·
                      rfl

theorem cell23_5264771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 5].length) (baseStart_5264771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264771 prefixEnd_5264771 := by exact prefixLift 5264771
  have htrace : WordTrace (prefixWord ++ tailWord_5264771) baseStart_5264771 baseEnd_5264771 := by
    simpa [prefixWord, tailWord_5264771, baseEnd_5264771] using wordTrace_append hprefix tailTrace_5264771
  have hstable : (prefixWord ++ tailWord_5264771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264771).length < 2 ^ (prefixWord ++ tailWord_5264771).sum := by decide
  have hdescent : baseEnd_5264771 < baseStart_5264771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264794 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5264794 : Nat := 118140960795 + 5264794 * 2 ^ 59
def prefixEnd_5264794 : Nat := 4983230072969 + 3 ^ 40 * 5264794 * 2
def baseEnd_5264794 : Nat := 2703369868907179702962659

theorem tailTrace_5264794 : CollatzResearch.WordTrace tailWord_5264794 prefixEnd_5264794 2703369868907179702962659 := by
  unfold tailWord_5264794
  simp only [CollatzResearch.WordTrace]
  refine ⟨48005703122139492018726359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128015208325705312049936957 48005703122139492018726359)
  ·
    refine ⟨72008554683209238028089539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48005703122139492018726359 72008554683209238028089539)
    ·
      refine ⟨108012832024813857042134309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72008554683209238028089539 108012832024813857042134309)
      ·
        refine ⟨20252406004652598195400183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108012832024813857042134309 20252406004652598195400183)
        ·
          refine ⟨30378609006978897293100275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20252406004652598195400183 30378609006978897293100275)
          ·
            refine ⟨45567913510468345939650413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30378609006978897293100275 45567913510468345939650413)
            ·
              refine ⟨17087967566425629727368905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45567913510468345939650413 17087967566425629727368905)
              ·
                refine ⟨12815975674819222295526679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17087967566425629727368905 12815975674819222295526679)
                ·
                  refine ⟨19223963512228833443290019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12815975674819222295526679 19223963512228833443290019)
                  ·
                    refine ⟨28835945268343250164935029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19223963512228833443290019 28835945268343250164935029)
                    ·
                      refine ⟨2703369868907179702962659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28835945268343250164935029 2703369868907179702962659)
                      ·
                        rfl

theorem cell23_5264794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5264794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264794 prefixEnd_5264794 := by exact prefixLift 5264794
  have htrace : WordTrace (prefixWord ++ tailWord_5264794) baseStart_5264794 baseEnd_5264794 := by
    simpa [prefixWord, tailWord_5264794, baseEnd_5264794] using wordTrace_append hprefix tailTrace_5264794
  have hstable : (prefixWord ++ tailWord_5264794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264794).length < 2 ^ (prefixWord ++ tailWord_5264794).sum := by decide
  have hdescent : baseEnd_5264794 < baseStart_5264794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264824 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_5264824 : Nat := 118140960795 + 5264824 * 2 ^ 59
def prefixEnd_5264824 : Nat := 4983230072969 + 3 ^ 40 * 5264824 * 2
def baseEnd_5264824 : Nat := 2703385273326814585587521

theorem tailTrace_5264824 : CollatzResearch.WordTrace tailWord_5264824 prefixEnd_5264824 2703385273326814585587521 := by
  unfold tailWord_5264824
  simp only [CollatzResearch.WordTrace]
  refine ⟨96011953339224641599248763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128015937785632855465665017 96011953339224641599248763)
  ·
    refine ⟨144017930008836962398873145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96011953339224641599248763 144017930008836962398873145)
    ·
      refine ⟨108013447506627721799154859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144017930008836962398873145 108013447506627721799154859)
      ·
        refine ⟨162020171259941582698732289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108013447506627721799154859 162020171259941582698732289)
        ·
          refine ⟨121515128444956187024049217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162020171259941582698732289 121515128444956187024049217)
          ·
            refine ⟨91136346333717140268036913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121515128444956187024049217 91136346333717140268036913)
            ·
              refine ⟨68352259750287855201027685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91136346333717140268036913 68352259750287855201027685)
              ·
                refine ⟨12816048703178972850192691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68352259750287855201027685 12816048703178972850192691)
                ·
                  refine ⟨19224073054768459275289037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12816048703178972850192691 19224073054768459275289037)
                  ·
                    refine ⟨7209027395538172228233389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19224073054768459275289037 7209027395538172228233389)
                    ·
                      refine ⟨2703385273326814585587521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7209027395538172228233389 2703385273326814585587521)
                      ·
                        rfl

theorem cell23_5264824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_5264824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264824 prefixEnd_5264824 := by exact prefixLift 5264824
  have htrace : WordTrace (prefixWord ++ tailWord_5264824) baseStart_5264824 baseEnd_5264824 := by
    simpa [prefixWord, tailWord_5264824, baseEnd_5264824] using wordTrace_append hprefix tailTrace_5264824
  have hstable : (prefixWord ++ tailWord_5264824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264824).length < 2 ^ (prefixWord ++ tailWord_5264824).sum := by decide
  have hdescent : baseEnd_5264824 < baseStart_5264824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264841 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 3]
def baseStart_5264841 : Nat := 118140960795 + 5264841 * 2 ^ 59
def prefixEnd_5264841 : Nat := 4983230072969 + 3 ^ 40 * 5264841 * 2
def baseEnd_5264841 : Nat := 2703394002497941019074943

theorem tailTrace_5264841 : CollatzResearch.WordTrace tailWord_5264841 prefixEnd_5264841 2703394002497941019074943 := by
  unfold tailWord_5264841
  simp only [CollatzResearch.WordTrace]
  refine ⟨192024526719387695101866377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128016351146258463401244251 192024526719387695101866377)
  ·
    refine ⟨144018395039540771326399783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192024526719387695101866377 144018395039540771326399783)
    ·
      refine ⟨216027592559311156989599675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144018395039540771326399783 216027592559311156989599675)
      ·
        refine ⟨324041388838966735484399513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216027592559311156989599675 324041388838966735484399513)
        ·
          refine ⟨243031041629225051613299635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324041388838966735484399513 243031041629225051613299635)
          ·
            refine ⟨364546562443837577419949453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243031041629225051613299635 364546562443837577419949453)
            ·
              refine ⟨136704960916439091532481045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364546562443837577419949453 136704960916439091532481045)
              ·
                refine ⟨6408045042958082415585049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136704960916439091532481045 6408045042958082415585049)
                ·
                  refine ⟨4806033782218561811688787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6408045042958082415585049 4806033782218561811688787)
                  ·
                    refine ⟨7209050673327842717533181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4806033782218561811688787 7209050673327842717533181)
                    ·
                      refine ⟨2703394002497941019074943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7209050673327842717533181 2703394002497941019074943)
                      ·
                        rfl

theorem cell23_5264841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 3].length) (baseStart_5264841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264841 prefixEnd_5264841 := by exact prefixLift 5264841
  have htrace : WordTrace (prefixWord ++ tailWord_5264841) baseStart_5264841 baseEnd_5264841 := by
    simpa [prefixWord, tailWord_5264841, baseEnd_5264841] using wordTrace_append hprefix tailTrace_5264841
  have hstable : (prefixWord ++ tailWord_5264841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264841).length < 2 ^ (prefixWord ++ tailWord_5264841).sum := by decide
  have hdescent : baseEnd_5264841 < baseStart_5264841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264842 : List Nat := [3, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_5264842 : Nat := 118140960795 + 5264842 * 2 ^ 59
def prefixEnd_5264842 : Nat := 4983230072969 + 3 ^ 40 * 5264842 * 2
def baseEnd_5264842 : Nat := 2703394515978595515162439

theorem tailTrace_5264842 : CollatzResearch.WordTrace tailWord_5264842 prefixEnd_5264842 2703394515978595515162439 := by
  unfold tailWord_5264842
  simp only [CollatzResearch.WordTrace]
  refine ⟨48006140798096018068163195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128016375461589381515101853 48006140798096018068163195)
  ·
    refine ⟨72009211197144027102244793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48006140798096018068163195 72009211197144027102244793)
    ·
      refine ⟨54006908397858020326683595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72009211197144027102244793 54006908397858020326683595)
      ·
        refine ⟨81010362596787030490025393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54006908397858020326683595 81010362596787030490025393)
        ·
          refine ⟨60757771947590272867519045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81010362596787030490025393 60757771947590272867519045)
          ·
            refine ⟨11392082240173176162659821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60757771947590272867519045 11392082240173176162659821)
            ·
              refine ⟨4272030840064941060997433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11392082240173176162659821 4272030840064941060997433)
              ·
                refine ⟨3204023130048705795748075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4272030840064941060997433 3204023130048705795748075)
                ·
                  refine ⟨4806034695073058693622113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204023130048705795748075 4806034695073058693622113)
                  ·
                    refine ⟨3604526021304794020216585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4806034695073058693622113 3604526021304794020216585)
                    ·
                      refine ⟨2703394515978595515162439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604526021304794020216585 2703394515978595515162439)
                      ·
                        rfl

theorem cell23_5264842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_5264842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264842 prefixEnd_5264842 := by exact prefixLift 5264842
  have htrace : WordTrace (prefixWord ++ tailWord_5264842) baseStart_5264842 baseEnd_5264842 := by
    simpa [prefixWord, tailWord_5264842, baseEnd_5264842] using wordTrace_append hprefix tailTrace_5264842
  have hstable : (prefixWord ++ tailWord_5264842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264842).length < 2 ^ (prefixWord ++ tailWord_5264842).sum := by decide
  have hdescent : baseEnd_5264842 < baseStart_5264842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264852 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_5264852 : Nat := 118140960795 + 5264852 * 2 ^ 59
def prefixEnd_5264852 : Nat := 4983230072969 + 3 ^ 40 * 5264852 * 2
def baseEnd_5264852 : Nat := 901133216928380158679131

theorem tailTrace_5264852 : CollatzResearch.WordTrace tailWord_5264852 prefixEnd_5264852 901133216928380158679131 := by
  unfold tailWord_5264852
  simp only [CollatzResearch.WordTrace]
  refine ⟨96012463961173921990258405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128016618614898562653677873 96012463961173921990258405)
  ·
    refine ⟨18002336992720110373173451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96012463961173921990258405 18002336992720110373173451)
    ·
      refine ⟨27003505489080165559760177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18002336992720110373173451 27003505489080165559760177)
      ·
        refine ⟨20252629116810124169820133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27003505489080165559760177 20252629116810124169820133)
        ·
          refine ⟨3797367959401898281841275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20252629116810124169820133 3797367959401898281841275)
          ·
            refine ⟨5696051939102847422761913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797367959401898281841275 5696051939102847422761913)
            ·
              refine ⟨4272038954327135567071435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5696051939102847422761913 4272038954327135567071435)
              ·
                refine ⟨6408058431490703350607153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272038954327135567071435 6408058431490703350607153)
                ·
                  refine ⟨4806043823618027512955365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6408058431490703350607153 4806043823618027512955365)
                  ·
                    refine ⟨901133216928380158679131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806043823618027512955365 901133216928380158679131)
                    ·
                      rfl

theorem cell23_5264852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_5264852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264852 prefixEnd_5264852 := by exact prefixLift 5264852
  have htrace : WordTrace (prefixWord ++ tailWord_5264852) baseStart_5264852 baseEnd_5264852 := by
    simpa [prefixWord, tailWord_5264852, baseEnd_5264852] using wordTrace_append hprefix tailTrace_5264852
  have hstable : (prefixWord ++ tailWord_5264852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264852).length < 2 ^ (prefixWord ++ tailWord_5264852).sum := by decide
  have hdescent : baseEnd_5264852 < baseStart_5264852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264858 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_5264858 : Nat := 118140960795 + 5264858 * 2 ^ 59
def prefixEnd_5264858 : Nat := 4983230072969 + 3 ^ 40 * 5264858 * 2
def baseEnd_5264858 : Nat := 2703402731669067452562365

theorem tailTrace_5264858 : CollatzResearch.WordTrace tailWord_5264858 prefixEnd_5264858 2703402731669067452562365 := by
  unfold tailWord_5264858
  simp only [CollatzResearch.WordTrace]
  refine ⟨48006286690081526751308807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128016764506884071336823485 48006286690081526751308807)
  ·
    refine ⟨72009430035122290126963211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48006286690081526751308807 72009430035122290126963211)
    ·
      refine ⟨108014145052683435190444817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72009430035122290126963211 108014145052683435190444817)
      ·
        refine ⟨81010608789512576392833613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108014145052683435190444817 81010608789512576392833613)
        ·
          refine ⟨30378978296067216147312605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81010608789512576392833613 30378978296067216147312605)
          ·
            refine ⟨11392116861025206055242227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30378978296067216147312605 11392116861025206055242227)
            ·
              refine ⟨17088175291537809082863341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11392116861025206055242227 17088175291537809082863341)
              ·
                refine ⟨6408065734326678406073753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17088175291537809082863341 6408065734326678406073753)
                ·
                  refine ⟨4806049300745008804555315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6408065734326678406073753 4806049300745008804555315)
                  ·
                    refine ⟨7209073951117513206832973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4806049300745008804555315 7209073951117513206832973)
                    ·
                      refine ⟨2703402731669067452562365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7209073951117513206832973 2703402731669067452562365)
                      ·
                        rfl

theorem cell23_5264858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_5264858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264858 prefixEnd_5264858 := by exact prefixLift 5264858
  have htrace : WordTrace (prefixWord ++ tailWord_5264858) baseStart_5264858 baseEnd_5264858 := by
    simpa [prefixWord, tailWord_5264858, baseEnd_5264858] using wordTrace_append hprefix tailTrace_5264858
  have hstable : (prefixWord ++ tailWord_5264858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264858).length < 2 ^ (prefixWord ++ tailWord_5264858).sum := by decide
  have hdescent : baseEnd_5264858 < baseStart_5264858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264881 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 3, 4, 2]
def baseStart_5264881 : Nat := 118140960795 + 5264881 * 2 ^ 59
def prefixEnd_5264881 : Nat := 4983230072969 + 3 ^ 40 * 5264881 * 2
def baseEnd_5264881 : Nat := 2703414541724120862574759

theorem tailTrace_5264881 : CollatzResearch.WordTrace tailWord_5264881 prefixEnd_5264881 2703414541724120862574759 := by
  unfold tailWord_5264881
  simp only [CollatzResearch.WordTrace]
  refine ⟨192025985639242781933322497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128017323759495187955548331 192025985639242781933322497)
  ·
    refine ⟨144019489229432086449991873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192025985639242781933322497 144019489229432086449991873)
    ·
      refine ⟨108014616922074064837493905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144019489229432086449991873 108014616922074064837493905)
      ·
        refine ⟨81010962691555548628120429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108014616922074064837493905 81010962691555548628120429)
        ·
          refine ⟨30379111009333330735545161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81010962691555548628120429 30379111009333330735545161)
          ·
            refine ⟨22784333256999998051658871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30379111009333330735545161 22784333256999998051658871)
            ·
              refine ⟨34176499885499997077488307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22784333256999998051658871 34176499885499997077488307)
              ·
                refine ⟨51264749828249995616232461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34176499885499997077488307 51264749828249995616232461)
                ·
                  refine ⟨19224281185593748356087173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51264749828249995616232461 19224281185593748356087173)
                  ·
                    refine ⟨3604552722298827816766345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19224281185593748356087173 3604552722298827816766345)
                    ·
                      refine ⟨2703414541724120862574759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604552722298827816766345 2703414541724120862574759)
                      ·
                        rfl

theorem cell23_5264881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_5264881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264881 prefixEnd_5264881 := by exact prefixLift 5264881
  have htrace : WordTrace (prefixWord ++ tailWord_5264881) baseStart_5264881 baseEnd_5264881 := by
    simpa [prefixWord, tailWord_5264881, baseEnd_5264881] using wordTrace_append hprefix tailTrace_5264881
  have hstable : (prefixWord ++ tailWord_5264881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264881).length < 2 ^ (prefixWord ++ tailWord_5264881).sum := by decide
  have hdescent : baseEnd_5264881 < baseStart_5264881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264887 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 11]
def baseStart_5264887 : Nat := 118140960795 + 5264887 * 2 ^ 59
def prefixEnd_5264887 : Nat := 4983230072969 + 3 ^ 40 * 5264887 * 2
def baseEnd_5264887 : Nat := 300379735845338648788859

theorem tailTrace_5264887 : CollatzResearch.WordTrace tailWord_5264887 prefixEnd_5264887 300379735845338648788859 := by
  unfold tailWord_5264887
  simp only [CollatzResearch.WordTrace]
  refine ⟨192026204477221044958040915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128017469651480696638693943 192026204477221044958040915)
  ·
    refine ⟨288039306715831567437061373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192026204477221044958040915 288039306715831567437061373)
    ·
      refine ⟨108014740018436837788898015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288039306715831567437061373 108014740018436837788898015)
      ·
        refine ⟨162022110027655256683347023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108014740018436837788898015 162022110027655256683347023)
        ·
          refine ⟨243033165041482885025020535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162022110027655256683347023 243033165041482885025020535)
          ·
            refine ⟨364549747562224327537530803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243033165041482885025020535 364549747562224327537530803)
            ·
              refine ⟨546824621343336491306296205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364549747562224327537530803 546824621343336491306296205)
              ·
                refine ⟨205059233003751184239861077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 546824621343336491306296205 205059233003751184239861077)
                ·
                  refine ⟨300379735845338648788859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 205059233003751184239861077 300379735845338648788859)
                  ·
                    rfl

theorem cell23_5264887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 11].length) (baseStart_5264887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264887 prefixEnd_5264887 := by exact prefixLift 5264887
  have htrace : WordTrace (prefixWord ++ tailWord_5264887) baseStart_5264887 baseEnd_5264887 := by
    simpa [prefixWord, tailWord_5264887, baseEnd_5264887] using wordTrace_append hprefix tailTrace_5264887
  have hstable : (prefixWord ++ tailWord_5264887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264887).length < 2 ^ (prefixWord ++ tailWord_5264887).sum := by decide
  have hdescent : baseEnd_5264887 < baseStart_5264887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264938 : List Nat := [3, 1, 4, 1, 1, 1, 4, 3, 5]
def baseStart_5264938 : Nat := 118140960795 + 5264938 * 2 ^ 59
def prefixEnd_5264938 : Nat := 4983230072969 + 3 ^ 40 * 5264938 * 2
def baseEnd_5264938 : Nat := 300382645569047459951333

theorem tailTrace_5264938 : CollatzResearch.WordTrace tailWord_5264938 prefixEnd_5264938 300382645569047459951333 := by
  unfold tailWord_5264938
  simp only [CollatzResearch.WordTrace]
  refine ⟨48007016150009070167036867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128018709733357520445431645 48007016150009070167036867)
  ·
    refine ⟨72010524225013605250555301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48007016150009070167036867 72010524225013605250555301)
    ·
      refine ⟨13501973292190050984479119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72010524225013605250555301 13501973292190050984479119)
      ·
        refine ⟨20252959938285076476718679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13501973292190050984479119 20252959938285076476718679)
        ·
          refine ⟨30379439907427614715078019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20252959938285076476718679 30379439907427614715078019)
          ·
            refine ⟨45569159861141422072617029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30379439907427614715078019 45569159861141422072617029)
            ·
              refine ⟨8544217473964016638615693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45569159861141422072617029 8544217473964016638615693)
              ·
                refine ⟨3204081552736506239480885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8544217473964016638615693 3204081552736506239480885)
                ·
                  refine ⟨300382645569047459951333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3204081552736506239480885 300382645569047459951333)
                  ·
                    rfl

theorem cell23_5264938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_5264938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264938 prefixEnd_5264938 := by exact prefixLift 5264938
  have htrace : WordTrace (prefixWord ++ tailWord_5264938) baseStart_5264938 baseEnd_5264938 := by
    simpa [prefixWord, tailWord_5264938, baseEnd_5264938] using wordTrace_append hprefix tailTrace_5264938
  have hstable : (prefixWord ++ tailWord_5264938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264938).length < 2 ^ (prefixWord ++ tailWord_5264938).sum := by decide
  have hdescent : baseEnd_5264938 < baseStart_5264938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264966 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5264966 : Nat := 118140960795 + 5264966 * 2 ^ 59
def prefixEnd_5264966 : Nat := 4983230072969 + 3 ^ 40 * 5264966 * 2
def baseEnd_5264966 : Nat := 2703458187579753030011869

theorem tailTrace_5264966 : CollatzResearch.WordTrace tailWord_5264966 prefixEnd_5264966 2703458187579753030011869 := by
  unfold tailWord_5264966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000908932622963795317711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128019390562623227633444501 6000908932622963795317711)
  ·
    refine ⟨9001363398934445692976567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6000908932622963795317711 9001363398934445692976567)
    ·
      refine ⟨13502045098401668539464851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9001363398934445692976567 13502045098401668539464851)
      ·
        refine ⟨20253067647602502809197277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13502045098401668539464851 20253067647602502809197277)
        ·
          refine ⟨7594900367850938553448979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20253067647602502809197277 7594900367850938553448979)
          ·
            refine ⟨11392350551776407830173469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7594900367850938553448979 11392350551776407830173469)
            ·
              refine ⟨4272131456916152936315051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11392350551776407830173469 4272131456916152936315051)
              ·
                refine ⟨6408197185374229404472577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272131456916152936315051 6408197185374229404472577)
                ·
                  refine ⟨4806147889030672053354433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6408197185374229404472577 4806147889030672053354433)
                  ·
                    refine ⟨3604610916773004040015825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4806147889030672053354433 3604610916773004040015825)
                    ·
                      refine ⟨2703458187579753030011869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604610916773004040015825 2703458187579753030011869)
                      ·
                        rfl

theorem cell23_5264966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5264966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264966 prefixEnd_5264966 := by exact prefixLift 5264966
  have htrace : WordTrace (prefixWord ++ tailWord_5264966) baseStart_5264966 baseEnd_5264966 := by
    simpa [prefixWord, tailWord_5264966, baseEnd_5264966] using wordTrace_append hprefix tailTrace_5264966
  have hstable : (prefixWord ++ tailWord_5264966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264966).length < 2 ^ (prefixWord ++ tailWord_5264966).sum := by decide
  have hdescent : baseEnd_5264966 < baseStart_5264966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264984 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_5264984 : Nat := 118140960795 + 5264984 * 2 ^ 59
def prefixEnd_5264984 : Nat := 4983230072969 + 3 ^ 40 * 5264984 * 2
def baseEnd_5264984 : Nat := 2703467430231533959586785

theorem tailTrace_5264984 : CollatzResearch.WordTrace tailWord_5264984 prefixEnd_5264984 2703467430231533959586785 := by
  unfold tailWord_5264984
  simp only [CollatzResearch.WordTrace]
  refine ⟨96014871178934815262161003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128019828238579753682881337 96014871178934815262161003)
  ·
    refine ⟨144022306768402222893241505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96014871178934815262161003 144022306768402222893241505)
    ·
      refine ⟨108016730076301667169931129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144022306768402222893241505 108016730076301667169931129)
      ·
        refine ⟨81012547557226250377448347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108016730076301667169931129 81012547557226250377448347)
        ·
          refine ⟨121518821335839375566172521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81012547557226250377448347 121518821335839375566172521)
          ·
            refine ⟨91139116001879531674629391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121518821335839375566172521 91139116001879531674629391)
            ·
              refine ⟨136708674002819297511944087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91139116001879531674629391 136708674002819297511944087)
              ·
                refine ⟨205063011004228946267916131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136708674002819297511944087 205063011004228946267916131)
                ·
                  refine ⟨307594516506343419401874197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205063011004228946267916131 307594516506343419401874197)
                  ·
                    refine ⟨14418492961234847784462853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 307594516506343419401874197 14418492961234847784462853)
                    ·
                      refine ⟨2703467430231533959586785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14418492961234847784462853 2703467430231533959586785)
                      ·
                        rfl

theorem cell23_5264984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_5264984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264984 prefixEnd_5264984 := by exact prefixLift 5264984
  have htrace : WordTrace (prefixWord ++ tailWord_5264984) baseStart_5264984 baseEnd_5264984 := by
    simpa [prefixWord, tailWord_5264984, baseEnd_5264984] using wordTrace_append hprefix tailTrace_5264984
  have hstable : (prefixWord ++ tailWord_5264984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264984).length < 2 ^ (prefixWord ++ tailWord_5264984).sum := by decide
  have hdescent : baseEnd_5264984 < baseStart_5264984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5264989 : List Nat := [1, 4, 4, 2, 2, 1, 1, 3, 5]
def baseStart_5264989 : Nat := 118140960795 + 5264989 * 2 ^ 59
def prefixEnd_5264989 : Nat := 4983230072969 + 3 ^ 40 * 5264989 * 2
def baseEnd_5264989 : Nat := 300385555292756271113807

theorem tailTrace_5264989 : CollatzResearch.WordTrace tailWord_5264989 prefixEnd_5264989 300385555292756271113807 := by
  unfold tailWord_5264989
  simp only [CollatzResearch.WordTrace]
  refine ⟨192029924722851516378254021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128019949815234344252169347 192029924722851516378254021)
  ·
    refine ⟨36005610885534659320922629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192029924722851516378254021 36005610885534659320922629)
    ·
      refine ⟨6751052041037748622672993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36005610885534659320922629 6751052041037748622672993)
      ·
        refine ⟨5063289030778311467004745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6751052041037748622672993 5063289030778311467004745)
        ·
          refine ⟨3797466773083733600253559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5063289030778311467004745 3797466773083733600253559)
          ·
            refine ⟨5696200159625600400380339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797466773083733600253559 5696200159625600400380339)
            ·
              refine ⟨8544300239438400600570509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5696200159625600400380339 8544300239438400600570509)
              ·
                refine ⟨3204112589789400225213941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8544300239438400600570509 3204112589789400225213941)
                ·
                  refine ⟨300385555292756271113807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3204112589789400225213941 300385555292756271113807)
                  ·
                    rfl

theorem cell23_5264989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_5264989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5264989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5264989 prefixEnd_5264989 := by exact prefixLift 5264989
  have htrace : WordTrace (prefixWord ++ tailWord_5264989) baseStart_5264989 baseEnd_5264989 := by
    simpa [prefixWord, tailWord_5264989, baseEnd_5264989] using wordTrace_append hprefix tailTrace_5264989
  have hstable : (prefixWord ++ tailWord_5264989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5264989).length < 2 ^ (prefixWord ++ tailWord_5264989).sum := by decide
  have hdescent : baseEnd_5264989 < baseStart_5264989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5264989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265008 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 3]
def baseStart_5265008 : Nat := 118140960795 + 5265008 * 2 ^ 59
def prefixEnd_5265008 : Nat := 4983230072969 + 3 ^ 40 * 5265008 * 2
def baseEnd_5265008 : Nat := 2703479753767241865686675

theorem tailTrace_5265008 : CollatzResearch.WordTrace tailWord_5265008 prefixEnd_5265008 2703479753767241865686675 := by
  unfold tailWord_5265008
  simp only [CollatzResearch.WordTrace]
  refine ⟨96015308854891341311597839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128020411806521788415463785 96015308854891341311597839)
  ·
    refine ⟨144022963282337011967396759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96015308854891341311597839 144022963282337011967396759)
    ·
      refine ⟨216034444923505517951095139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144022963282337011967396759 216034444923505517951095139)
      ·
        refine ⟨324051667385258276926642709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216034444923505517951095139 324051667385258276926642709)
        ·
          refine ⟨15189921908683981730936377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 324051667385258276926642709 15189921908683981730936377)
          ·
            refine ⟨11392441431512986298202283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15189921908683981730936377 11392441431512986298202283)
            ·
              refine ⟨17088662147269479447303425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11392441431512986298202283 17088662147269479447303425)
              ·
                refine ⟨12816496610452109585477569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17088662147269479447303425 12816496610452109585477569)
                ·
                  refine ⟨9612372457839082189108177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12816496610452109585477569 9612372457839082189108177)
                  ·
                    refine ⟨7209279343379311641831133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9612372457839082189108177 7209279343379311641831133)
                    ·
                      refine ⟨2703479753767241865686675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7209279343379311641831133 2703479753767241865686675)
                      ·
                        rfl

theorem cell23_5265008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_5265008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265008 prefixEnd_5265008 := by exact prefixLift 5265008
  have htrace : WordTrace (prefixWord ++ tailWord_5265008) baseStart_5265008 baseEnd_5265008 := by
    simpa [prefixWord, tailWord_5265008, baseEnd_5265008] using wordTrace_append hprefix tailTrace_5265008
  have hstable : (prefixWord ++ tailWord_5265008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265008).length < 2 ^ (prefixWord ++ tailWord_5265008).sum := by decide
  have hdescent : baseEnd_5265008 < baseStart_5265008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265028 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 6]
def baseStart_5265028 : Nat := 118140960795 + 5265028 * 2 ^ 59
def prefixEnd_5265028 : Nat := 4983230072969 + 3 ^ 40 * 5265028 * 2
def baseEnd_5265028 : Nat := 300387780375592420826287

theorem tailTrace_5265028 : CollatzResearch.WordTrace tailWord_5265028 prefixEnd_5265028 300387780375592420826287 := by
  unfold tailWord_5265028
  simp only [CollatzResearch.WordTrace]
  refine ⟨96015673584855113019461869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128020898113140150692615825 96015673584855113019461869)
  ·
    refine ⟨36005877594320667382298201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96015673584855113019461869 36005877594320667382298201)
    ·
      refine ⟨27004408195740500536723651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36005877594320667382298201 27004408195740500536723651)
      ·
        refine ⟨40506612293610750805085477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27004408195740500536723651 40506612293610750805085477)
        ·
          refine ⟨7594989805052015775953527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40506612293610750805085477 7594989805052015775953527)
          ·
            refine ⟨11392484707578023663930291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7594989805052015775953527 11392484707578023663930291)
            ·
              refine ⟨17088727061367035495895437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11392484707578023663930291 17088727061367035495895437)
              ·
                refine ⟨6408272648012638310960789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17088727061367035495895437 6408272648012638310960789)
                ·
                  refine ⟨300387780375592420826287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6408272648012638310960789 300387780375592420826287)
                  ·
                    rfl

theorem cell23_5265028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_5265028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265028 prefixEnd_5265028 := by exact prefixLift 5265028
  have htrace : WordTrace (prefixWord ++ tailWord_5265028) baseStart_5265028 baseEnd_5265028 := by
    simpa [prefixWord, tailWord_5265028, baseEnd_5265028] using wordTrace_append hprefix tailTrace_5265028
  have hstable : (prefixWord ++ tailWord_5265028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265028).length < 2 ^ (prefixWord ++ tailWord_5265028).sum := by decide
  have hdescent : baseEnd_5265028 < baseStart_5265028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265041 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 1, 5]
def baseStart_5265041 : Nat := 118140960795 + 5265041 * 2 ^ 59
def prefixEnd_5265041 : Nat := 4983230072969 + 3 ^ 40 * 5265041 * 2
def baseEnd_5265041 : Nat := 901165566209613412191341

theorem tailTrace_5265041 : CollatzResearch.WordTrace tailWord_5265041 prefixEnd_5265041 901165566209613412191341 := by
  unfold tailWord_5265041
  simp only [CollatzResearch.WordTrace]
  refine ⟨192031821318663129259146977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128021214212442086172764651 192031821318663129259146977)
  ·
    refine ⟨144023865988997346944360233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192031821318663129259146977 144023865988997346944360233)
    ·
      refine ⟨108017899491748010208270175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144023865988997346944360233 108017899491748010208270175)
      ·
        refine ⟨162026849237622015312405263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108017899491748010208270175 162026849237622015312405263)
        ·
          refine ⟨243040273856433022968607895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162026849237622015312405263 243040273856433022968607895)
          ·
            refine ⟨364560410784649534452911843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243040273856433022968607895 364560410784649534452911843)
            ·
              refine ⟨546840616176974301679367765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364560410784649534452911843 546840616176974301679367765)
              ·
                refine ⟨6408288470823917597805091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 546840616176974301679367765 6408288470823917597805091)
                ·
                  refine ⟨9612432706235876396707637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6408288470823917597805091 9612432706235876396707637)
                  ·
                    refine ⟨901165566209613412191341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9612432706235876396707637 901165566209613412191341)
                    ·
                      rfl

theorem cell23_5265041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_5265041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265041 prefixEnd_5265041 := by exact prefixLift 5265041
  have htrace : WordTrace (prefixWord ++ tailWord_5265041) baseStart_5265041 baseEnd_5265041 := by
    simpa [prefixWord, tailWord_5265041, baseEnd_5265041] using wordTrace_append hprefix tailTrace_5265041
  have hstable : (prefixWord ++ tailWord_5265041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265041).length < 2 ^ (prefixWord ++ tailWord_5265041).sum := by decide
  have hdescent : baseEnd_5265041 < baseStart_5265041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265072 : List Nat := [2, 1, 1, 1, 2, 1, 8, 2, 1, 1, 3]
def baseStart_5265072 : Nat := 118140960795 + 5265072 * 2 ^ 59
def prefixEnd_5265072 : Nat := 4983230072969 + 3 ^ 40 * 5265072 * 2
def baseEnd_5265072 : Nat := 2703512616529129615286381

theorem tailTrace_5265072 : CollatzResearch.WordTrace tailWord_5265072 prefixEnd_5265072 2703512616529129615286381 := by
  unfold tailWord_5265072
  simp only [CollatzResearch.WordTrace]
  refine ⟨96016475990775410776762735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128021967987700547702350313 96016475990775410776762735)
  ·
    refine ⟨144024713986163116165144103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96016475990775410776762735 144024713986163116165144103)
    ·
      refine ⟨216037070979244674247716155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144024713986163116165144103 216037070979244674247716155)
      ·
        refine ⟨324055606468867011371574233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216037070979244674247716155 324055606468867011371574233)
        ·
          refine ⟨243041704851650258528680675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324055606468867011371574233 243041704851650258528680675)
          ·
            refine ⟨364562557277475387793021013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243041704851650258528680675 364562557277475387793021013)
            ·
              refine ⟨4272217468095414700699465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 364562557277475387793021013 4272217468095414700699465)
              ·
                refine ⟨3204163101071561025524599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4272217468095414700699465 3204163101071561025524599)
                ·
                  refine ⟨4806244651607341538286899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204163101071561025524599 4806244651607341538286899)
                  ·
                    refine ⟨7209366977411012307430349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4806244651607341538286899 7209366977411012307430349)
                    ·
                      refine ⟨2703512616529129615286381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7209366977411012307430349 2703512616529129615286381)
                      ·
                        rfl

theorem cell23_5265072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 1, 3].length) (baseStart_5265072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265072 prefixEnd_5265072 := by exact prefixLift 5265072
  have htrace : WordTrace (prefixWord ++ tailWord_5265072) baseStart_5265072 baseEnd_5265072 := by
    simpa [prefixWord, tailWord_5265072, baseEnd_5265072] using wordTrace_append hprefix tailTrace_5265072
  have hstable : (prefixWord ++ tailWord_5265072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265072).length < 2 ^ (prefixWord ++ tailWord_5265072).sum := by decide
  have hdescent : baseEnd_5265072 < baseStart_5265072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265081 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5265081 : Nat := 118140960795 + 5265081 * 2 ^ 59
def prefixEnd_5265081 : Nat := 4983230072969 + 3 ^ 40 * 5265081 * 2
def baseEnd_5265081 : Nat := 2703517237855020080073839

theorem tailTrace_5265081 : CollatzResearch.WordTrace tailWord_5265081 prefixEnd_5265081 2703517237855020080073839 := by
  unfold tailWord_5265081
  simp only [CollatzResearch.WordTrace]
  refine ⟨192033280238518216090603097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128022186825678810727068731 192033280238518216090603097)
  ·
    refine ⟨144024960178888662067952323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192033280238518216090603097 144024960178888662067952323)
    ·
      refine ⟨216037440268332993101928485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144024960178888662067952323 216037440268332993101928485)
      ·
        refine ⟨40507020050312436206611591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216037440268332993101928485 40507020050312436206611591)
        ·
          refine ⟨60760530075468654309917387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40507020050312436206611591 60760530075468654309917387)
          ·
            refine ⟨91140795113202981464876081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60760530075468654309917387 91140795113202981464876081)
            ·
              refine ⟨68355596334902236098657061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91140795113202981464876081 68355596334902236098657061)
              ·
                refine ⟨12816674312794169268498199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68355596334902236098657061 12816674312794169268498199)
                ·
                  refine ⟨19225011469191253902747299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12816674312794169268498199 19225011469191253902747299)
                  ·
                    refine ⟨28837517203786880854120949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19225011469191253902747299 28837517203786880854120949)
                    ·
                      refine ⟨2703517237855020080073839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28837517203786880854120949 2703517237855020080073839)
                      ·
                        rfl

theorem cell23_5265081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5265081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265081 prefixEnd_5265081 := by exact prefixLift 5265081
  have htrace : WordTrace (prefixWord ++ tailWord_5265081) baseStart_5265081 baseEnd_5265081 := by
    simpa [prefixWord, tailWord_5265081, baseEnd_5265081] using wordTrace_append hprefix tailTrace_5265081
  have hstable : (prefixWord ++ tailWord_5265081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265081).length < 2 ^ (prefixWord ++ tailWord_5265081).sum := by decide
  have hdescent : baseEnd_5265081 < baseStart_5265081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265088 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 2, 4]
def baseStart_5265088 : Nat := 118140960795 + 5265088 * 2 ^ 59
def prefixEnd_5265088 : Nat := 4983230072969 + 3 ^ 40 * 5265088 * 2
def baseEnd_5265088 : Nat := 901173610739867184228769

theorem tailTrace_5265088 : CollatzResearch.WordTrace tailWord_5265088 prefixEnd_5265088 901173610739867184228769 := by
  unfold tailWord_5265088
  simp only [CollatzResearch.WordTrace]
  refine ⟨96016767774746428143053959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128022357032995237524071945 96016767774746428143053959)
  ·
    refine ⟨144025151662119642214580939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96016767774746428143053959 144025151662119642214580939)
    ·
      refine ⟨216037727493179463321871409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144025151662119642214580939 216037727493179463321871409)
      ·
        refine ⟨162028295619884597491403557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216037727493179463321871409 162028295619884597491403557)
        ·
          refine ⟨30380305428728362029638167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162028295619884597491403557 30380305428728362029638167)
          ·
            refine ⟨45570458143092543044457251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30380305428728362029638167 45570458143092543044457251)
            ·
              refine ⟨68355687214638814566685877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45570458143092543044457251 68355687214638814566685877)
              ·
                refine ⟨6408345676372388865626801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68355687214638814566685877 6408345676372388865626801)
                ·
                  refine ⟨4806259257279291649220101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6408345676372388865626801 4806259257279291649220101)
                  ·
                    refine ⟨901173610739867184228769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806259257279291649220101 901173610739867184228769)
                    ·
                      rfl

theorem cell23_5265088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 4].length) (baseStart_5265088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265088 prefixEnd_5265088 := by exact prefixLift 5265088
  have htrace : WordTrace (prefixWord ++ tailWord_5265088) baseStart_5265088 baseEnd_5265088 := by
    simpa [prefixWord, tailWord_5265088, baseEnd_5265088] using wordTrace_append hprefix tailTrace_5265088
  have hstable : (prefixWord ++ tailWord_5265088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265088).length < 2 ^ (prefixWord ++ tailWord_5265088).sum := by decide
  have hdescent : baseEnd_5265088 < baseStart_5265088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265095 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_5265095 : Nat := 118140960795 + 5265095 * 2 ^ 59
def prefixEnd_5265095 : Nat := 4983230072969 + 3 ^ 40 * 5265095 * 2
def baseEnd_5265095 : Nat := 2703524426584183025298775

theorem tailTrace_5265095 : CollatzResearch.WordTrace tailWord_5265095 prefixEnd_5265095 2703524426584183025298775 := by
  unfold tailWord_5265095
  simp only [CollatzResearch.WordTrace]
  refine ⟨192033790860467496481612739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128022527240311664321075159 192033790860467496481612739)
  ·
    refine ⟨288050686290701244722419109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192033790860467496481612739 288050686290701244722419109)
    ·
      refine ⟨54009503679506483385453583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288050686290701244722419109 54009503679506483385453583)
      ·
        refine ⟨81014255519259725078180375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54009503679506483385453583 81014255519259725078180375)
        ·
          refine ⟨121521383278889587617270563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81014255519259725078180375 121521383278889587617270563)
          ·
            refine ⟨182282074918334381425905845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121521383278889587617270563 182282074918334381425905845)
            ·
              refine ⟨17088944523593848258678673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 182282074918334381425905845 17088944523593848258678673)
              ·
                refine ⟨12816708392695386194009005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17088944523593848258678673 12816708392695386194009005)
                ·
                  refine ⟨4806265647260769822753377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12816708392695386194009005 4806265647260769822753377)
                  ·
                    refine ⟨3604699235445577367065033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4806265647260769822753377 3604699235445577367065033)
                    ·
                      refine ⟨2703524426584183025298775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604699235445577367065033 2703524426584183025298775)
                      ·
                        rfl

theorem cell23_5265095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_5265095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265095 prefixEnd_5265095 := by exact prefixLift 5265095
  have htrace : WordTrace (prefixWord ++ tailWord_5265095) baseStart_5265095 baseEnd_5265095 := by
    simpa [prefixWord, tailWord_5265095, baseEnd_5265095] using wordTrace_append hprefix tailTrace_5265095
  have hstable : (prefixWord ++ tailWord_5265095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265095).length < 2 ^ (prefixWord ++ tailWord_5265095).sum := by decide
  have hdescent : baseEnd_5265095 < baseStart_5265095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265151 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_5265151 : Nat := 118140960795 + 5265151 * 2 ^ 59
def prefixEnd_5265151 : Nat := 4983230072969 + 3 ^ 40 * 5265151 * 2
def baseEnd_5265151 : Nat := 2703553181500834806198517

theorem tailTrace_5265151 : CollatzResearch.WordTrace tailWord_5265151 prefixEnd_5265151 2703553181500834806198517 := by
  unfold tailWord_5265151
  simp only [CollatzResearch.WordTrace]
  refine ⟨192035833348264618045651307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128023888898843078697100871 192035833348264618045651307)
  ·
    refine ⟨288053750022396927068476961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192035833348264618045651307 288053750022396927068476961)
    ·
      refine ⟨216040312516797695301357721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288053750022396927068476961 216040312516797695301357721)
      ·
        refine ⟨162030234387598271476018291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216040312516797695301357721 162030234387598271476018291)
        ·
          refine ⟨243045351581397407214027437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162030234387598271476018291 243045351581397407214027437)
          ·
            refine ⟨91142006843024027705260289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243045351581397407214027437 91142006843024027705260289)
            ·
              refine ⟨68356505132268020778945217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91142006843024027705260289 68356505132268020778945217)
              ·
                refine ⟨51267378849201015584208913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68356505132268020778945217 51267378849201015584208913)
                ·
                  refine ⟨38450534136900761688156685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51267378849201015584208913 38450534136900761688156685)
                  ·
                    refine ⟨14418950301337785633058757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38450534136900761688156685 14418950301337785633058757)
                    ·
                      refine ⟨2703553181500834806198517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14418950301337785633058757 2703553181500834806198517)
                      ·
                        rfl

theorem cell23_5265151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_5265151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265151 prefixEnd_5265151 := by exact prefixLift 5265151
  have htrace : WordTrace (prefixWord ++ tailWord_5265151) baseStart_5265151 baseEnd_5265151 := by
    simpa [prefixWord, tailWord_5265151, baseEnd_5265151] using wordTrace_append hprefix tailTrace_5265151
  have hstable : (prefixWord ++ tailWord_5265151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265151).length < 2 ^ (prefixWord ++ tailWord_5265151).sum := by decide
  have hdescent : baseEnd_5265151 < baseStart_5265151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265155 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 1, 3, 2]
def baseStart_5265155 : Nat := 118140960795 + 5265155 * 2 ^ 59
def prefixEnd_5265155 : Nat := 4983230072969 + 3 ^ 40 * 5265155 * 2
def baseEnd_5265155 : Nat := 2703555235423452790548499

theorem tailTrace_5265155 : CollatzResearch.WordTrace tailWord_5265155 prefixEnd_5265155 2703555235423452790548499 := by
  unfold tailWord_5265155
  simp only [CollatzResearch.WordTrace]
  refine ⟨192035979240250126728796919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128023986160166751152531279 192035979240250126728796919)
  ·
    refine ⟨288053968860375190093195379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192035979240250126728796919 288053968860375190093195379)
    ·
      refine ⟨432080953290562785139793069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288053968860375190093195379 432080953290562785139793069)
      ·
        refine ⟨162030357483961044427422401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432080953290562785139793069 162030357483961044427422401)
        ·
          refine ⟨121522768112970783320566801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162030357483961044427422401 121522768112970783320566801)
          ·
            refine ⟨91142076084728087490425101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121522768112970783320566801 91142076084728087490425101)
            ·
              refine ⟨34178278531773032808909413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91142076084728087490425101 34178278531773032808909413)
              ·
                refine ⟨6408427224707443651670515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34178278531773032808909413 6408427224707443651670515)
                ·
                  refine ⟨9612640837061165477505773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6408427224707443651670515 9612640837061165477505773)
                  ·
                    refine ⟨3604740313897937054064665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9612640837061165477505773 3604740313897937054064665)
                    ·
                      refine ⟨2703555235423452790548499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604740313897937054064665 2703555235423452790548499)
                      ·
                        rfl

theorem cell23_5265155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_5265155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265155 prefixEnd_5265155 := by exact prefixLift 5265155
  have htrace : WordTrace (prefixWord ++ tailWord_5265155) baseStart_5265155 baseEnd_5265155 := by
    simpa [prefixWord, tailWord_5265155, baseEnd_5265155] using wordTrace_append hprefix tailTrace_5265155
  have hstable : (prefixWord ++ tailWord_5265155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265155).length < 2 ^ (prefixWord ++ tailWord_5265155).sum := by decide
  have hdescent : baseEnd_5265155 < baseStart_5265155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265206 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5265206 : Nat := 118140960795 + 5265206 * 2 ^ 59
def prefixEnd_5265206 : Nat := 4983230072969 + 3 ^ 40 * 5265206 * 2
def baseEnd_5265206 : Nat := 2703581422936832091010765

theorem tailTrace_5265206 : CollatzResearch.WordTrace tailWord_5265206 prefixEnd_5265206 2703581422936832091010765 := by
  unfold tailWord_5265206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12002364960191585152431467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128025226242043574959268981 12002364960191585152431467)
  ·
    refine ⟨18003547440287377728647201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12002364960191585152431467 18003547440287377728647201)
    ·
      refine ⟨13502660580215533296485401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18003547440287377728647201 13502660580215533296485401)
      ·
        refine ⟨10126995435161649972364051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13502660580215533296485401 10126995435161649972364051)
        ·
          refine ⟨15190493152742474958546077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10126995435161649972364051 15190493152742474958546077)
          ·
            refine ⟨5696434932278428109454779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15190493152742474958546077 5696434932278428109454779)
            ·
              refine ⟨8544652398417642164182169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5696434932278428109454779 8544652398417642164182169)
              ·
                refine ⟨6408489298813231623136627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8544652398417642164182169 6408489298813231623136627)
                ·
                  refine ⟨9612733948219847434704941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6408489298813231623136627 9612733948219847434704941)
                  ·
                    refine ⟨3604775230582442788014353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9612733948219847434704941 3604775230582442788014353)
                    ·
                      refine ⟨2703581422936832091010765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604775230582442788014353 2703581422936832091010765)
                      ·
                        rfl

theorem cell23_5265206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5265206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265206 prefixEnd_5265206 := by exact prefixLift 5265206
  have htrace : WordTrace (prefixWord ++ tailWord_5265206) baseStart_5265206 baseEnd_5265206 := by
    simpa [prefixWord, tailWord_5265206, baseEnd_5265206] using wordTrace_append hprefix tailTrace_5265206
  have hstable : (prefixWord ++ tailWord_5265206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265206).length < 2 ^ (prefixWord ++ tailWord_5265206).sum := by decide
  have hdescent : baseEnd_5265206 < baseStart_5265206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265222 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5265222 : Nat := 118140960795 + 5265222 * 2 ^ 59
def prefixEnd_5265222 : Nat := 4983230072969 + 3 ^ 40 * 5265222 * 2
def baseEnd_5265222 : Nat := 2703589638627304028410691

theorem tailTrace_5265222 : CollatzResearch.WordTrace tailWord_5265222 prefixEnd_5265222 2703589638627304028410691 := by
  unfold tailWord_5265222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001200716593981161608935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128025615287338264780990613 6001200716593981161608935)
  ·
    refine ⟨9001801074890971742413403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6001200716593981161608935 9001801074890971742413403)
    ·
      refine ⟨13502701612336457613620105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9001801074890971742413403 13502701612336457613620105)
      ·
        refine ⟨10127026209252343210215079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13502701612336457613620105 10127026209252343210215079)
        ·
          refine ⟨15190539313878514815322619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10127026209252343210215079 15190539313878514815322619)
          ·
            refine ⟨22785808970817772222983929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15190539313878514815322619 22785808970817772222983929)
            ·
              refine ⟨17089356728113329167237947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22785808970817772222983929 17089356728113329167237947)
              ·
                refine ⟨25634035092169993750856921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17089356728113329167237947 25634035092169993750856921)
                ·
                  refine ⟨19225526319127495313142691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25634035092169993750856921 19225526319127495313142691)
                  ·
                    refine ⟨28838289478691242969714037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19225526319127495313142691 28838289478691242969714037)
                    ·
                      refine ⟨2703589638627304028410691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28838289478691242969714037 2703589638627304028410691)
                      ·
                        rfl

theorem cell23_5265222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5265222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265222 prefixEnd_5265222 := by exact prefixLift 5265222
  have htrace : WordTrace (prefixWord ++ tailWord_5265222) baseStart_5265222 baseEnd_5265222 := by
    simpa [prefixWord, tailWord_5265222, baseEnd_5265222] using wordTrace_append hprefix tailTrace_5265222
  have hstable : (prefixWord ++ tailWord_5265222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265222).length < 2 ^ (prefixWord ++ tailWord_5265222).sum := by decide
  have hdescent : baseEnd_5265222 < baseStart_5265222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265248 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_5265248 : Nat := 118140960795 + 5265248 * 2 ^ 59
def prefixEnd_5265248 : Nat := 4983230072969 + 3 ^ 40 * 5265248 * 2
def baseEnd_5265248 : Nat := 2703602989124320926685571

theorem tailTrace_5265248 : CollatzResearch.WordTrace tailWord_5265248 prefixEnd_5265248 2703602989124320926685571 := by
  unfold tailWord_5265248
  simp only [CollatzResearch.WordTrace]
  refine ⟨96019685614456601805966199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128026247485942135741288265 96019685614456601805966199)
  ·
    refine ⟨144029528421684902708949299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96019685614456601805966199 144029528421684902708949299)
    ·
      refine ⟨216044292632527354063423949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144029528421684902708949299 216044292632527354063423949)
      ·
        refine ⟨81016609737197757773783981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216044292632527354063423949 81016609737197757773783981)
        ·
          refine ⟨30381228651449159165168993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81016609737197757773783981 30381228651449159165168993)
          ·
            refine ⟨22785921488586869373876745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30381228651449159165168993 22785921488586869373876745)
            ·
              refine ⟨17089441116440152030407559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22785921488586869373876745 17089441116440152030407559)
              ·
                refine ⟨25634161674660228045611339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17089441116440152030407559 25634161674660228045611339)
                ·
                  refine ⟨38451242511990342068417009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25634161674660228045611339 38451242511990342068417009)
                  ·
                    refine ⟨28838431883992756551312757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38451242511990342068417009 28838431883992756551312757)
                    ·
                      refine ⟨2703602989124320926685571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28838431883992756551312757 2703602989124320926685571)
                      ·
                        rfl

theorem cell23_5265248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_5265248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265248 prefixEnd_5265248 := by exact prefixLift 5265248
  have htrace : WordTrace (prefixWord ++ tailWord_5265248) baseStart_5265248 baseEnd_5265248 := by
    simpa [prefixWord, tailWord_5265248, baseEnd_5265248] using wordTrace_append hprefix tailTrace_5265248
  have hstable : (prefixWord ++ tailWord_5265248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265248).length < 2 ^ (prefixWord ++ tailWord_5265248).sum := by decide
  have hdescent : baseEnd_5265248 < baseStart_5265248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265352 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_5265352 : Nat := 118140960795 + 5265352 * 2 ^ 59
def prefixEnd_5265352 : Nat := 4983230072969 + 3 ^ 40 * 5265352 * 2
def baseEnd_5265352 : Nat := 2703656391112388519785093

theorem tailTrace_5265352 : CollatzResearch.WordTrace tailWord_5265352 prefixEnd_5265352 2703656391112388519785093 := by
  unfold tailWord_5265352
  simp only [CollatzResearch.WordTrace]
  refine ⟨96021582210268214686859155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128028776280357619582478873 96021582210268214686859155)
  ·
    refine ⟨144032373315402322030288733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96021582210268214686859155 144032373315402322030288733)
    ·
      refine ⟨54012139993275870761358275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144032373315402322030288733 54012139993275870761358275)
      ·
        refine ⟨81018209989913806142037413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54012139993275870761358275 81018209989913806142037413)
        ·
          refine ⟨15190914373108838651632015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81018209989913806142037413 15190914373108838651632015)
          ·
            refine ⟨22786371559663257977448023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15190914373108838651632015 22786371559663257977448023)
            ·
              refine ⟨34179557339494886966172035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22786371559663257977448023 34179557339494886966172035)
              ·
                refine ⟨51269336009242330449258053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34179557339494886966172035 51269336009242330449258053)
                ·
                  refine ⟨9613000501732936959235885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51269336009242330449258053 9613000501732936959235885)
                  ·
                    refine ⟨3604875188149851359713457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9613000501732936959235885 3604875188149851359713457)
                    ·
                      refine ⟨2703656391112388519785093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604875188149851359713457 2703656391112388519785093)
                      ·
                        rfl

theorem cell23_5265352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_5265352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265352 prefixEnd_5265352 := by exact prefixLift 5265352
  have htrace : WordTrace (prefixWord ++ tailWord_5265352) baseStart_5265352 baseEnd_5265352 := by
    simpa [prefixWord, tailWord_5265352, baseEnd_5265352] using wordTrace_append hprefix tailTrace_5265352
  have hstable : (prefixWord ++ tailWord_5265352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265352).length < 2 ^ (prefixWord ++ tailWord_5265352).sum := by decide
  have hdescent : baseEnd_5265352 < baseStart_5265352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265366 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_5265366 : Nat := 118140960795 + 5265366 * 2 ^ 59
def prefixEnd_5265366 : Nat := 4983230072969 + 3 ^ 40 * 5265366 * 2
def baseEnd_5265366 : Nat := 300407064426839051667781

theorem tailTrace_5265366 : CollatzResearch.WordTrace tailWord_5265366 prefixEnd_5265366 300407064426839051667781 := by
  unfold tailWord_5265366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12002729690155356860295497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128029116694990473176485301 12002729690155356860295497)
  ·
    refine ⟨9002047267616517645221623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12002729690155356860295497 9002047267616517645221623)
    ·
      refine ⟨13503070901424776467832435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9002047267616517645221623 13503070901424776467832435)
      ·
        refine ⟨20254606352137164701748653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13503070901424776467832435 20254606352137164701748653)
        ·
          refine ⟨7595477382051436763155745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20254606352137164701748653 7595477382051436763155745)
          ·
            refine ⟨5696608036538577572366809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7595477382051436763155745 5696608036538577572366809)
            ·
              refine ⟨4272456027403933179275107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5696608036538577572366809 4272456027403933179275107)
              ·
                refine ⟨6408684041105899768912661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272456027403933179275107 6408684041105899768912661)
                ·
                  refine ⟨300407064426839051667781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6408684041105899768912661 300407064426839051667781)
                  ·
                    rfl

theorem cell23_5265366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_5265366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265366 prefixEnd_5265366 := by exact prefixLift 5265366
  have htrace : WordTrace (prefixWord ++ tailWord_5265366) baseStart_5265366 baseEnd_5265366 := by
    simpa [prefixWord, tailWord_5265366, baseEnd_5265366] using wordTrace_append hprefix tailTrace_5265366
  have hstable : (prefixWord ++ tailWord_5265366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265366).length < 2 ^ (prefixWord ++ tailWord_5265366).sum := by decide
  have hdescent : baseEnd_5265366 < baseStart_5265366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265408 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_5265408 : Nat := 118140960795 + 5265408 * 2 ^ 59
def prefixEnd_5265408 : Nat := 4983230072969 + 3 ^ 40 * 5265408 * 2
def baseEnd_5265408 : Nat := 2703685146029040300684835

theorem tailTrace_5265408 : CollatzResearch.WordTrace tailWord_5265408 prefixEnd_5265408 2703685146029040300684835 := by
  unfold tailWord_5265408
  simp only [CollatzResearch.WordTrace]
  refine ⟨96022603454166775468878439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128030137938889033958504585 96022603454166775468878439)
  ·
    refine ⟨144033905181250163203317659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96022603454166775468878439 144033905181250163203317659)
    ·
      refine ⟨216050857771875244804976489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144033905181250163203317659 216050857771875244804976489)
      ·
        refine ⟨162038143328906433603732367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216050857771875244804976489 162038143328906433603732367)
        ·
          refine ⟨243057214993359650405598551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162038143328906433603732367 243057214993359650405598551)
          ·
            refine ⟨364585822490039475608397827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243057214993359650405598551 364585822490039475608397827)
            ·
              refine ⟨546878733735059213412596741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364585822490039475608397827 546878733735059213412596741)
              ·
                refine ⟨102539762575323602514861889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 546878733735059213412596741 102539762575323602514861889)
                ·
                  refine ⟨76904821931492701886146417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102539762575323602514861889 76904821931492701886146417)
                  ·
                    refine ⟨57678616448619526414609813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76904821931492701886146417 57678616448619526414609813)
                    ·
                      refine ⟨2703685146029040300684835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57678616448619526414609813 2703685146029040300684835)
                      ·
                        rfl

theorem cell23_5265408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_5265408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265408 prefixEnd_5265408 := by exact prefixLift 5265408
  have htrace : WordTrace (prefixWord ++ tailWord_5265408) baseStart_5265408 baseEnd_5265408 := by
    simpa [prefixWord, tailWord_5265408, baseEnd_5265408] using wordTrace_append hprefix tailTrace_5265408
  have hstable : (prefixWord ++ tailWord_5265408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265408).length < 2 ^ (prefixWord ++ tailWord_5265408).sum := by decide
  have hdescent : baseEnd_5265408 < baseStart_5265408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265416 : List Nat := [2, 1, 3, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_5265416 : Nat := 118140960795 + 5265416 * 2 ^ 59
def prefixEnd_5265416 : Nat := 4983230072969 + 3 ^ 40 * 5265416 * 2
def baseEnd_5265416 : Nat := 2703689253874276269384799

theorem tailTrace_5265416 : CollatzResearch.WordTrace tailWord_5265416 prefixEnd_5265416 2703689253874276269384799 := by
  unfold tailWord_5265416
  simp only [CollatzResearch.WordTrace]
  refine ⟨96022749346152284152024051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128030332461536378869365401 96022749346152284152024051)
  ·
    refine ⟨144034124019228426228036077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96022749346152284152024051 144034124019228426228036077)
    ·
      refine ⟨54012796507210659835513529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144034124019228426228036077 54012796507210659835513529)
      ·
        refine ⟨40509597380407994876635147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54012796507210659835513529 40509597380407994876635147)
        ·
          refine ⟨60764396070611992314952721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40509597380407994876635147 60764396070611992314952721)
          ·
            refine ⟨45573297052958994236214541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60764396070611992314952721 45573297052958994236214541)
            ·
              refine ⟨17089986394859622838580453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45573297052958994236214541 17089986394859622838580453)
              ·
                refine ⟨3204372449036179282233835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17089986394859622838580453 3204372449036179282233835)
                ·
                  refine ⟨4806558673554268923350753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204372449036179282233835 4806558673554268923350753)
                  ·
                    refine ⟨3604919005165701692513065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4806558673554268923350753 3604919005165701692513065)
                    ·
                      refine ⟨2703689253874276269384799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3604919005165701692513065 2703689253874276269384799)
                      ·
                        rfl

theorem cell23_5265416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_5265416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265416 prefixEnd_5265416 := by exact prefixLift 5265416
  have htrace : WordTrace (prefixWord ++ tailWord_5265416) baseStart_5265416 baseEnd_5265416 := by
    simpa [prefixWord, tailWord_5265416, baseEnd_5265416] using wordTrace_append hprefix tailTrace_5265416
  have hstable : (prefixWord ++ tailWord_5265416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265416).length < 2 ^ (prefixWord ++ tailWord_5265416).sum := by decide
  have hdescent : baseEnd_5265416 < baseStart_5265416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265432 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_5265432 : Nat := 118140960795 + 5265432 * 2 ^ 59
def prefixEnd_5265432 : Nat := 4983230072969 + 3 ^ 40 * 5265432 * 2
def baseEnd_5265432 : Nat := 2703697469564748206784725

theorem tailTrace_5265432 : CollatzResearch.WordTrace tailWord_5265432 prefixEnd_5265432 2703697469564748206784725 := by
  unfold tailWord_5265432
  simp only [CollatzResearch.WordTrace]
  refine ⟨96023041130123301518315275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128030721506831068691087033 96023041130123301518315275)
  ·
    refine ⟨144034561695184952277472913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96023041130123301518315275 144034561695184952277472913)
    ·
      refine ⟨108025921271388714208104685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144034561695184952277472913 108025921271388714208104685)
      ·
        refine ⟨40509720476770767828039257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108025921271388714208104685 40509720476770767828039257)
        ·
          refine ⟨30382290357578075871029443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40509720476770767828039257 30382290357578075871029443)
          ·
            refine ⟨45573435536367113806544165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30382290357578075871029443 45573435536367113806544165)
            ·
              refine ⟨8545019163068833838727031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45573435536367113806544165 8545019163068833838727031)
              ·
                refine ⟨12817528744603250758090547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8545019163068833838727031 12817528744603250758090547)
                ·
                  refine ⟨19226293116904876137135821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12817528744603250758090547 19226293116904876137135821)
                  ·
                    refine ⟨7209859918839328551425933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19226293116904876137135821 7209859918839328551425933)
                    ·
                      refine ⟨2703697469564748206784725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7209859918839328551425933 2703697469564748206784725)
                      ·
                        rfl

theorem cell23_5265432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_5265432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265432 prefixEnd_5265432 := by exact prefixLift 5265432
  have htrace : WordTrace (prefixWord ++ tailWord_5265432) baseStart_5265432 baseEnd_5265432 := by
    simpa [prefixWord, tailWord_5265432, baseEnd_5265432] using wordTrace_append hprefix tailTrace_5265432
  have hstable : (prefixWord ++ tailWord_5265432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265432).length < 2 ^ (prefixWord ++ tailWord_5265432).sum := by decide
  have hdescent : baseEnd_5265432 < baseStart_5265432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265475 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 3]
def baseStart_5265475 : Nat := 118140960795 + 5265475 * 2 ^ 59
def prefixEnd_5265475 : Nat := 4983230072969 + 3 ^ 40 * 5265475 * 2
def baseEnd_5265475 : Nat := 2703719549232891538547027

theorem tailTrace_5265475 : CollatzResearch.WordTrace tailWord_5265475 prefixEnd_5265475 2703719549232891538547027 := by
  unfold tailWord_5265475
  simp only [CollatzResearch.WordTrace]
  refine ⟨192047650599090821380445879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128031767066060547586963919 192047650599090821380445879)
  ·
    refine ⟨288071475898636232070668819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192047650599090821380445879 288071475898636232070668819)
    ·
      refine ⟨432107213847954348106003229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288071475898636232070668819 432107213847954348106003229)
      ·
        refine ⟨162040205192982880539751211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432107213847954348106003229 162040205192982880539751211)
        ·
          refine ⟨243060307789474320809626817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162040205192982880539751211 243060307789474320809626817)
          ·
            refine ⟨182295230842105740607220113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243060307789474320809626817 182295230842105740607220113)
            ·
              refine ⟨136721423131579305455415085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182295230842105740607220113 136721423131579305455415085)
              ·
                refine ⟨51270533674342239545780657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136721423131579305455415085 51270533674342239545780657)
                ·
                  refine ⟨38452900255756679659335493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51270533674342239545780657 38452900255756679659335493)
                  ·
                    refine ⟨7209918797954377436125405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38452900255756679659335493 7209918797954377436125405)
                    ·
                      refine ⟨2703719549232891538547027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7209918797954377436125405 2703719549232891538547027)
                      ·
                        rfl

theorem cell23_5265475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_5265475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265475 prefixEnd_5265475 := by exact prefixLift 5265475
  have htrace : WordTrace (prefixWord ++ tailWord_5265475) baseStart_5265475 baseEnd_5265475 := by
    simpa [prefixWord, tailWord_5265475, baseEnd_5265475] using wordTrace_append hprefix tailTrace_5265475
  have hstable : (prefixWord ++ tailWord_5265475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265475).length < 2 ^ (prefixWord ++ tailWord_5265475).sum := by decide
  have hdescent : baseEnd_5265475 < baseStart_5265475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265495 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 7]
def baseStart_5265495 : Nat := 118140960795 + 5265495 * 2 ^ 59
def prefixEnd_5265495 : Nat := 4983230072969 + 3 ^ 40 * 5265495 * 2
def baseEnd_5265495 : Nat := 300414424316220162255215

theorem tailTrace_5265495 : CollatzResearch.WordTrace tailWord_5265495 prefixEnd_5265495 300414424316220162255215 := by
  unfold tailWord_5265495
  simp only [CollatzResearch.WordTrace]
  refine ⟨192048380059018364796173939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128032253372678909864115959 192048380059018364796173939)
  ·
    refine ⟨288072570088527547194260909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192048380059018364796173939 288072570088527547194260909)
    ·
      refine ⟨108027213783197830197847841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288072570088527547194260909 108027213783197830197847841)
      ·
        refine ⟨81020410337398372648385881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108027213783197830197847841 81020410337398372648385881)
        ·
          refine ⟨60765307753048779486289411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81020410337398372648385881 60765307753048779486289411)
          ·
            refine ⟨91147961629573169229434117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60765307753048779486289411 91147961629573169229434117)
            ·
              refine ⟨17090242805544969230518897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91147961629573169229434117 17090242805544969230518897)
              ·
                refine ⟨12817682104158726922889173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17090242805544969230518897 12817682104158726922889173)
                ·
                  refine ⟨300414424316220162255215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12817682104158726922889173 300414424316220162255215)
                  ·
                    rfl

theorem cell23_5265495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 7].length) (baseStart_5265495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265495 prefixEnd_5265495 := by exact prefixLift 5265495
  have htrace : WordTrace (prefixWord ++ tailWord_5265495) baseStart_5265495 baseEnd_5265495 := by
    simpa [prefixWord, tailWord_5265495, baseEnd_5265495] using wordTrace_append hprefix tailTrace_5265495
  have hstable : (prefixWord ++ tailWord_5265495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265495).length < 2 ^ (prefixWord ++ tailWord_5265495).sum := by decide
  have hdescent : baseEnd_5265495 < baseStart_5265495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265559 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 2, 5]
def baseStart_5265559 : Nat := 118140960795 + 5265559 * 2 ^ 59
def prefixEnd_5265559 : Nat := 4983230072969 + 3 ^ 40 * 5265559 * 2
def baseEnd_5265559 : Nat := 901254227202623069965547

theorem tailTrace_5265559 : CollatzResearch.WordTrace tailWord_5265559 prefixEnd_5265559 901254227202623069965547 := by
  unfold tailWord_5265559
  simp only [CollatzResearch.WordTrace]
  refine ⟨192050714330786503726503731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128033809553857669151002487 192050714330786503726503731)
  ·
    refine ⟨288076071496179755589755597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192050714330786503726503731 288076071496179755589755597)
    ·
      refine ⟨108028526811067408346158349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288076071496179755589755597 108028526811067408346158349)
      ·
        refine ⟨40510697554150278129809381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108028526811067408346158349 40510697554150278129809381)
        ·
          refine ⟨7595755791403177149339259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40510697554150278129809381 7595755791403177149339259)
          ·
            refine ⟨11393633687104765724008889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7595755791403177149339259 11393633687104765724008889)
            ·
              refine ⟨8545225265328574293006667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11393633687104765724008889 8545225265328574293006667)
              ·
                refine ⟨12817837897992861439510001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8545225265328574293006667 12817837897992861439510001)
                ·
                  refine ⟨9613378423494646079632501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12817837897992861439510001 9613378423494646079632501)
                  ·
                    refine ⟨901254227202623069965547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9613378423494646079632501 901254227202623069965547)
                    ·
                      rfl

theorem cell23_5265559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_5265559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265559 prefixEnd_5265559 := by exact prefixLift 5265559
  have htrace : WordTrace (prefixWord ++ tailWord_5265559) baseStart_5265559 baseEnd_5265559 := by
    simpa [prefixWord, tailWord_5265559, baseEnd_5265559] using wordTrace_append hprefix tailTrace_5265559
  have hstable : (prefixWord ++ tailWord_5265559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265559).length < 2 ^ (prefixWord ++ tailWord_5265559).sum := by decide
  have hdescent : baseEnd_5265559 < baseStart_5265559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265596 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_5265596 : Nat := 118140960795 + 5265596 * 2 ^ 59
def prefixEnd_5265596 : Nat := 4983230072969 + 3 ^ 40 * 5265596 * 2
def baseEnd_5265596 : Nat := 2703781680392085565133971

theorem tailTrace_5265596 : CollatzResearch.WordTrace tailWord_5265596 prefixEnd_5265596 2703781680392085565133971 := by
  unfold tailWord_5265596
  simp only [CollatzResearch.WordTrace]
  refine ⟨96026031915826229522800321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128034709221101639363733761 96026031915826229522800321)
  ·
    refine ⟨72019523936869672142100241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96026031915826229522800321 72019523936869672142100241)
    ·
      refine ⟨54014642952652254106575181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72019523936869672142100241 54014642952652254106575181)
      ·
        refine ⟨20255491107244595289965693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54014642952652254106575181 20255491107244595289965693)
        ·
          refine ⟨7595809165216723233737135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20255491107244595289965693 7595809165216723233737135)
          ·
            refine ⟨11393713747825084850605703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7595809165216723233737135 11393713747825084850605703)
            ·
              refine ⟨17090570621737627275908555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11393713747825084850605703 17090570621737627275908555)
              ·
                refine ⟨25635855932606440913862833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17090570621737627275908555 25635855932606440913862833)
                ·
                  refine ⟨19226891949454830685397125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25635855932606440913862833 19226891949454830685397125)
                  ·
                    refine ⟨3605042240522780753511961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19226891949454830685397125 3605042240522780753511961)
                    ·
                      refine ⟨2703781680392085565133971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605042240522780753511961 2703781680392085565133971)
                      ·
                        rfl

theorem cell23_5265596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_5265596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265596 prefixEnd_5265596 := by exact prefixLift 5265596
  have htrace : WordTrace (prefixWord ++ tailWord_5265596) baseStart_5265596 baseEnd_5265596 := by
    simpa [prefixWord, tailWord_5265596, baseEnd_5265596] using wordTrace_append hprefix tailTrace_5265596
  have hstable : (prefixWord ++ tailWord_5265596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265596).length < 2 ^ (prefixWord ++ tailWord_5265596).sum := by decide
  have hdescent : baseEnd_5265596 < baseStart_5265596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265666 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_5265666 : Nat := 118140960795 + 5265666 * 2 ^ 59
def prefixEnd_5265666 : Nat := 4983230072969 + 3 ^ 40 * 5265666 * 2
def baseEnd_5265666 : Nat := 901272541345966763752883

theorem tailTrace_5265666 : CollatzResearch.WordTrace tailWord_5265666 prefixEnd_5265666 901272541345966763752883 := by
  unfold tailWord_5265666
  simp only [CollatzResearch.WordTrace]
  refine ⟨48013654235349715250162213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128036411294265907333765901 48013654235349715250162213)
  ·
    refine ⟨9002560169128071609405415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48013654235349715250162213 9002560169128071609405415)
    ·
      refine ⟨13503840253692107414108123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9002560169128071609405415 13503840253692107414108123)
      ·
        refine ⟨20255760380538161121162185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13503840253692107414108123 20255760380538161121162185)
        ·
          refine ⟨15191820285403620840871639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20255760380538161121162185 15191820285403620840871639)
          ·
            refine ⟨22787730428105431261307459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15191820285403620840871639 22787730428105431261307459)
            ·
              refine ⟨34181595642158146891961189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22787730428105431261307459 34181595642158146891961189)
              ·
                refine ⟨6409049182904652542242723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34181595642158146891961189 6409049182904652542242723)
                ·
                  refine ⟨9613573774356978813364085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409049182904652542242723 9613573774356978813364085)
                  ·
                    refine ⟨901272541345966763752883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9613573774356978813364085 901272541345966763752883)
                    ·
                      rfl

theorem cell23_5265666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_5265666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265666 prefixEnd_5265666 := by exact prefixLift 5265666
  have htrace : WordTrace (prefixWord ++ tailWord_5265666) baseStart_5265666 baseEnd_5265666 := by
    simpa [prefixWord, tailWord_5265666, baseEnd_5265666] using wordTrace_append hprefix tailTrace_5265666
  have hstable : (prefixWord ++ tailWord_5265666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265666).length < 2 ^ (prefixWord ++ tailWord_5265666).sum := by decide
  have hdescent : baseEnd_5265666 < baseStart_5265666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265776 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 1, 4, 2]
def baseStart_5265776 : Nat := 118140960795 + 5265776 * 2 ^ 59
def prefixEnd_5265776 : Nat := 4983230072969 + 3 ^ 40 * 5265776 * 2
def baseEnd_5265776 : Nat := 2703874106909894860883143

theorem tailTrace_5265776 : CollatzResearch.WordTrace tailWord_5265776 prefixEnd_5265776 2703874106909894860883143 := by
  unfold tailWord_5265776
  simp only [CollatzResearch.WordTrace]
  refine ⟨96029314485500174893576591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128039085980666899858102121 96029314485500174893576591)
  ·
    refine ⟨144043971728250262340364887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96029314485500174893576591 144043971728250262340364887)
    ·
      refine ⟨216065957592375393510547331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144043971728250262340364887 216065957592375393510547331)
      ·
        refine ⟨324098936388563090265820997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216065957592375393510547331 324098936388563090265820997)
        ·
          refine ⟨60768550572855579424841437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 324098936388563090265820997 60768550572855579424841437)
          ·
            refine ⟨22788206464820842284315539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60768550572855579424841437 22788206464820842284315539)
            ·
              refine ⟨34182309697231263426473309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22788206464820842284315539 34182309697231263426473309)
              ·
                refine ⟨12818366136461723784927491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34182309697231263426473309 12818366136461723784927491)
                ·
                  refine ⟨19227549204692585677391237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12818366136461723784927491 19227549204692585677391237)
                  ·
                    refine ⟨3605165475879859814510857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19227549204692585677391237 3605165475879859814510857)
                    ·
                      refine ⟨2703874106909894860883143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605165475879859814510857 2703874106909894860883143)
                      ·
                        rfl

theorem cell23_5265776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 4, 2].length) (baseStart_5265776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265776 prefixEnd_5265776 := by exact prefixLift 5265776
  have htrace : WordTrace (prefixWord ++ tailWord_5265776) baseStart_5265776 baseEnd_5265776 := by
    simpa [prefixWord, tailWord_5265776, baseEnd_5265776] using wordTrace_append hprefix tailTrace_5265776
  have hstable : (prefixWord ++ tailWord_5265776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265776).length < 2 ^ (prefixWord ++ tailWord_5265776).sum := by decide
  have hdescent : baseEnd_5265776 < baseStart_5265776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265792 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_5265792 : Nat := 118140960795 + 5265792 * 2 ^ 59
def prefixEnd_5265792 : Nat := 4983230072969 + 3 ^ 40 * 5265792 * 2
def baseEnd_5265792 : Nat := 2703882322600366798283069

theorem tailTrace_5265792 : CollatzResearch.WordTrace tailWord_5265792 prefixEnd_5265792 2703882322600366798283069 := by
  unfold tailWord_5265792
  simp only [CollatzResearch.WordTrace]
  refine ⟨96029606269471192259867815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128039475025961589679823753 96029606269471192259867815)
  ·
    refine ⟨144044409404206788389801723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96029606269471192259867815 144044409404206788389801723)
    ·
      refine ⟨216066614106310182584702585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144044409404206788389801723 216066614106310182584702585)
      ·
        refine ⟨162049960579732636938526939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216066614106310182584702585 162049960579732636938526939)
        ·
          refine ⟨243074940869598955407790409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162049960579732636938526939 243074940869598955407790409)
          ·
            refine ⟨182306205652199216555842807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243074940869598955407790409 182306205652199216555842807)
            ·
              refine ⟨273459308478298824833764211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182306205652199216555842807 273459308478298824833764211)
              ·
                refine ⟨410188962717448237250646317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273459308478298824833764211 410188962717448237250646317)
                ·
                  refine ⟨153820861019043088968992369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410188962717448237250646317 153820861019043088968992369)
                  ·
                    refine ⟨115365645764282316726744277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153820861019043088968992369 115365645764282316726744277)
                    ·
                      refine ⟨2703882322600366798283069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115365645764282316726744277 2703882322600366798283069)
                      ·
                        rfl

theorem cell23_5265792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_5265792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265792 prefixEnd_5265792 := by exact prefixLift 5265792
  have htrace : WordTrace (prefixWord ++ tailWord_5265792) baseStart_5265792 baseEnd_5265792 := by
    simpa [prefixWord, tailWord_5265792, baseEnd_5265792] using wordTrace_append hprefix tailTrace_5265792
  have hstable : (prefixWord ++ tailWord_5265792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265792).length < 2 ^ (prefixWord ++ tailWord_5265792).sum := by decide
  have hdescent : baseEnd_5265792 < baseStart_5265792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265793 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_5265793 : Nat := 118140960795 + 5265793 * 2 ^ 59
def prefixEnd_5265793 : Nat := 4983230072969 + 3 ^ 40 * 5265793 * 2
def baseEnd_5265793 : Nat := 2703882836081021294370565

theorem tailTrace_5265793 : CollatzResearch.WordTrace tailWord_5265793 prefixEnd_5265793 2703882836081021294370565 := by
  unfold tailWord_5265793
  simp only [CollatzResearch.WordTrace]
  refine ⟨192059249011938761690522033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128039499341292507793681355 192059249011938761690522033)
  ·
    refine ⟨144044436758954071267891525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192059249011938761690522033 144044436758954071267891525)
    ·
      refine ⟨27008331892303888362729661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144044436758954071267891525 27008331892303888362729661)
      ·
        refine ⟨10128124459613958136023623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27008331892303888362729661 10128124459613958136023623)
        ·
          refine ⟨15192186689420937204035435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10128124459613958136023623 15192186689420937204035435)
          ·
            refine ⟨22788280034131405806053153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15192186689420937204035435 22788280034131405806053153)
            ·
              refine ⟨17091210025598554354539865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22788280034131405806053153 17091210025598554354539865)
              ·
                refine ⟨12818407519198915765904899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17091210025598554354539865 12818407519198915765904899)
                ·
                  refine ⟨19227611278798373648857349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12818407519198915765904899 19227611278798373648857349)
                  ·
                    refine ⟨3605177114774695059160753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19227611278798373648857349 3605177114774695059160753)
                    ·
                      refine ⟨2703882836081021294370565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605177114774695059160753 2703882836081021294370565)
                      ·
                        rfl

theorem cell23_5265793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_5265793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265793 prefixEnd_5265793 := by exact prefixLift 5265793
  have htrace : WordTrace (prefixWord ++ tailWord_5265793) baseStart_5265793 baseEnd_5265793 := by
    simpa [prefixWord, tailWord_5265793, baseEnd_5265793] using wordTrace_append hprefix tailTrace_5265793
  have hstable : (prefixWord ++ tailWord_5265793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265793).length < 2 ^ (prefixWord ++ tailWord_5265793).sum := by decide
  have hdescent : baseEnd_5265793 < baseStart_5265793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265806 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5265806 : Nat := 118140960795 + 5265806 * 2 ^ 59
def prefixEnd_5265806 : Nat := 4983230072969 + 3 ^ 40 * 5265806 * 2
def baseEnd_5265806 : Nat := 2703889511329529743508005

theorem tailTrace_5265806 : CollatzResearch.WordTrace tailWord_5265806 prefixEnd_5265806 2703889511329529743508005 := by
  unfold tailWord_5265806
  simp only [CollatzResearch.WordTrace]
  refine ⟨24007465395111458113843159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128039815440594443273830181 24007465395111458113843159)
  ·
    refine ⟨36011198092667187170764739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24007465395111458113843159 36011198092667187170764739)
    ·
      refine ⟨54016797139000780756147109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36011198092667187170764739 54016797139000780756147109)
      ·
        refine ⟨10128149463562646391777583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54016797139000780756147109 10128149463562646391777583)
        ·
          refine ⟨15192224195343969587666375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10128149463562646391777583 15192224195343969587666375)
          ·
            refine ⟨22788336293015954381499563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15192224195343969587666375 22788336293015954381499563)
            ·
              refine ⟨34182504439523931572249345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22788336293015954381499563 34182504439523931572249345)
              ·
                refine ⟨25636878329642948679187009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34182504439523931572249345 25636878329642948679187009)
                ·
                  refine ⟨19227658747232211509390257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25636878329642948679187009 19227658747232211509390257)
                  ·
                    refine ⟨14420744060424158632042693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19227658747232211509390257 14420744060424158632042693)
                    ·
                      refine ⟨2703889511329529743508005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14420744060424158632042693 2703889511329529743508005)
                      ·
                        rfl

theorem cell23_5265806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5265806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265806 prefixEnd_5265806 := by exact prefixLift 5265806
  have htrace : WordTrace (prefixWord ++ tailWord_5265806) baseStart_5265806 baseEnd_5265806 := by
    simpa [prefixWord, tailWord_5265806, baseEnd_5265806] using wordTrace_append hprefix tailTrace_5265806
  have hstable : (prefixWord ++ tailWord_5265806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265806).length < 2 ^ (prefixWord ++ tailWord_5265806).sum := by decide
  have hdescent : baseEnd_5265806 < baseStart_5265806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265816 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 7]
def baseStart_5265816 : Nat := 118140960795 + 5265816 * 2 ^ 59
def prefixEnd_5265816 : Nat := 4983230072969 + 3 ^ 40 * 5265816 * 2
def baseEnd_5265816 : Nat := 300432738459563856042551

theorem tailTrace_5265816 : CollatzResearch.WordTrace tailWord_5265816 prefixEnd_5265816 300432738459563856042551 := by
  unfold tailWord_5265816
  simp only [CollatzResearch.WordTrace]
  refine ⟨96030043945427718309304651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128040058593903624412406201 96030043945427718309304651)
  ·
    refine ⟨144045065918141577463956977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96030043945427718309304651 144045065918141577463956977)
    ·
      refine ⟨108033799438606183097967733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144045065918141577463956977 108033799438606183097967733)
      ·
        refine ⟨10128168697369329665434475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108033799438606183097967733 10128168697369329665434475)
        ·
          refine ⟨15192253046053994498151713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10128168697369329665434475 15192253046053994498151713)
          ·
            refine ⟨11394189784540495873613785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15192253046053994498151713 11394189784540495873613785)
            ·
              refine ⟨8545642338405371905210339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11394189784540495873613785 8545642338405371905210339)
              ·
                refine ⟨12818463507608057857815509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8545642338405371905210339 12818463507608057857815509)
                ·
                  refine ⟨300432738459563856042551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12818463507608057857815509 300432738459563856042551)
                  ·
                    rfl

theorem cell23_5265816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 7].length) (baseStart_5265816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265816 prefixEnd_5265816 := by exact prefixLift 5265816
  have htrace : WordTrace (prefixWord ++ tailWord_5265816) baseStart_5265816 baseEnd_5265816 := by
    simpa [prefixWord, tailWord_5265816, baseEnd_5265816] using wordTrace_append hprefix tailTrace_5265816
  have hstable : (prefixWord ++ tailWord_5265816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265816).length < 2 ^ (prefixWord ++ tailWord_5265816).sum := by decide
  have hdescent : baseEnd_5265816 < baseStart_5265816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265826 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_5265826 : Nat := 118140960795 + 5265826 * 2 ^ 59
def prefixEnd_5265826 : Nat := 4983230072969 + 3 ^ 40 * 5265826 * 2
def baseEnd_5265826 : Nat := 2703899780942619665257913

theorem tailTrace_5265826 : CollatzResearch.WordTrace tailWord_5265826 prefixEnd_5265826 2703899780942619665257913 := by
  unfold tailWord_5265826
  simp only [CollatzResearch.WordTrace]
  refine ⟨48015113155204802081618333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128040301747212805550982221 48015113155204802081618333)
  ·
    refine ⟨18005667433201800780606875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48015113155204802081618333 18005667433201800780606875)
    ·
      refine ⟨27008501149802701170910313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18005667433201800780606875 27008501149802701170910313)
      ·
        refine ⟨20256375862352025878182735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27008501149802701170910313 20256375862352025878182735)
        ·
          refine ⟨30384563793528038817274103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20256375862352025878182735 30384563793528038817274103)
          ·
            refine ⟨45576845690292058225911155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30384563793528038817274103 45576845690292058225911155)
            ·
              refine ⟨68365268535438087338866733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45576845690292058225911155 68365268535438087338866733)
              ·
                refine ⟨25636975700789282752075025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68365268535438087338866733 25636975700789282752075025)
                ·
                  refine ⟨19227731775591962064056269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25636975700789282752075025 19227731775591962064056269)
                  ·
                    refine ⟨7210399415846985774021101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19227731775591962064056269 7210399415846985774021101)
                    ·
                      refine ⟨2703899780942619665257913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7210399415846985774021101 2703899780942619665257913)
                      ·
                        rfl

theorem cell23_5265826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_5265826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265826 prefixEnd_5265826 := by exact prefixLift 5265826
  have htrace : WordTrace (prefixWord ++ tailWord_5265826) baseStart_5265826 baseEnd_5265826 := by
    simpa [prefixWord, tailWord_5265826, baseEnd_5265826] using wordTrace_append hprefix tailTrace_5265826
  have hstable : (prefixWord ++ tailWord_5265826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265826).length < 2 ^ (prefixWord ++ tailWord_5265826).sum := by decide
  have hdescent : baseEnd_5265826 < baseStart_5265826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265866 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_5265866 : Nat := 118140960795 + 5265866 * 2 ^ 59
def prefixEnd_5265866 : Nat := 4983230072969 + 3 ^ 40 * 5265866 * 2
def baseEnd_5265866 : Nat := 2703920320168799508757729

theorem tailTrace_5265866 : CollatzResearch.WordTrace tailWord_5265866 prefixEnd_5265866 2703920320168799508757729 := by
  unfold tailWord_5265866
  simp only [CollatzResearch.WordTrace]
  refine ⟨48015477885168573789482363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128041274360449530105286301 48015477885168573789482363)
  ·
    refine ⟨72023216827752860684223545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48015477885168573789482363 72023216827752860684223545)
    ·
      refine ⟨54017412620814645513167659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72023216827752860684223545 54017412620814645513167659)
      ·
        refine ⟨81026118931221968269751489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54017412620814645513167659 81026118931221968269751489)
        ·
          refine ⟨60769589198416476202313617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81026118931221968269751489 60769589198416476202313617)
          ·
            refine ⟨45577191898812357151735213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60769589198416476202313617 45577191898812357151735213)
            ·
              refine ⟨17091446962054633931900705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45577191898812357151735213 17091446962054633931900705)
              ·
                refine ⟨12818585221540975448925529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17091446962054633931900705 12818585221540975448925529)
                ·
                  refine ⟨9613938916155731586694147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12818585221540975448925529 9613938916155731586694147)
                  ·
                    refine ⟨14420908374233597380041221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9613938916155731586694147 14420908374233597380041221)
                    ·
                      refine ⟨2703920320168799508757729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14420908374233597380041221 2703920320168799508757729)
                      ·
                        rfl

theorem cell23_5265866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_5265866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265866 prefixEnd_5265866 := by exact prefixLift 5265866
  have htrace : WordTrace (prefixWord ++ tailWord_5265866) baseStart_5265866 baseEnd_5265866 := by
    simpa [prefixWord, tailWord_5265866, baseEnd_5265866] using wordTrace_append hprefix tailTrace_5265866
  have hstable : (prefixWord ++ tailWord_5265866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265866).length < 2 ^ (prefixWord ++ tailWord_5265866).sum := by decide
  have hdescent : baseEnd_5265866 < baseStart_5265866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265910 : List Nat := [5, 1, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_5265910 : Nat := 118140960795 + 5265910 * 2 ^ 59
def prefixEnd_5265910 : Nat := 4983230072969 + 3 ^ 40 * 5265910 * 2
def baseEnd_5265910 : Nat := 901314304439199112202509

theorem tailTrace_5265910 : CollatzResearch.WordTrace tailWord_5265910 prefixEnd_5265910 901314304439199112202509 := by
  unfold tailWord_5265910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12003969772032180667033199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128042344235009927115020789 12003969772032180667033199)
  ·
    refine ⟨18005954658048271000549799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12003969772032180667033199 18005954658048271000549799)
    ·
      refine ⟨27008931987072406500824699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18005954658048271000549799 27008931987072406500824699)
      ·
        refine ⟨40513397980608609751237049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27008931987072406500824699 40513397980608609751237049)
        ·
          refine ⟨30385048485456457313427787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40513397980608609751237049 30385048485456457313427787)
          ·
            refine ⟨45577572728184685970141681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30385048485456457313427787 45577572728184685970141681)
            ·
              refine ⟨34183179546138514477606261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45577572728184685970141681 34183179546138514477606261)
              ·
                refine ⟨3204673082450485732275587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34183179546138514477606261 3204673082450485732275587)
                ·
                  refine ⟨4807009623675728598413381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204673082450485732275587 4807009623675728598413381)
                  ·
                    refine ⟨901314304439199112202509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4807009623675728598413381 901314304439199112202509)
                    ·
                      rfl

theorem cell23_5265910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_5265910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265910 prefixEnd_5265910 := by exact prefixLift 5265910
  have htrace : WordTrace (prefixWord ++ tailWord_5265910) baseStart_5265910 baseEnd_5265910 := by
    simpa [prefixWord, tailWord_5265910, baseEnd_5265910] using wordTrace_append hprefix tailTrace_5265910
  have hstable : (prefixWord ++ tailWord_5265910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265910).length < 2 ^ (prefixWord ++ tailWord_5265910).sum := by decide
  have hdescent : baseEnd_5265910 < baseStart_5265910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265960 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_5265960 : Nat := 118140960795 + 5265960 * 2 ^ 59
def prefixEnd_5265960 : Nat := 4983230072969 + 3 ^ 40 * 5265960 * 2
def baseEnd_5265960 : Nat := 2703968587350322140982297

theorem tailTrace_5265960 : CollatzResearch.WordTrace tailWord_5265960 prefixEnd_5265960 2703968587350322140982297 := by
  unfold tailWord_5265960
  simp only [CollatzResearch.WordTrace]
  refine ⟨96032670001166874605925667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128043560001555832807900889 96032670001166874605925667)
  ·
    refine ⟨144049005001750311908888501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96032670001166874605925667 144049005001750311908888501)
    ·
      refine ⟨13504594218914091741458297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144049005001750311908888501 13504594218914091741458297)
      ·
        refine ⟨10128445664185568806093723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13504594218914091741458297 10128445664185568806093723)
        ·
          refine ⟨15192668496278353209140585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10128445664185568806093723 15192668496278353209140585)
          ·
            refine ⟨11394501372208764906855439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15192668496278353209140585 11394501372208764906855439)
            ·
              refine ⟨17091752058313147360283159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11394501372208764906855439 17091752058313147360283159)
              ·
                refine ⟨25637628087469721040424739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17091752058313147360283159 25637628087469721040424739)
                ·
                  refine ⟨38456442131204581560637109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25637628087469721040424739 38456442131204581560637109)
                  ·
                    refine ⟨3605291449800429521309729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38456442131204581560637109 3605291449800429521309729)
                    ·
                      refine ⟨2703968587350322140982297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605291449800429521309729 2703968587350322140982297)
                      ·
                        rfl

theorem cell23_5265960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_5265960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265960 prefixEnd_5265960 := by exact prefixLift 5265960
  have htrace : WordTrace (prefixWord ++ tailWord_5265960) baseStart_5265960 baseEnd_5265960 := by
    simpa [prefixWord, tailWord_5265960, baseEnd_5265960] using wordTrace_append hprefix tailTrace_5265960
  have hstable : (prefixWord ++ tailWord_5265960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265960).length < 2 ^ (prefixWord ++ tailWord_5265960).sum := by decide
  have hdescent : baseEnd_5265960 < baseStart_5265960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265973 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_5265973 : Nat := 118140960795 + 5265973 * 2 ^ 59
def prefixEnd_5265973 : Nat := 4983230072969 + 3 ^ 40 * 5265973 * 2
def baseEnd_5265973 : Nat := 2703975262598830590119737

theorem tailTrace_5265973 : CollatzResearch.WordTrace tailWord_5265973 prefixEnd_5265973 2703975262598830590119737 := by
  unfold tailWord_5265973
  simp only [CollatzResearch.WordTrace]
  refine ⟨192065814151286652432074573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128043876100857768288049715 192065814151286652432074573)
  ·
    refine ⟨72024680306732494662027965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192065814151286652432074573 72024680306732494662027965)
    ·
      refine ⟨27009255115024685498260487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72024680306732494662027965 27009255115024685498260487)
      ·
        refine ⟨40513882672537028247390731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27009255115024685498260487 40513882672537028247390731)
        ·
          refine ⟨60770824008805542371086097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40513882672537028247390731 60770824008805542371086097)
          ·
            refine ⟨45578118006604156778314573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60770824008805542371086097 45578118006604156778314573)
            ·
              refine ⟨17091794252476558791867965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45578118006604156778314573 17091794252476558791867965)
              ·
                refine ⟨6409422844678709546950487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17091794252476558791867965 6409422844678709546950487)
                ·
                  refine ⟨9614134267018064320425731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409422844678709546950487 9614134267018064320425731)
                  ·
                    refine ⟨14421201400527096480638597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9614134267018064320425731 14421201400527096480638597)
                    ·
                      refine ⟨2703975262598830590119737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14421201400527096480638597 2703975262598830590119737)
                      ·
                        rfl

theorem cell23_5265973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_5265973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265973 prefixEnd_5265973 := by exact prefixLift 5265973
  have htrace : WordTrace (prefixWord ++ tailWord_5265973) baseStart_5265973 baseEnd_5265973 := by
    simpa [prefixWord, tailWord_5265973, baseEnd_5265973] using wordTrace_append hprefix tailTrace_5265973
  have hstable : (prefixWord ++ tailWord_5265973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265973).length < 2 ^ (prefixWord ++ tailWord_5265973).sum := by decide
  have hdescent : baseEnd_5265973 < baseStart_5265973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5265976 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_5265976 : Nat := 118140960795 + 5265976 * 2 ^ 59
def prefixEnd_5265976 : Nat := 4983230072969 + 3 ^ 40 * 5265976 * 2
def baseEnd_5265976 : Nat := 2703976803040794078382223

theorem tailTrace_5265976 : CollatzResearch.WordTrace tailWord_5265976 prefixEnd_5265976 2703976803040794078382223 := by
  unfold tailWord_5265976
  simp only [CollatzResearch.WordTrace]
  refine ⟨96032961785137891972216891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128043949046850522629622521 96032961785137891972216891)
  ·
    refine ⟨144049442677706837958325337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96032961785137891972216891 144049442677706837958325337)
    ·
      refine ⟨108037082008280128468744003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144049442677706837958325337 108037082008280128468744003)
      ·
        refine ⟨162055623012420192703116005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108037082008280128468744003 162055623012420192703116005)
        ·
          refine ⟨30385429314828786131834251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162055623012420192703116005 30385429314828786131834251)
          ·
            refine ⟨45578143972243179197751377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30385429314828786131834251 45578143972243179197751377)
            ·
              refine ⟨34183607979182384398313533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45578143972243179197751377 34183607979182384398313533)
              ·
                refine ⟨12818852992193394149367575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34183607979182384398313533 12818852992193394149367575)
                ·
                  refine ⟨19228279488290091224051363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12818852992193394149367575 19228279488290091224051363)
                  ·
                    refine ⟨28842419232435136836077045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19228279488290091224051363 28842419232435136836077045)
                    ·
                      refine ⟨2703976803040794078382223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28842419232435136836077045 2703976803040794078382223)
                      ·
                        rfl

theorem cell23_5265976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_5265976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5265976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5265976 prefixEnd_5265976 := by exact prefixLift 5265976
  have htrace : WordTrace (prefixWord ++ tailWord_5265976) baseStart_5265976 baseEnd_5265976 := by
    simpa [prefixWord, tailWord_5265976, baseEnd_5265976] using wordTrace_append hprefix tailTrace_5265976
  have hstable : (prefixWord ++ tailWord_5265976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5265976).length < 2 ^ (prefixWord ++ tailWord_5265976).sum := by decide
  have hdescent : baseEnd_5265976 < baseStart_5265976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5265976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266018 : List Nat := [3, 3, 2, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5266018 : Nat := 118140960795 + 5266018 * 2 ^ 59
def prefixEnd_5266018 : Nat := 4983230072969 + 3 ^ 40 * 5266018 * 2
def baseEnd_5266018 : Nat := 2703998369228282914057031

theorem tailTrace_5266018 : CollatzResearch.WordTrace tailWord_5266018 prefixEnd_5266018 2703998369228282914057031 := by
  unfold tailWord_5266018
  simp only [CollatzResearch.WordTrace]
  refine ⟨48016863859030906279365677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128044970290749083411641805 48016863859030906279365677)
  ·
    refine ⟨18006323947136589854762129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48016863859030906279365677 18006323947136589854762129)
    ·
      refine ⟨13504742960352442391071597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18006323947136589854762129 13504742960352442391071597)
      ·
        refine ⟨5064278610132165896651849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13504742960352442391071597 5064278610132165896651849)
        ·
          refine ⟨3798208957599124422488887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5064278610132165896651849 3798208957599124422488887)
          ·
            refine ⟨5697313436398686633733331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798208957599124422488887 5697313436398686633733331)
            ·
              refine ⟨8545970154598029950599997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697313436398686633733331 8545970154598029950599997)
              ·
                refine ⟨3204738807974261231474999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8545970154598029950599997 3204738807974261231474999)
                ·
                  refine ⟨4807108211961391847212499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204738807974261231474999 4807108211961391847212499)
                  ·
                    refine ⟨7210662317942087770818749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4807108211961391847212499 7210662317942087770818749)
                    ·
                      refine ⟨2703998369228282914057031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7210662317942087770818749 2703998369228282914057031)
                      ·
                        rfl

theorem cell23_5266018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5266018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266018 prefixEnd_5266018 := by exact prefixLift 5266018
  have htrace : WordTrace (prefixWord ++ tailWord_5266018) baseStart_5266018 baseEnd_5266018 := by
    simpa [prefixWord, tailWord_5266018, baseEnd_5266018] using wordTrace_append hprefix tailTrace_5266018
  have hstable : (prefixWord ++ tailWord_5266018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266018).length < 2 ^ (prefixWord ++ tailWord_5266018).sum := by decide
  have hdescent : baseEnd_5266018 < baseStart_5266018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266033 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 7, 3, 2]
def baseStart_5266033 : Nat := 118140960795 + 5266033 * 2 ^ 59
def prefixEnd_5266033 : Nat := 4983230072969 + 3 ^ 40 * 5266033 * 2
def baseEnd_5266033 : Nat := 2704006071438100355369461

theorem tailTrace_5266033 : CollatzResearch.WordTrace tailWord_5266033 prefixEnd_5266033 2704006071438100355369461 := by
  unfold tailWord_5266033
  simp only [CollatzResearch.WordTrace]
  refine ⟨192068002531069282679258753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128045335020712855119505835 192068002531069282679258753)
  ·
    refine ⟨144051001898301962009444065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192068002531069282679258753 144051001898301962009444065)
    ·
      refine ⟨108038251423726471507083049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144051001898301962009444065 108038251423726471507083049)
      ·
        refine ⟨81028688567794853630312287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108038251423726471507083049 81028688567794853630312287)
        ·
          refine ⟨121543032851692280445468431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81028688567794853630312287 121543032851692280445468431)
          ·
            refine ⟨182314549277538420668202647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121543032851692280445468431 182314549277538420668202647)
            ·
              refine ⟨273471823916307631002303971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182314549277538420668202647 273471823916307631002303971)
              ·
                refine ⟨410207735874461446503455957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273471823916307631002303971 410207735874461446503455957)
                ·
                  refine ⟨9614243809557690152424749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 410207735874461446503455957 9614243809557690152424749)
                  ·
                    refine ⟨3605341428584133807159281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9614243809557690152424749 3605341428584133807159281)
                    ·
                      refine ⟨2704006071438100355369461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605341428584133807159281 2704006071438100355369461)
                      ·
                        rfl

theorem cell23_5266033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_5266033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266033 prefixEnd_5266033 := by exact prefixLift 5266033
  have htrace : WordTrace (prefixWord ++ tailWord_5266033) baseStart_5266033 baseEnd_5266033 := by
    simpa [prefixWord, tailWord_5266033, baseEnd_5266033] using wordTrace_append hprefix tailTrace_5266033
  have hstable : (prefixWord ++ tailWord_5266033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266033).length < 2 ^ (prefixWord ++ tailWord_5266033).sum := by decide
  have hdescent : baseEnd_5266033 < baseStart_5266033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266153 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_5266153 : Nat := 118140960795 + 5266153 * 2 ^ 59
def prefixEnd_5266153 : Nat := 4983230072969 + 3 ^ 40 * 5266153 * 2
def baseEnd_5266153 : Nat := 2704067689116639885868909

theorem tailTrace_5266153 : CollatzResearch.WordTrace tailWord_5266153 prefixEnd_5266153 2704067689116639885868909 := by
  unfold tailWord_5266153
  simp only [CollatzResearch.WordTrace]
  refine ⟨192072379290634543173627113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128048252860423028782418075 192072379290634543173627113)
  ·
    refine ⟨144054284467975907380220335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192072379290634543173627113 144054284467975907380220335)
    ·
      refine ⟨216081426701963861070330503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144054284467975907380220335 216081426701963861070330503)
      ·
        refine ⟨324122140052945791605495755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216081426701963861070330503 324122140052945791605495755)
        ·
          refine ⟨486183210079418687408243633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324122140052945791605495755 486183210079418687408243633)
          ·
            refine ⟨364637407559564015556182725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486183210079418687408243633 364637407559564015556182725)
            ·
              refine ⟨68369513917418252916784261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 364637407559564015556182725 68369513917418252916784261)
              ·
                refine ⟨12819283859515922421897049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68369513917418252916784261 12819283859515922421897049)
                ·
                  refine ⟨9614462894636941816422787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12819283859515922421897049 9614462894636941816422787)
                  ·
                    refine ⟨14421694341955412724634181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9614462894636941816422787 14421694341955412724634181)
                    ·
                      refine ⟨2704067689116639885868909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14421694341955412724634181 2704067689116639885868909)
                      ·
                        rfl

theorem cell23_5266153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_5266153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266153 prefixEnd_5266153 := by exact prefixLift 5266153
  have htrace : WordTrace (prefixWord ++ tailWord_5266153) baseStart_5266153 baseEnd_5266153 := by
    simpa [prefixWord, tailWord_5266153, baseEnd_5266153] using wordTrace_append hprefix tailTrace_5266153
  have hstable : (prefixWord ++ tailWord_5266153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266153).length < 2 ^ (prefixWord ++ tailWord_5266153).sum := by decide
  have hdescent : baseEnd_5266153 < baseStart_5266153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266165 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5266165 : Nat := 118140960795 + 5266165 * 2 ^ 59
def prefixEnd_5266165 : Nat := 4983230072969 + 3 ^ 40 * 5266165 * 2
def baseEnd_5266165 : Nat := 2704073850884493838918855

theorem tailTrace_5266165 : CollatzResearch.WordTrace tailWord_5266165 prefixEnd_5266165 2704073850884493838918855 := by
  unfold tailWord_5266165
  simp only [CollatzResearch.WordTrace]
  refine ⟨192072816966591069223063949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128048544644394046148709299 192072816966591069223063949)
  ·
    refine ⟨72027306362471650958648981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192072816966591069223063949 72027306362471650958648981)
    ·
      refine ⟨3376279985740858638686671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72027306362471650958648981 3376279985740858638686671)
      ·
        refine ⟨5064419978611287958030007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3376279985740858638686671 5064419978611287958030007)
        ·
          refine ⟨7596629967916931937045011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064419978611287958030007 7596629967916931937045011)
          ·
            refine ⟨11394944951875397905567517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7596629967916931937045011 11394944951875397905567517)
            ·
              refine ⟨4273104356953274214587819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11394944951875397905567517 4273104356953274214587819)
              ·
                refine ⟨6409656535429911321881729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273104356953274214587819 6409656535429911321881729)
                ·
                  refine ⟨4807242401572433491411297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6409656535429911321881729 4807242401572433491411297)
                  ·
                    refine ⟨3605431801179325118558473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4807242401572433491411297 3605431801179325118558473)
                    ·
                      refine ⟨2704073850884493838918855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605431801179325118558473 2704073850884493838918855)
                      ·
                        rfl

theorem cell23_5266165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5266165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266165 prefixEnd_5266165 := by exact prefixLift 5266165
  have htrace : WordTrace (prefixWord ++ tailWord_5266165) baseStart_5266165 baseEnd_5266165 := by
    simpa [prefixWord, tailWord_5266165, baseEnd_5266165] using wordTrace_append hprefix tailTrace_5266165
  have hstable : (prefixWord ++ tailWord_5266165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266165).length < 2 ^ (prefixWord ++ tailWord_5266165).sum := by decide
  have hdescent : baseEnd_5266165 < baseStart_5266165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266170 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2]
def baseStart_5266170 : Nat := 118140960795 + 5266170 * 2 ^ 59
def prefixEnd_5266170 : Nat := 4983230072969 + 3 ^ 40 * 5266170 * 2
def baseEnd_5266170 : Nat := 2704076418287766319356331

theorem tailTrace_5266170 : CollatzResearch.WordTrace tailWord_5266170 prefixEnd_5266170 2704076418287766319356331 := by
  unfold tailWord_5266170
  simp only [CollatzResearch.WordTrace]
  refine ⟨48018249832893238769248991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128048666221048636717997309 48018249832893238769248991)
  ·
    refine ⟨72027374749339858153873487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48018249832893238769248991 72027374749339858153873487)
    ·
      refine ⟨108041062124009787230810231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72027374749339858153873487 108041062124009787230810231)
      ·
        refine ⟨162061593186014680846215347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108041062124009787230810231 162061593186014680846215347)
        ·
          refine ⟨243092389779022021269323021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162061593186014680846215347 243092389779022021269323021)
          ·
            refine ⟨91159646167133257975996133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243092389779022021269323021 91159646167133257975996133)
            ·
              refine ⟨17092433656337485870499275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91159646167133257975996133 17092433656337485870499275)
              ·
                refine ⟨25638650484506228805748913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17092433656337485870499275 25638650484506228805748913)
                ·
                  refine ⟨19228987863379671604311685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25638650484506228805748913 19228987863379671604311685)
                  ·
                    refine ⟨3605435224383688425808441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19228987863379671604311685 3605435224383688425808441)
                    ·
                      refine ⟨2704076418287766319356331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605435224383688425808441 2704076418287766319356331)
                      ·
                        rfl

theorem cell23_5266170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_5266170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266170 prefixEnd_5266170 := by exact prefixLift 5266170
  have htrace : WordTrace (prefixWord ++ tailWord_5266170) baseStart_5266170 baseEnd_5266170 := by
    simpa [prefixWord, tailWord_5266170, baseEnd_5266170] using wordTrace_append hprefix tailTrace_5266170
  have hstable : (prefixWord ++ tailWord_5266170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266170).length < 2 ^ (prefixWord ++ tailWord_5266170).sum := by decide
  have hdescent : baseEnd_5266170 < baseStart_5266170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266173 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_5266173 : Nat := 118140960795 + 5266173 * 2 ^ 59
def prefixEnd_5266173 : Nat := 4983230072969 + 3 ^ 40 * 5266173 * 2
def baseEnd_5266173 : Nat := 2704077958729729807618817

theorem tailTrace_5266173 : CollatzResearch.WordTrace tailWord_5266173 prefixEnd_5266173 2704077958729729807618817 := by
  unfold tailWord_5266173
  simp only [CollatzResearch.WordTrace]
  refine ⟨192073108750562086589355173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128048739167041391059570115 192073108750562086589355173)
  ·
    refine ⟨36013707890730391235504095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192073108750562086589355173 36013707890730391235504095)
    ·
      refine ⟨54020561836095586853256143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36013707890730391235504095 54020561836095586853256143)
      ·
        refine ⟨81030842754143380279884215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54020561836095586853256143 81030842754143380279884215)
        ·
          refine ⟨121546264131215070419826323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81030842754143380279884215 121546264131215070419826323)
          ·
            refine ⟨182319396196822605629739485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121546264131215070419826323 182319396196822605629739485)
            ·
              refine ⟨68369773573808477111152307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182319396196822605629739485 68369773573808477111152307)
              ·
                refine ⟨102554660360712715666728461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68369773573808477111152307 102554660360712715666728461)
                ·
                  refine ⟨38457997635267268375023173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102554660360712715666728461 38457997635267268375023173)
                  ·
                    refine ⟨7210874556612612820316845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38457997635267268375023173 7210874556612612820316845)
                    ·
                      refine ⟨2704077958729729807618817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7210874556612612820316845 2704077958729729807618817)
                      ·
                        rfl

theorem cell23_5266173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_5266173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266173 prefixEnd_5266173 := by exact prefixLift 5266173
  have htrace : WordTrace (prefixWord ++ tailWord_5266173) baseStart_5266173 baseEnd_5266173 := by
    simpa [prefixWord, tailWord_5266173, baseEnd_5266173] using wordTrace_append hprefix tailTrace_5266173
  have hstable : (prefixWord ++ tailWord_5266173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266173).length < 2 ^ (prefixWord ++ tailWord_5266173).sum := by decide
  have hdescent : baseEnd_5266173 < baseStart_5266173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266176 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 12]
def baseStart_5266176 : Nat := 118140960795 + 5266176 * 2 ^ 59
def prefixEnd_5266176 : Nat := 4983230072969 + 3 ^ 40 * 5266176 * 2
def baseEnd_5266176 : Nat := 300453277685743699542367

theorem tailTrace_5266176 : CollatzResearch.WordTrace tailWord_5266176 prefixEnd_5266176 300453277685743699542367 := by
  unfold tailWord_5266176
  simp only [CollatzResearch.WordTrace]
  refine ⟨96036609084775609050857191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128048812113034145401142921 96036609084775609050857191)
  ·
    refine ⟨144054913627163413576285787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96036609084775609050857191 144054913627163413576285787)
    ·
      refine ⟨216082370440745120364428681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144054913627163413576285787 216082370440745120364428681)
      ·
        refine ⟨162061777830558840273321511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216082370440745120364428681 162061777830558840273321511)
        ·
          refine ⟨243092666745838260409982267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162061777830558840273321511 243092666745838260409982267)
          ·
            refine ⟨364639000118757390614973401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243092666745838260409982267 364639000118757390614973401)
            ·
              refine ⟨273479250089068042961230051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364639000118757390614973401 273479250089068042961230051)
              ·
                refine ⟨410218875133602064441845077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273479250089068042961230051 410218875133602064441845077)
                ·
                  refine ⟨300453277685743699542367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 410218875133602064441845077 300453277685743699542367)
                  ·
                    rfl

theorem cell23_5266176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 12].length) (baseStart_5266176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266176 prefixEnd_5266176 := by exact prefixLift 5266176
  have htrace : WordTrace (prefixWord ++ tailWord_5266176) baseStart_5266176 baseEnd_5266176 := by
    simpa [prefixWord, tailWord_5266176, baseEnd_5266176] using wordTrace_append hprefix tailTrace_5266176
  have hstable : (prefixWord ++ tailWord_5266176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266176).length < 2 ^ (prefixWord ++ tailWord_5266176).sum := by decide
  have hdescent : baseEnd_5266176 < baseStart_5266176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266180 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_5266180 : Nat := 118140960795 + 5266180 * 2 ^ 59
def prefixEnd_5266180 : Nat := 4983230072969 + 3 ^ 40 * 5266180 * 2
def baseEnd_5266180 : Nat := 901360517698103760077095

theorem tailTrace_5266180 : CollatzResearch.WordTrace tailWord_5266180 prefixEnd_5266180 901360517698103760077095 := by
  unfold tailWord_5266180
  simp only [CollatzResearch.WordTrace]
  refine ⟨96036682030768363392429997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128048909374357817856573329 96036682030768363392429997)
  ·
    refine ⟨36013755761538136272161249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96036682030768363392429997 36013755761538136272161249)
    ·
      refine ⟨27010316821153602204120937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36013755761538136272161249 27010316821153602204120937)
      ·
        refine ⟨20257737615865201653090703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27010316821153602204120937 20257737615865201653090703)
        ·
          refine ⟨30386606423797802479636055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20257737615865201653090703 30386606423797802479636055)
          ·
            refine ⟨45579909635696703719454083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30386606423797802479636055 45579909635696703719454083)
            ·
              refine ⟨68369864453545055579181125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45579909635696703719454083 68369864453545055579181125)
              ·
                refine ⟨12819349585039697921096461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68369864453545055579181125 12819349585039697921096461)
                ·
                  refine ⟨4807256094389886720411173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12819349585039697921096461 4807256094389886720411173)
                  ·
                    refine ⟨901360517698103760077095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4807256094389886720411173 901360517698103760077095)
                    ·
                      rfl

theorem cell23_5266180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_5266180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266180 prefixEnd_5266180 := by exact prefixLift 5266180
  have htrace : WordTrace (prefixWord ++ tailWord_5266180) baseStart_5266180 baseEnd_5266180 := by
    simpa [prefixWord, tailWord_5266180, baseEnd_5266180] using wordTrace_append hprefix tailTrace_5266180
  have hstable : (prefixWord ++ tailWord_5266180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266180).length < 2 ^ (prefixWord ++ tailWord_5266180).sum := by decide
  have hdescent : baseEnd_5266180 < baseStart_5266180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266190 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_5266190 : Nat := 118140960795 + 5266190 * 2 ^ 59
def prefixEnd_5266190 : Nat := 4983230072969 + 3 ^ 40 * 5266190 * 2
def baseEnd_5266190 : Nat := 2704086687900856241106239

theorem tailTrace_5266190 : CollatzResearch.WordTrace tailWord_5266190 prefixEnd_5266190 2704086687900856241106239 := by
  unfold tailWord_5266190
  simp only [CollatzResearch.WordTrace]
  refine ⟨24009216098937562311590503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128049152527666998995149349 24009216098937562311590503)
  ·
    refine ⟨36013824148406343467385755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24009216098937562311590503 36013824148406343467385755)
    ·
      refine ⟨54020736222609515201078633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36013824148406343467385755 54020736222609515201078633)
      ·
        refine ⟨40515552166957136400808975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54020736222609515201078633 40515552166957136400808975)
        ·
          refine ⟨60773328250435704601213463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40515552166957136400808975 60773328250435704601213463)
          ·
            refine ⟨91159992375653556901820195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60773328250435704601213463 91159992375653556901820195)
            ·
              refine ⟨136739988563480335352730293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91159992375653556901820195 136739988563480335352730293)
              ·
                refine ⟨12819373927826281439318465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136739988563480335352730293 12819373927826281439318465)
                ·
                  refine ⟨9614530445869711079488849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12819373927826281439318465 9614530445869711079488849)
                  ·
                    refine ⟨7210897834402283309616637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9614530445869711079488849 7210897834402283309616637)
                    ·
                      refine ⟨2704086687900856241106239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7210897834402283309616637 2704086687900856241106239)
                      ·
                        rfl

theorem cell23_5266190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_5266190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266190 prefixEnd_5266190 := by exact prefixLift 5266190
  have htrace : WordTrace (prefixWord ++ tailWord_5266190) baseStart_5266190 baseEnd_5266190 := by
    simpa [prefixWord, tailWord_5266190, baseEnd_5266190] using wordTrace_append hprefix tailTrace_5266190
  have hstable : (prefixWord ++ tailWord_5266190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266190).length < 2 ^ (prefixWord ++ tailWord_5266190).sum := by decide
  have hdescent : baseEnd_5266190 < baseStart_5266190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266227 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 6]
def baseStart_5266227 : Nat := 118140960795 + 5266227 * 2 ^ 59
def prefixEnd_5266227 : Nat := 4983230072969 + 3 ^ 40 * 5266227 * 2
def baseEnd_5266227 : Nat := 300456187409452510704841

theorem tailTrace_5266227 : CollatzResearch.WordTrace tailWord_5266227 prefixEnd_5266227 300456187409452510704841 := by
  unfold tailWord_5266227
  simp only [CollatzResearch.WordTrace]
  refine ⟨192075078292366453811820935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128050052194910969207880623 192075078292366453811820935)
  ·
    refine ⟨288112617438549680717731403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192075078292366453811820935 288112617438549680717731403)
    ·
      refine ⟨432168926157824521076597105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288112617438549680717731403 432168926157824521076597105)
      ·
        refine ⟨324126694618368390807447829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432168926157824521076597105 324126694618368390807447829)
        ·
          refine ⟨15193438810236018319099117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 324126694618368390807447829 15193438810236018319099117)
          ·
            refine ⟨5697539553838506869662169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15193438810236018319099117 5697539553838506869662169)
            ·
              refine ⟨4273154665378880152246627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5697539553838506869662169 4273154665378880152246627)
              ·
                refine ⟨6409731998068320228369941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273154665378880152246627 6409731998068320228369941)
                ·
                  refine ⟨300456187409452510704841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6409731998068320228369941 300456187409452510704841)
                  ·
                    rfl

theorem cell23_5266227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 6].length) (baseStart_5266227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266227 prefixEnd_5266227 := by exact prefixLift 5266227
  have htrace : WordTrace (prefixWord ++ tailWord_5266227) baseStart_5266227 baseEnd_5266227 := by
    simpa [prefixWord, tailWord_5266227, baseEnd_5266227] using wordTrace_append hprefix tailTrace_5266227
  have hstable : (prefixWord ++ tailWord_5266227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266227).length < 2 ^ (prefixWord ++ tailWord_5266227).sum := by decide
  have hdescent : baseEnd_5266227 < baseStart_5266227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266273 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_5266273 : Nat := 118140960795 + 5266273 * 2 ^ 59
def prefixEnd_5266273 : Nat := 4983230072969 + 3 ^ 40 * 5266273 * 2
def baseEnd_5266273 : Nat := 2704129306795179416368357

theorem tailTrace_5266273 : CollatzResearch.WordTrace tailWord_5266273 prefixEnd_5266273 2704129306795179416368357 := by
  unfold tailWord_5266273
  simp only [CollatzResearch.WordTrace]
  refine ⟨192076756050199803667995473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128051170700133202445330315 192076756050199803667995473)
  ·
    refine ⟨144057567037649852750996605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192076756050199803667995473 144057567037649852750996605)
    ·
      refine ⟨54021587639118694781623727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144057567037649852750996605 54021587639118694781623727)
      ·
        refine ⟨81032381458678042172435591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54021587639118694781623727 81032381458678042172435591)
        ·
          refine ⟨121548572188017063258653387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81032381458678042172435591 121548572188017063258653387)
          ·
            refine ⟨182322858282025594887980081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121548572188017063258653387 182322858282025594887980081)
            ·
              refine ⟨136742143711519196165985061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182322858282025594887980081 136742143711519196165985061)
              ·
                refine ⟨25639151945909849281122199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136742143711519196165985061 25639151945909849281122199)
                ·
                  refine ⟨38458727918864773921683299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25639151945909849281122199 38458727918864773921683299)
                  ·
                    refine ⟨57688091878297160882524949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38458727918864773921683299 57688091878297160882524949)
                    ·
                      refine ⟨2704129306795179416368357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57688091878297160882524949 2704129306795179416368357)
                      ·
                        rfl

theorem cell23_5266273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_5266273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266273 prefixEnd_5266273 := by exact prefixLift 5266273
  have htrace : WordTrace (prefixWord ++ tailWord_5266273) baseStart_5266273 baseEnd_5266273 := by
    simpa [prefixWord, tailWord_5266273, baseEnd_5266273] using wordTrace_append hprefix tailTrace_5266273
  have hstable : (prefixWord ++ tailWord_5266273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266273).length < 2 ^ (prefixWord ++ tailWord_5266273).sum := by decide
  have hdescent : baseEnd_5266273 < baseStart_5266273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266283 : List Nat := [1, 1, 1, 1, 2, 2, 7, 8]
def baseStart_5266283 : Nat := 118140960795 + 5266283 * 2 ^ 59
def prefixEnd_5266283 : Nat := 4983230072969 + 3 ^ 40 * 5266283 * 2
def baseEnd_5266283 : Nat := 100153127466730532490493

theorem tailTrace_5266283 : CollatzResearch.WordTrace tailWord_5266283 prefixEnd_5266283 100153127466730532490493 := by
  unfold tailWord_5266283
  simp only [CollatzResearch.WordTrace]
  refine ⟨192077120780163575375859503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128051413853442383583906335 192077120780163575375859503)
  ·
    refine ⟨288115681170245363063789255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192077120780163575375859503 288115681170245363063789255)
    ·
      refine ⟨432173521755368044595683883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288115681170245363063789255 432173521755368044595683883)
      ·
        refine ⟨648260282633052066893525825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432173521755368044595683883 648260282633052066893525825)
        ·
          refine ⟨486195211974789050170144369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648260282633052066893525825 486195211974789050170144369)
          ·
            refine ⟨364646408981091787627608277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486195211974789050170144369 364646408981091787627608277)
            ·
              refine ⟨8546400210494338772522069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 364646408981091787627608277 8546400210494338772522069)
              ·
                refine ⟨100153127466730532490493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8546400210494338772522069 100153127466730532490493)
                ·
                  rfl

theorem cell23_5266283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 8].length) (baseStart_5266283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266283 prefixEnd_5266283 := by exact prefixLift 5266283
  have htrace : WordTrace (prefixWord ++ tailWord_5266283) baseStart_5266283 baseEnd_5266283 := by
    simpa [prefixWord, tailWord_5266283, baseEnd_5266283] using wordTrace_append hprefix tailTrace_5266283
  have hstable : (prefixWord ++ tailWord_5266283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266283).length < 2 ^ (prefixWord ++ tailWord_5266283).sum := by decide
  have hdescent : baseEnd_5266283 < baseStart_5266283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266290 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5266290 : Nat := 118140960795 + 5266290 * 2 ^ 59
def prefixEnd_5266290 : Nat := 4983230072969 + 3 ^ 40 * 5266290 * 2
def baseEnd_5266290 : Nat := 2704138035966305849855779

theorem tailTrace_5266290 : CollatzResearch.WordTrace tailWord_5266290 prefixEnd_5266290 2704138035966305849855779 := by
  unfold tailWord_5266290
  simp only [CollatzResearch.WordTrace]
  refine ⟨48019344022784553892841081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128051584060758810380909549 48019344022784553892841081)
  ·
    refine ⟨36014508017088415419630811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48019344022784553892841081 36014508017088415419630811)
    ·
      refine ⟨54021762025632623129446217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36014508017088415419630811 54021762025632623129446217)
      ·
        refine ⟨40516321519224467347084663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54021762025632623129446217 40516321519224467347084663)
        ·
          refine ⟨60774482278836701020626995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40516321519224467347084663 60774482278836701020626995)
          ·
            refine ⟨91161723418255051530940493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60774482278836701020626995 91161723418255051530940493)
            ·
              refine ⟨34185646281845644324102685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91161723418255051530940493 34185646281845644324102685)
              ·
                refine ⟨12819617355692116621538507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34185646281845644324102685 12819617355692116621538507)
                ·
                  refine ⟨19229426033538174932307761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12819617355692116621538507 19229426033538174932307761)
                  ·
                    refine ⟨14422069525153631199230821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19229426033538174932307761 14422069525153631199230821)
                    ·
                      refine ⟨2704138035966305849855779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14422069525153631199230821 2704138035966305849855779)
                      ·
                        rfl

theorem cell23_5266290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5266290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266290 prefixEnd_5266290 := by exact prefixLift 5266290
  have htrace : WordTrace (prefixWord ++ tailWord_5266290) baseStart_5266290 baseEnd_5266290 := by
    simpa [prefixWord, tailWord_5266290, baseEnd_5266290] using wordTrace_append hprefix tailTrace_5266290
  have hstable : (prefixWord ++ tailWord_5266290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266290).length < 2 ^ (prefixWord ++ tailWord_5266290).sum := by decide
  have hdescent : baseEnd_5266290 < baseStart_5266290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266311 : List Nat := [1, 1, 4, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_5266311 : Nat := 118140960795 + 5266311 * 2 ^ 59
def prefixEnd_5266311 : Nat := 4983230072969 + 3 ^ 40 * 5266311 * 2
def baseEnd_5266311 : Nat := 2704148819060050267693183

theorem tailTrace_5266311 : CollatzResearch.WordTrace tailWord_5266311 prefixEnd_5266311 2704148819060050267693183 := by
  unfold tailWord_5266311
  simp only [CollatzResearch.WordTrace]
  refine ⟨192078142024062136157878787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128052094682708090771919191 192078142024062136157878787)
  ·
    refine ⟨288117213036093204236818181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192078142024062136157878787 288117213036093204236818181)
    ·
      refine ⟨54021977444267475794403409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288117213036093204236818181 54021977444267475794403409)
      ·
        refine ⟨40516483083200606845802557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54021977444267475794403409 40516483083200606845802557)
        ·
          refine ⟨15193681156200227567175959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40516483083200606845802557 15193681156200227567175959)
          ·
            refine ⟨22790521734300341350763939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15193681156200227567175959 22790521734300341350763939)
            ·
              refine ⟨34185782601450512026145909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22790521734300341350763939 34185782601450512026145909)
              ·
                refine ⟨3204917118885985502451179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34185782601450512026145909 3204917118885985502451179)
                ·
                  refine ⟨4807375678328978253676769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204917118885985502451179 4807375678328978253676769)
                  ·
                    refine ⟨3605531758746733690257577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4807375678328978253676769 3605531758746733690257577)
                    ·
                      refine ⟨2704148819060050267693183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605531758746733690257577 2704148819060050267693183)
                      ·
                        rfl

theorem cell23_5266311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_5266311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266311 prefixEnd_5266311 := by exact prefixLift 5266311
  have htrace : WordTrace (prefixWord ++ tailWord_5266311) baseStart_5266311 baseEnd_5266311 := by
    simpa [prefixWord, tailWord_5266311, baseEnd_5266311] using wordTrace_append hprefix tailTrace_5266311
  have hstable : (prefixWord ++ tailWord_5266311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266311).length < 2 ^ (prefixWord ++ tailWord_5266311).sum := by decide
  have hdescent : baseEnd_5266311 < baseStart_5266311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266314 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5266314 : Nat := 118140960795 + 5266314 * 2 ^ 59
def prefixEnd_5266314 : Nat := 4983230072969 + 3 ^ 40 * 5266314 * 2
def baseEnd_5266314 : Nat := 2704150359502013755955669

theorem tailTrace_5266314 : CollatzResearch.WordTrace tailWord_5266314 prefixEnd_5266314 2704150359502013755955669 := by
  unfold tailWord_5266314
  simp only [CollatzResearch.WordTrace]
  refine ⟨48019562860762816917559499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128052167628700845113491997 48019562860762816917559499)
  ·
    refine ⟨72029344291144225376339249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48019562860762816917559499 72029344291144225376339249)
    ·
      refine ⟨54022008218358169032254437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72029344291144225376339249 54022008218358169032254437)
      ·
        refine ⟨10129126540942156693547707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54022008218358169032254437 10129126540942156693547707)
        ·
          refine ⟨15193689811413235040321561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10129126540942156693547707 15193689811413235040321561)
          ·
            refine ⟨11395267358559926280241171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15193689811413235040321561 11395267358559926280241171)
            ·
              refine ⟨17092901037839889420361757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11395267358559926280241171 17092901037839889420361757)
              ·
                refine ⟨6409837889189958532635659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17092901037839889420361757 6409837889189958532635659)
                ·
                  refine ⟨9614756833784937798953489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409837889189958532635659 9614756833784937798953489)
                  ·
                    refine ⟨7211067625338703349215117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9614756833784937798953489 7211067625338703349215117)
                    ·
                      refine ⟨2704150359502013755955669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7211067625338703349215117 2704150359502013755955669)
                      ·
                        rfl

theorem cell23_5266314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5266314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266314 prefixEnd_5266314 := by exact prefixLift 5266314
  have htrace : WordTrace (prefixWord ++ tailWord_5266314) baseStart_5266314 baseEnd_5266314 := by
    simpa [prefixWord, tailWord_5266314, baseEnd_5266314] using wordTrace_append hprefix tailTrace_5266314
  have hstable : (prefixWord ++ tailWord_5266314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266314).length < 2 ^ (prefixWord ++ tailWord_5266314).sum := by decide
  have hdescent : baseEnd_5266314 < baseStart_5266314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266320 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 9, 2]
def baseStart_5266320 : Nat := 118140960795 + 5266320 * 2 ^ 59
def prefixEnd_5266320 : Nat := 4983230072969 + 3 ^ 40 * 5266320 * 2
def baseEnd_5266320 : Nat := 2704153440385940732480641

theorem tailTrace_5266320 : CollatzResearch.WordTrace tailWord_5266320 prefixEnd_5266320 2704153440385940732480641 := by
  unfold tailWord_5266320
  simp only [CollatzResearch.WordTrace]
  refine ⟨96039235140514765347478207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128052313520686353796637609 96039235140514765347478207)
  ·
    refine ⟨144058852710772148021217311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96039235140514765347478207 144058852710772148021217311)
    ·
      refine ⟨216088279066158222031825967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144058852710772148021217311 216088279066158222031825967)
      ·
        refine ⟨324132418599237333047738951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216088279066158222031825967 324132418599237333047738951)
        ·
          refine ⟨486198627898855999571608427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324132418599237333047738951 486198627898855999571608427)
          ·
            refine ⟨729297941848283999357412641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486198627898855999571608427 729297941848283999357412641)
            ·
              refine ⟨546973456386212999518059481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729297941848283999357412641 546973456386212999518059481)
              ·
                refine ⟨410230092289659749638544611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546973456386212999518059481 410230092289659749638544611)
                ·
                  refine ⟨615345138434489624457816917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410230092289659749638544611 615345138434489624457816917)
                  ·
                    refine ⟨3605537920514587643307521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 615345138434489624457816917 3605537920514587643307521)
                    ·
                      refine ⟨2704153440385940732480641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605537920514587643307521 2704153440385940732480641)
                      ·
                        rfl

theorem cell23_5266320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 9, 2].length) (baseStart_5266320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266320 prefixEnd_5266320 := by exact prefixLift 5266320
  have htrace : WordTrace (prefixWord ++ tailWord_5266320) baseStart_5266320 baseEnd_5266320 := by
    simpa [prefixWord, tailWord_5266320, baseEnd_5266320] using wordTrace_append hprefix tailTrace_5266320
  have hstable : (prefixWord ++ tailWord_5266320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266320).length < 2 ^ (prefixWord ++ tailWord_5266320).sum := by decide
  have hdescent : baseEnd_5266320 < baseStart_5266320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266323 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 5]
def baseStart_5266323 : Nat := 118140960795 + 5266323 * 2 ^ 59
def prefixEnd_5266323 : Nat := 4983230072969 + 3 ^ 40 * 5266323 * 2
def baseEnd_5266323 : Nat := 2704154980827904220743127

theorem tailTrace_5266323 : CollatzResearch.WordTrace tailWord_5266323 prefixEnd_5266323 2704154980827904220743127 := by
  unfold tailWord_5266323
  simp only [CollatzResearch.WordTrace]
  refine ⟨192078579700018662207315623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128052386466679108138210415 192078579700018662207315623)
  ·
    refine ⟨288117869550027993310973435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192078579700018662207315623 288117869550027993310973435)
    ·
      refine ⟨432176804325041989966460153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288117869550027993310973435 432176804325041989966460153)
      ·
        refine ⟨324132603243781492474845115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432176804325041989966460153 324132603243781492474845115)
        ·
          refine ⟨486198904865672238712267673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324132603243781492474845115 486198904865672238712267673)
          ·
            refine ⟨364649178649254179034200755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486198904865672238712267673 364649178649254179034200755)
            ·
              refine ⟨546973767973881268551301133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364649178649254179034200755 546973767973881268551301133)
              ·
                refine ⟨205115162990205475706737925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 546973767973881268551301133 205115162990205475706737925)
                ·
                  refine ⟨38459093060663526695013361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205115162990205475706737925 38459093060663526695013361)
                  ·
                    refine ⟨28844319795497645021260021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38459093060663526695013361 28844319795497645021260021)
                    ·
                      refine ⟨2704154980827904220743127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28844319795497645021260021 2704154980827904220743127)
                      ·
                        rfl

theorem cell23_5266323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_5266323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266323 prefixEnd_5266323 := by exact prefixLift 5266323
  have htrace : WordTrace (prefixWord ++ tailWord_5266323) baseStart_5266323 baseEnd_5266323 := by
    simpa [prefixWord, tailWord_5266323, baseEnd_5266323] using wordTrace_append hprefix tailTrace_5266323
  have hstable : (prefixWord ++ tailWord_5266323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266323).length < 2 ^ (prefixWord ++ tailWord_5266323).sum := by decide
  have hdescent : baseEnd_5266323 < baseStart_5266323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266327 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_5266327 : Nat := 118140960795 + 5266327 * 2 ^ 59
def prefixEnd_5266327 : Nat := 4983230072969 + 3 ^ 40 * 5266327 * 2
def baseEnd_5266327 : Nat := 2704157034750522205093109

theorem tailTrace_5266327 : CollatzResearch.WordTrace tailWord_5266327 prefixEnd_5266327 2704157034750522205093109 := by
  unfold tailWord_5266327
  simp only [CollatzResearch.WordTrace]
  refine ⟨192078725592004170890461235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128052483728002780593640823 192078725592004170890461235)
  ·
    refine ⟨288118088388006256335691853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192078725592004170890461235 288118088388006256335691853)
    ·
      refine ⟨108044283145502346125884445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288118088388006256335691853 108044283145502346125884445)
      ·
        refine ⟨40516606179563379797206667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108044283145502346125884445 40516606179563379797206667)
        ·
          refine ⟨60774909269345069695810001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40516606179563379797206667 60774909269345069695810001)
          ·
            refine ⟨45581181952008802271857501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60774909269345069695810001 45581181952008802271857501)
            ·
              refine ⟨17092943232003300851946563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45581181952008802271857501 17092943232003300851946563)
              ·
                refine ⟨25639414848004951277919845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17092943232003300851946563 25639414848004951277919845)
                ·
                  refine ⟨4807390284000928364609971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25639414848004951277919845 4807390284000928364609971)
                  ·
                    refine ⟨7211085426001392546914957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4807390284000928364609971 7211085426001392546914957)
                    ·
                      refine ⟨2704157034750522205093109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7211085426001392546914957 2704157034750522205093109)
                      ·
                        rfl

theorem cell23_5266327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_5266327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266327 prefixEnd_5266327 := by exact prefixLift 5266327
  have htrace : WordTrace (prefixWord ++ tailWord_5266327) baseStart_5266327 baseEnd_5266327 := by
    simpa [prefixWord, tailWord_5266327, baseEnd_5266327] using wordTrace_append hprefix tailTrace_5266327
  have hstable : (prefixWord ++ tailWord_5266327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266327).length < 2 ^ (prefixWord ++ tailWord_5266327).sum := by decide
  have hdescent : baseEnd_5266327 < baseStart_5266327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266363 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 6]
def baseStart_5266363 : Nat := 118140960795 + 5266363 * 2 ^ 59
def prefixEnd_5266363 : Nat := 4983230072969 + 3 ^ 40 * 5266363 * 2
def baseEnd_5266363 : Nat := 2704175520054084064242943

theorem tailTrace_5266363 : CollatzResearch.WordTrace tailWord_5266363 prefixEnd_5266363 2704175520054084064242943 := by
  unfold tailWord_5266363
  simp only [CollatzResearch.WordTrace]
  refine ⟨192080038619873749038771743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128053359079915832692514495 192080038619873749038771743)
  ·
    refine ⟨288120057929810623558157615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192080038619873749038771743 288120057929810623558157615)
    ·
      refine ⟨432180086894715935337236423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288120057929810623558157615 432180086894715935337236423)
      ·
        refine ⟨648270130342073903005854635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432180086894715935337236423 648270130342073903005854635)
        ·
          refine ⟨972405195513110854508781953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648270130342073903005854635 972405195513110854508781953)
          ·
            refine ⟨729303896634833140881586465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972405195513110854508781953 729303896634833140881586465)
            ·
              refine ⟨546977922476124855661189849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729303896634833140881586465 546977922476124855661189849)
              ·
                refine ⟨410233441857093641745892387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546977922476124855661189849 410233441857093641745892387)
                ·
                  refine ⟨615350162785640462618838581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410233441857093641745892387 615350162785640462618838581)
                  ·
                    refine ⟨57689077761153793370516117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 615350162785640462618838581 57689077761153793370516117)
                    ·
                      refine ⟨2704175520054084064242943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57689077761153793370516117 2704175520054084064242943)
                      ·
                        rfl

theorem cell23_5266363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_5266363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266363 prefixEnd_5266363 := by exact prefixLift 5266363
  have htrace : WordTrace (prefixWord ++ tailWord_5266363) baseStart_5266363 baseEnd_5266363 := by
    simpa [prefixWord, tailWord_5266363, baseEnd_5266363] using wordTrace_append hprefix tailTrace_5266363
  have hstable : (prefixWord ++ tailWord_5266363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266363).length < 2 ^ (prefixWord ++ tailWord_5266363).sum := by decide
  have hdescent : baseEnd_5266363 < baseStart_5266363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266384 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 2, 2, 2]
def baseStart_5266384 : Nat := 118140960795 + 5266384 * 2 ^ 59
def prefixEnd_5266384 : Nat := 4983230072969 + 3 ^ 40 * 5266384 * 2
def baseEnd_5266384 : Nat := 2704186303147828482080347

theorem tailTrace_5266384 : CollatzResearch.WordTrace tailWord_5266384 prefixEnd_5266384 2704186303147828482080347 := by
  unfold tailWord_5266384
  simp only [CollatzResearch.WordTrace]
  refine ⟨96040402276398834812643103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128053869701865113083524137 96040402276398834812643103)
  ·
    refine ⟨144060603414598252218964655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96040402276398834812643103 144060603414598252218964655)
    ·
      refine ⟨216090905121897378328446983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144060603414598252218964655 216090905121897378328446983)
      ·
        refine ⟨324136357682846067492670475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216090905121897378328446983 324136357682846067492670475)
        ·
          refine ⟨486204536524269101239005713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324136357682846067492670475 486204536524269101239005713)
          ·
            refine ⟨364653402393201825929254285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486204536524269101239005713 364653402393201825929254285)
            ·
              refine ⟨136745025897450684723470357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364653402393201825929254285 136745025897450684723470357)
              ·
                refine ⟨6409923088943000846412673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136745025897450684723470357 6409923088943000846412673)
                ·
                  refine ⟨4807442316707250634809505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6409923088943000846412673 4807442316707250634809505)
                  ·
                    refine ⟨3605581737530437976107129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4807442316707250634809505 3605581737530437976107129)
                    ·
                      refine ⟨2704186303147828482080347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605581737530437976107129 2704186303147828482080347)
                      ·
                        rfl

theorem cell23_5266384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 2, 2].length) (baseStart_5266384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266384 prefixEnd_5266384 := by exact prefixLift 5266384
  have htrace : WordTrace (prefixWord ++ tailWord_5266384) baseStart_5266384 baseEnd_5266384 := by
    simpa [prefixWord, tailWord_5266384, baseEnd_5266384] using wordTrace_append hprefix tailTrace_5266384
  have hstable : (prefixWord ++ tailWord_5266384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266384).length < 2 ^ (prefixWord ++ tailWord_5266384).sum := by decide
  have hdescent : baseEnd_5266384 < baseStart_5266384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266405 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5266405 : Nat := 118140960795 + 5266405 * 2 ^ 59
def prefixEnd_5266405 : Nat := 4983230072969 + 3 ^ 40 * 5266405 * 2
def baseEnd_5266405 : Nat := 2704197086241572899917751

theorem tailTrace_5266405 : CollatzResearch.WordTrace tailWord_5266405 prefixEnd_5266405 2704197086241572899917751 := by
  unfold tailWord_5266405
  simp only [CollatzResearch.WordTrace]
  refine ⟨192081570485721590211800669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128054380323814393474533779 192081570485721590211800669)
  ·
    refine ⟨72030588932145596329425251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192081570485721590211800669 72030588932145596329425251)
    ·
      refine ⟨108045883398218394494137877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72030588932145596329425251 108045883398218394494137877)
      ·
        refine ⟨5064650784291487241912713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108045883398218394494137877 5064650784291487241912713)
        ·
          refine ⟨3798488088218615431434535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5064650784291487241912713 3798488088218615431434535)
          ·
            refine ⟨5697732132327923147151803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798488088218615431434535 5697732132327923147151803)
            ·
              refine ⟨8546598198491884720727705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697732132327923147151803 8546598198491884720727705)
              ·
                refine ⟨6409948648868913540545779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8546598198491884720727705 6409948648868913540545779)
                ·
                  refine ⟨9614922973303370310818669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409948648868913540545779 9614922973303370310818669)
                  ·
                    refine ⟨3605596114988763866557001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9614922973303370310818669 3605596114988763866557001)
                    ·
                      refine ⟨2704197086241572899917751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605596114988763866557001 2704197086241572899917751)
                      ·
                        rfl

theorem cell23_5266405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5266405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266405 prefixEnd_5266405 := by exact prefixLift 5266405
  have htrace : WordTrace (prefixWord ++ tailWord_5266405) baseStart_5266405 baseEnd_5266405 := by
    simpa [prefixWord, tailWord_5266405, baseEnd_5266405] using wordTrace_append hprefix tailTrace_5266405
  have hstable : (prefixWord ++ tailWord_5266405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266405).length < 2 ^ (prefixWord ++ tailWord_5266405).sum := by decide
  have hdescent : baseEnd_5266405 < baseStart_5266405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266457 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 1, 6, 2]
def baseStart_5266457 : Nat := 118140960795 + 5266457 * 2 ^ 59
def prefixEnd_5266457 : Nat := 4983230072969 + 3 ^ 40 * 5266457 * 2
def baseEnd_5266457 : Nat := 2704223787235606696467511

theorem tailTrace_5266457 : CollatzResearch.WordTrace tailWord_5266457 prefixEnd_5266457 2704223787235606696467511 := by
  unfold tailWord_5266457
  simp only [CollatzResearch.WordTrace]
  refine ⟨192083467081533203092693625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128055644721022135395129083 192083467081533203092693625)
  ·
    refine ⟨144062600311149902319520219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192083467081533203092693625 144062600311149902319520219)
    ·
      refine ⟨216093900466724853479280329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144062600311149902319520219 216093900466724853479280329)
      ·
        refine ⟨162070425350043640109460247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216093900466724853479280329 162070425350043640109460247)
        ·
          refine ⟨243105638025065460164190371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162070425350043640109460247 243105638025065460164190371)
          ·
            refine ⟨364658457037598190246285557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243105638025065460164190371 364658457037598190246285557)
            ·
              refine ⟨34186730347274830335589271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 364658457037598190246285557 34186730347274830335589271)
              ·
                refine ⟨51280095520912245503383907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34186730347274830335589271 51280095520912245503383907)
                ·
                  refine ⟨76920143281368368255075861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51280095520912245503383907 76920143281368368255075861)
                  ·
                    refine ⟨3605631716314142261956681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76920143281368368255075861 3605631716314142261956681)
                    ·
                      refine ⟨2704223787235606696467511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605631716314142261956681 2704223787235606696467511)
                      ·
                        rfl

theorem cell23_5266457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_5266457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266457 prefixEnd_5266457 := by exact prefixLift 5266457
  have htrace : WordTrace (prefixWord ++ tailWord_5266457) baseStart_5266457 baseEnd_5266457 := by
    simpa [prefixWord, tailWord_5266457, baseEnd_5266457] using wordTrace_append hprefix tailTrace_5266457
  have hstable : (prefixWord ++ tailWord_5266457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266457).length < 2 ^ (prefixWord ++ tailWord_5266457).sum := by decide
  have hdescent : baseEnd_5266457 < baseStart_5266457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266467 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 5, 4]
def baseStart_5266467 : Nat := 118140960795 + 5266467 * 2 ^ 59
def prefixEnd_5266467 : Nat := 4983230072969 + 3 ^ 40 * 5266467 * 2
def baseEnd_5266467 : Nat := 901409640680717219114155

theorem tailTrace_5266467 : CollatzResearch.WordTrace tailWord_5266467 prefixEnd_5266467 901409640680717219114155 := by
  unfold tailWord_5266467
  simp only [CollatzResearch.WordTrace]
  refine ⟨192083831811496974800557655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128055887874331316533705103 192083831811496974800557655)
  ·
    refine ⟨288125747717245462200836483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192083831811496974800557655 288125747717245462200836483)
    ·
      refine ⟨432188621575868193301254725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288125747717245462200836483 432188621575868193301254725)
      ·
        refine ⟨81035366545475286243985261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 432188621575868193301254725 81035366545475286243985261)
        ·
          refine ⟨30388262454553232341494473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81035366545475286243985261 30388262454553232341494473)
          ·
            refine ⟨22791196840914924256120855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30388262454553232341494473 22791196840914924256120855)
            ·
              refine ⟨34186795261372386384181283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22791196840914924256120855 34186795261372386384181283)
              ·
                refine ⟨51280192892058579576271925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34186795261372386384181283 51280192892058579576271925)
                ·
                  refine ⟨4807518083630491835275493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51280192892058579576271925 4807518083630491835275493)
                  ·
                    refine ⟨901409640680717219114155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4807518083630491835275493 901409640680717219114155)
                    ·
                      rfl

theorem cell23_5266467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 4].length) (baseStart_5266467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266467 prefixEnd_5266467 := by exact prefixLift 5266467
  have htrace : WordTrace (prefixWord ++ tailWord_5266467) baseStart_5266467 baseEnd_5266467 := by
    simpa [prefixWord, tailWord_5266467, baseEnd_5266467] using wordTrace_append hprefix tailTrace_5266467
  have hstable : (prefixWord ++ tailWord_5266467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266467).length < 2 ^ (prefixWord ++ tailWord_5266467).sum := by decide
  have hdescent : baseEnd_5266467 < baseStart_5266467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266471 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 2, 5]
def baseStart_5266471 : Nat := 118140960795 + 5266471 * 2 ^ 59
def prefixEnd_5266471 : Nat := 4983230072969 + 3 ^ 40 * 5266471 * 2
def baseEnd_5266471 : Nat := 901410325321589880564149

theorem tailTrace_5266471 : CollatzResearch.WordTrace tailWord_5266471 prefixEnd_5266471 901410325321589880564149 := by
  unfold tailWord_5266471
  simp only [CollatzResearch.WordTrace]
  refine ⟨192083977703482483483703267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128055985135654988989135511 192083977703482483483703267)
  ·
    refine ⟨288125966555223725225554901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192083977703482483483703267 288125966555223725225554901)
    ·
      refine ⟨6752952341138056059973943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 288125966555223725225554901 6752952341138056059973943)
      ·
        refine ⟨10129428511707084089960915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6752952341138056059973943 10129428511707084089960915)
        ·
          refine ⟨15194142767560626134941373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10129428511707084089960915 15194142767560626134941373)
          ·
            refine ⟨5697803537835234800603015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15194142767560626134941373 5697803537835234800603015)
            ·
              refine ⟨8546705306752852200904523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697803537835234800603015 8546705306752852200904523)
              ·
                refine ⟨12820057960129278301356785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8546705306752852200904523 12820057960129278301356785)
                ·
                  refine ⟨9615043470096958726017589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12820057960129278301356785 9615043470096958726017589)
                  ·
                    refine ⟨901410325321589880564149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9615043470096958726017589 901410325321589880564149)
                    ·
                      rfl

theorem cell23_5266471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_5266471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266471 prefixEnd_5266471 := by exact prefixLift 5266471
  have htrace : WordTrace (prefixWord ++ tailWord_5266471) baseStart_5266471 baseEnd_5266471 := by
    simpa [prefixWord, tailWord_5266471, baseEnd_5266471] using wordTrace_append hprefix tailTrace_5266471
  have hstable : (prefixWord ++ tailWord_5266471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266471).length < 2 ^ (prefixWord ++ tailWord_5266471).sum := by decide
  have hdescent : baseEnd_5266471 < baseStart_5266471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266474 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_5266474 : Nat := 118140960795 + 5266474 * 2 ^ 59
def prefixEnd_5266474 : Nat := 4983230072969 + 3 ^ 40 * 5266474 * 2
def baseEnd_5266474 : Nat := 2704232516406733129954933

theorem tailTrace_5266474 : CollatzResearch.WordTrace tailWord_5266474 prefixEnd_5266474 2704232516406733129954933 := by
  unfold tailWord_5266474
  simp only [CollatzResearch.WordTrace]
  refine ⟨48021021780617903749015619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128056058081647743330708317 48021021780617903749015619)
  ·
    refine ⟨72031532670926855623523429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48021021780617903749015619 72031532670926855623523429)
    ·
      refine ⟨13505912375798785429410643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72031532670926855623523429 13505912375798785429410643)
      ·
        refine ⟨20258868563698178144115965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13505912375798785429410643 20258868563698178144115965)
        ·
          refine ⟨7597075711386816804043487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20258868563698178144115965 7597075711386816804043487)
          ·
            refine ⟨11395613567080225206065231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7597075711386816804043487 11395613567080225206065231)
            ·
              refine ⟨17093420350620337809097847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11395613567080225206065231 17093420350620337809097847)
              ·
                refine ⟨25640130525930506713646771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17093420350620337809097847 25640130525930506713646771)
                ·
                  refine ⟨38460195788895760070470157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25640130525930506713646771 38460195788895760070470157)
                  ·
                    refine ⟨14422573420835910026426309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38460195788895760070470157 14422573420835910026426309)
                    ·
                      refine ⟨2704232516406733129954933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14422573420835910026426309 2704232516406733129954933)
                      ·
                        rfl

theorem cell23_5266474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_5266474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266474 prefixEnd_5266474 := by exact prefixLift 5266474
  have htrace : WordTrace (prefixWord ++ tailWord_5266474) baseStart_5266474 baseEnd_5266474 := by
    simpa [prefixWord, tailWord_5266474, baseEnd_5266474] using wordTrace_append hprefix tailTrace_5266474
  have hstable : (prefixWord ++ tailWord_5266474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266474).length < 2 ^ (prefixWord ++ tailWord_5266474).sum := by decide
  have hdescent : baseEnd_5266474 < baseStart_5266474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266480 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 8]
def baseStart_5266480 : Nat := 118140960795 + 5266480 * 2 ^ 59
def prefixEnd_5266480 : Nat := 4983230072969 + 3 ^ 40 * 5266480 * 2
def baseEnd_5266480 : Nat := 300470621921184456275545

theorem tailTrace_5266480 : CollatzResearch.WordTrace tailWord_5266480 prefixEnd_5266480 300470621921184456275545 := by
  unfold tailWord_5266480
  simp only [CollatzResearch.WordTrace]
  refine ⟨96042152980224939010390447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128056203973633252013853929 96042152980224939010390447)
  ·
    refine ⟨144063229470337408515585671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96042152980224939010390447 144063229470337408515585671)
    ·
      refine ⟨216094844205506112773378507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144063229470337408515585671 216094844205506112773378507)
      ·
        refine ⟨324142266308259169160067761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216094844205506112773378507 324142266308259169160067761)
        ·
          refine ⟨243106699731194376870050821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324142266308259169160067761 243106699731194376870050821)
          ·
            refine ⟨45582506199598945663134529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243106699731194376870050821 45582506199598945663134529)
            ·
              refine ⟨34186879649699209247350897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45582506199598945663134529 34186879649699209247350897)
              ·
                refine ⟨25640159737274406935513173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34186879649699209247350897 25640159737274406935513173)
                ·
                  refine ⟨300470621921184456275545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25640159737274406935513173 300470621921184456275545)
                  ·
                    rfl

theorem cell23_5266480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 8].length) (baseStart_5266480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266480 prefixEnd_5266480 := by exact prefixLift 5266480
  have htrace : WordTrace (prefixWord ++ tailWord_5266480) baseStart_5266480 baseEnd_5266480 := by
    simpa [prefixWord, tailWord_5266480, baseEnd_5266480] using wordTrace_append hprefix tailTrace_5266480
  have hstable : (prefixWord ++ tailWord_5266480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266480).length < 2 ^ (prefixWord ++ tailWord_5266480).sum := by decide
  have hdescent : baseEnd_5266480 < baseStart_5266480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266567 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_5266567 : Nat := 118140960795 + 5266567 * 2 ^ 59
def prefixEnd_5266567 : Nat := 4983230072969 + 3 ^ 40 * 5266567 * 2
def baseEnd_5266567 : Nat := 2704280270107601266092005

theorem tailTrace_5266567 : CollatzResearch.WordTrace tailWord_5266567 prefixEnd_5266567 2704280270107601266092005 := by
  unfold tailWord_5266567
  simp only [CollatzResearch.WordTrace]
  refine ⟨192087479111134691879197955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128058319407423127919465303 192087479111134691879197955)
  ·
    refine ⟨288131218666702037818796933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192087479111134691879197955 288131218666702037818796933)
    ·
      refine ⟨54024603500006632091024425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288131218666702037818796933 54024603500006632091024425)
      ·
        refine ⟨40518452625004974068268319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54024603500006632091024425 40518452625004974068268319)
        ·
          refine ⟨60777678937507461102402479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40518452625004974068268319 60777678937507461102402479)
          ·
            refine ⟨91166518406261191653603719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60777678937507461102402479 91166518406261191653603719)
            ·
              refine ⟨136749777609391787480405579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91166518406261191653603719 136749777609391787480405579)
              ·
                refine ⟨205124666414087681220608369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136749777609391787480405579 205124666414087681220608369)
                ·
                  refine ⟨153843499810565760915456277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205124666414087681220608369 153843499810565760915456277)
                  ·
                    refine ⟨7211414053620270042912013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 153843499810565760915456277 7211414053620270042912013)
                    ·
                      refine ⟨2704280270107601266092005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7211414053620270042912013 2704280270107601266092005)
                      ·
                        rfl

theorem cell23_5266567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_5266567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266567 prefixEnd_5266567 := by exact prefixLift 5266567
  have htrace : WordTrace (prefixWord ++ tailWord_5266567) baseStart_5266567 baseEnd_5266567 := by
    simpa [prefixWord, tailWord_5266567, baseEnd_5266567] using wordTrace_append hprefix tailTrace_5266567
  have hstable : (prefixWord ++ tailWord_5266567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266567).length < 2 ^ (prefixWord ++ tailWord_5266567).sum := by decide
  have hdescent : baseEnd_5266567 < baseStart_5266567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266617 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 2, 7]
def baseStart_5266617 : Nat := 118140960795 + 5266617 * 2 ^ 59
def prefixEnd_5266617 : Nat := 4983230072969 + 3 ^ 40 * 5266617 * 2
def baseEnd_5266617 : Nat := 901435314713442023488925

theorem tailTrace_5266617 : CollatzResearch.WordTrace tailWord_5266617 prefixEnd_5266617 901435314713442023488925 := by
  unfold tailWord_5266617
  simp only [CollatzResearch.WordTrace]
  refine ⟨192089302760953550418518105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128059535173969033612345403 192089302760953550418518105)
  ·
    refine ⟨144066977070715162813888579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192089302760953550418518105 144066977070715162813888579)
    ·
      refine ⟨216100465606072744220832869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144066977070715162813888579 216100465606072744220832869)
      ·
        refine ⟨40518837301138639541406163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216100465606072744220832869 40518837301138639541406163)
        ·
          refine ⟨60778255951707959312109245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40518837301138639541406163 60778255951707959312109245)
          ·
            refine ⟨22791845981890484742040967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60778255951707959312109245 22791845981890484742040967)
            ·
              refine ⟨34187768972835727113061451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22791845981890484742040967 34187768972835727113061451)
              ·
                refine ⟨51281653459253590669592177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34187768972835727113061451 51281653459253590669592177)
                ·
                  refine ⟨38461240094440193002194133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51281653459253590669592177 38461240094440193002194133)
                  ·
                    refine ⟨901435314713442023488925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38461240094440193002194133 901435314713442023488925)
                    ·
                      rfl

theorem cell23_5266617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_5266617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266617 prefixEnd_5266617 := by exact prefixLift 5266617
  have htrace : WordTrace (prefixWord ++ tailWord_5266617) baseStart_5266617 baseEnd_5266617 := by
    simpa [prefixWord, tailWord_5266617, baseEnd_5266617] using wordTrace_append hprefix tailTrace_5266617
  have hstable : (prefixWord ++ tailWord_5266617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266617).length < 2 ^ (prefixWord ++ tailWord_5266617).sum := by decide
  have hdescent : baseEnd_5266617 < baseStart_5266617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266641 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 1, 3, 2]
def baseStart_5266641 : Nat := 118140960795 + 5266641 * 2 ^ 59
def prefixEnd_5266641 : Nat := 4983230072969 + 3 ^ 40 * 5266641 * 2
def baseEnd_5266641 : Nat := 2704318267676033976566665

theorem tailTrace_5266641 : CollatzResearch.WordTrace tailWord_5266641 prefixEnd_5266641 2704318267676033976566665 := by
  unfold tailWord_5266641
  simp only [CollatzResearch.WordTrace]
  refine ⟨192090178112866602517391777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128060118741911068344927851 192090178112866602517391777)
  ·
    refine ⟨144067633584649951888043833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192090178112866602517391777 144067633584649951888043833)
    ·
      refine ⟨108050725188487463916032875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144067633584649951888043833 108050725188487463916032875)
      ·
        refine ⟨162076087782731195874049313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108050725188487463916032875 162076087782731195874049313)
        ·
          refine ⟨121557065837048396905536985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162076087782731195874049313 121557065837048396905536985)
          ·
            refine ⟨91167799377786297679152739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121557065837048396905536985 91167799377786297679152739)
            ·
              refine ⟨136751699066679446518729109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91167799377786297679152739 136751699066679446518729109)
              ·
                refine ⟨6410235893750599055565427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136751699066679446518729109 6410235893750599055565427)
                ·
                  refine ⟨9615353840625898583348141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6410235893750599055565427 9615353840625898583348141)
                  ·
                    refine ⟨3605757690234711968755553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9615353840625898583348141 3605757690234711968755553)
                    ·
                      refine ⟨2704318267676033976566665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3605757690234711968755553 2704318267676033976566665)
                      ·
                        rfl

theorem cell23_5266641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_5266641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266641 prefixEnd_5266641 := by exact prefixLift 5266641
  have htrace : WordTrace (prefixWord ++ tailWord_5266641) baseStart_5266641 baseEnd_5266641 := by
    simpa [prefixWord, tailWord_5266641, baseEnd_5266641] using wordTrace_append hprefix tailTrace_5266641
  have hstable : (prefixWord ++ tailWord_5266641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266641).length < 2 ^ (prefixWord ++ tailWord_5266641).sum := by decide
  have hdescent : baseEnd_5266641 < baseStart_5266641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266744 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_5266744 : Nat := 118140960795 + 5266744 * 2 ^ 59
def prefixEnd_5266744 : Nat := 4983230072969 + 3 ^ 40 * 5266744 * 2
def baseEnd_5266744 : Nat := 2704371156183447073578691

theorem tailTrace_5266744 : CollatzResearch.WordTrace tailWord_5266744 prefixEnd_5266744 2704371156183447073578691 := by
  unfold tailWord_5266744
  simp only [CollatzResearch.WordTrace]
  refine ⟨96046967415746725554195643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128062623220995634072260857 96046967415746725554195643)
  ·
    refine ⟨144070451123620088331293465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96046967415746725554195643 144070451123620088331293465)
    ·
      refine ⟨108052838342715066248470099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144070451123620088331293465 108052838342715066248470099)
      ·
        refine ⟨162079257514072599372705149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108052838342715066248470099 162079257514072599372705149)
        ·
          refine ⟨60779721567777224764764431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162079257514072599372705149 60779721567777224764764431)
          ·
            refine ⟨91169582351665837147146647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60779721567777224764764431 91169582351665837147146647)
            ·
              refine ⟨136754373527498755720719971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91169582351665837147146647 136754373527498755720719971)
              ·
                refine ⟨205131560291248133581079957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136754373527498755720719971 205131560291248133581079957)
                ·
                  refine ⟨9615541888652256261613123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205131560291248133581079957 9615541888652256261613123)
                  ·
                    refine ⟨14423312832978384392419685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9615541888652256261613123 14423312832978384392419685)
                    ·
                      refine ⟨2704371156183447073578691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14423312832978384392419685 2704371156183447073578691)
                      ·
                        rfl

theorem cell23_5266744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_5266744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266744 prefixEnd_5266744 := by exact prefixLift 5266744
  have htrace : WordTrace (prefixWord ++ tailWord_5266744) baseStart_5266744 baseEnd_5266744 := by
    simpa [prefixWord, tailWord_5266744, baseEnd_5266744] using wordTrace_append hprefix tailTrace_5266744
  have hstable : (prefixWord ++ tailWord_5266744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266744).length < 2 ^ (prefixWord ++ tailWord_5266744).sum := by decide
  have hdescent : baseEnd_5266744 < baseStart_5266744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266747 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 9]
def baseStart_5266747 : Nat := 118140960795 + 5266747 * 2 ^ 59
def prefixEnd_5266747 : Nat := 4983230072969 + 3 ^ 40 * 5266747 * 2
def baseEnd_5266747 : Nat := 2704372696625410561841177

theorem tailTrace_5266747 : CollatzResearch.WordTrace tailWord_5266747 prefixEnd_5266747 2704372696625410561841177 := by
  unfold tailWord_5266747
  simp only [CollatzResearch.WordTrace]
  refine ⟨192094044250482582620750495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128062696166988388413833663 192094044250482582620750495)
  ·
    refine ⟨288141066375723873931125743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192094044250482582620750495 288141066375723873931125743)
    ·
      refine ⟨432211599563585810896688615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288141066375723873931125743 432211599563585810896688615)
      ·
        refine ⟨648317399345378716345032923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432211599563585810896688615 648317399345378716345032923)
        ·
          refine ⟨972476099018068074517549385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648317399345378716345032923 972476099018068074517549385)
          ·
            refine ⟨729357074263551055888162039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972476099018068074517549385 729357074263551055888162039)
            ·
              refine ⟨1094035611395326583832243059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729357074263551055888162039 1094035611395326583832243059)
              ·
                refine ⟨1641053417092989875748364589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094035611395326583832243059 1641053417092989875748364589)
                ·
                  refine ⟨615395031409871203405636721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1641053417092989875748364589 615395031409871203405636721)
                  ·
                    refine ⟨461546273557403402554227541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 615395031409871203405636721 461546273557403402554227541)
                    ·
                      refine ⟨2704372696625410561841177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 461546273557403402554227541 2704372696625410561841177)
                      ·
                        rfl

theorem cell23_5266747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_5266747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266747 prefixEnd_5266747 := by exact prefixLift 5266747
  have htrace : WordTrace (prefixWord ++ tailWord_5266747) baseStart_5266747 baseEnd_5266747 := by
    simpa [prefixWord, tailWord_5266747, baseEnd_5266747] using wordTrace_append hprefix tailTrace_5266747
  have hstable : (prefixWord ++ tailWord_5266747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266747).length < 2 ^ (prefixWord ++ tailWord_5266747).sum := by decide
  have hdescent : baseEnd_5266747 < baseStart_5266747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266845 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_5266845 : Nat := 118140960795 + 5266845 * 2 ^ 59
def prefixEnd_5266845 : Nat := 4983230072969 + 3 ^ 40 * 5266845 * 2
def baseEnd_5266845 : Nat := 2704423017729551178415727

theorem tailTrace_5266845 : CollatzResearch.WordTrace tailWord_5266845 prefixEnd_5266845 2704423017729551178415727 := by
  unfold tailWord_5266845
  simp only [CollatzResearch.WordTrace]
  refine ⟨192097618604127545357817989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128065079069418363571878659 192097618604127545357817989)
  ·
    refine ⟨36018303488273914754590873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192097618604127545357817989 36018303488273914754590873)
    ·
      refine ⟨27013727616205436065943155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36018303488273914754590873 27013727616205436065943155)
      ·
        refine ⟨40520591424308154098914733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27013727616205436065943155 40520591424308154098914733)
        ·
          refine ⟨15195221784115557787093025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40520591424308154098914733 15195221784115557787093025)
          ·
            refine ⟨11396416338086668340319769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15195221784115557787093025 11396416338086668340319769)
            ·
              refine ⟨8547312253565001255239827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11396416338086668340319769 8547312253565001255239827)
              ·
                refine ⟨12820968380347501882859741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8547312253565001255239827 12820968380347501882859741)
                ·
                  refine ⟨4807863142630313206072403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12820968380347501882859741 4807863142630313206072403)
                  ·
                    refine ⟨7211794713945469809108605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4807863142630313206072403 7211794713945469809108605)
                    ·
                      refine ⟨2704423017729551178415727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7211794713945469809108605 2704423017729551178415727)
                      ·
                        rfl

theorem cell23_5266845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_5266845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266845 prefixEnd_5266845 := by exact prefixLift 5266845
  have htrace : WordTrace (prefixWord ++ tailWord_5266845) baseStart_5266845 baseEnd_5266845 := by
    simpa [prefixWord, tailWord_5266845, baseEnd_5266845] using wordTrace_append hprefix tailTrace_5266845
  have hstable : (prefixWord ++ tailWord_5266845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266845).length < 2 ^ (prefixWord ++ tailWord_5266845).sum := by decide
  have hdescent : baseEnd_5266845 < baseStart_5266845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266888 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_5266888 : Nat := 118140960795 + 5266888 * 2 ^ 59
def prefixEnd_5266888 : Nat := 4983230072969 + 3 ^ 40 * 5266888 * 2
def baseEnd_5266888 : Nat := 2704445097397694510178029

theorem tailTrace_5266888 : CollatzResearch.WordTrace tailWord_5266888 prefixEnd_5266888 2704445097397694510178029 := by
  unfold tailWord_5266888
  simp only [CollatzResearch.WordTrace]
  refine ⟨96049593471485881850816659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128066124628647842467755545 96049593471485881850816659)
  ·
    refine ⟨144074390207228822776224989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96049593471485881850816659 144074390207228822776224989)
    ·
      refine ⟨54027896327710808541084371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144074390207228822776224989 54027896327710808541084371)
      ·
        refine ⟨81041844491566212811626557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54027896327710808541084371 81041844491566212811626557)
        ·
          refine ⟨30390691684337329804359959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81041844491566212811626557 30390691684337329804359959)
          ·
            refine ⟨45586037526505994706539939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30390691684337329804359959 45586037526505994706539939)
            ·
              refine ⟨68379056289758992059809909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45586037526505994706539939 68379056289758992059809909)
              ·
                refine ⟨6410536527164905505607179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68379056289758992059809909 6410536527164905505607179)
                ·
                  refine ⟨9615804790747358258410769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6410536527164905505607179 9615804790747358258410769)
                  ·
                    refine ⟨7211853593060518693808077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9615804790747358258410769 7211853593060518693808077)
                    ·
                      refine ⟨2704445097397694510178029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7211853593060518693808077 2704445097397694510178029)
                      ·
                        rfl

theorem cell23_5266888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_5266888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266888 prefixEnd_5266888 := by exact prefixLift 5266888
  have htrace : WordTrace (prefixWord ++ tailWord_5266888) baseStart_5266888 baseEnd_5266888 := by
    simpa [prefixWord, tailWord_5266888, baseEnd_5266888] using wordTrace_append hprefix tailTrace_5266888
  have hstable : (prefixWord ++ tailWord_5266888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266888).length < 2 ^ (prefixWord ++ tailWord_5266888).sum := by decide
  have hdescent : baseEnd_5266888 < baseStart_5266888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266922 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_5266922 : Nat := 118140960795 + 5266922 * 2 ^ 59
def prefixEnd_5266922 : Nat := 4983230072969 + 3 ^ 40 * 5266922 * 2
def baseEnd_5266922 : Nat := 2704462555739947377152873

theorem tailTrace_5266922 : CollatzResearch.WordTrace tailWord_5266922 prefixEnd_5266922 2704462555739947377152873 := by
  unfold tailWord_5266922
  simp only [CollatzResearch.WordTrace]
  refine ⟨48025106756212146877092755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128066951349899058338914013 48025106756212146877092755)
  ·
    refine ⟨72037660134318220315639133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48025106756212146877092755 72037660134318220315639133)
    ·
      refine ⟨27014122550369332618364675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72037660134318220315639133 27014122550369332618364675)
      ·
        refine ⟨40521183825553998927547013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27014122550369332618364675 40521183825553998927547013)
        ·
          refine ⟨7597721967291374798915065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40521183825553998927547013 7597721967291374798915065)
          ·
            refine ⟨5698291475468531099186299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7597721967291374798915065 5698291475468531099186299)
            ·
              refine ⟨8547437213202796648779449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5698291475468531099186299 8547437213202796648779449)
              ·
                refine ⟨6410577909902097486584587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8547437213202796648779449 6410577909902097486584587)
                ·
                  refine ⟨9615866864853146229876881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6410577909902097486584587 9615866864853146229876881)
                  ·
                    refine ⟨7211900148639859672407661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9615866864853146229876881 7211900148639859672407661)
                    ·
                      refine ⟨2704462555739947377152873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7211900148639859672407661 2704462555739947377152873)
                      ·
                        rfl

theorem cell23_5266922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_5266922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266922 prefixEnd_5266922 := by exact prefixLift 5266922
  have htrace : WordTrace (prefixWord ++ tailWord_5266922) baseStart_5266922 baseEnd_5266922 := by
    simpa [prefixWord, tailWord_5266922, baseEnd_5266922] using wordTrace_append hprefix tailTrace_5266922
  have hstable : (prefixWord ++ tailWord_5266922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266922).length < 2 ^ (prefixWord ++ tailWord_5266922).sum := by decide
  have hdescent : baseEnd_5266922 < baseStart_5266922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266961 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_5266961 : Nat := 118140960795 + 5266961 * 2 ^ 59
def prefixEnd_5266961 : Nat := 4983230072969 + 3 ^ 40 * 5266961 * 2
def baseEnd_5266961 : Nat := 2704482581485472724565193

theorem tailTrace_5266961 : CollatzResearch.WordTrace tailWord_5266961 prefixEnd_5266961 2704482581485472724565193 := by
  unfold tailWord_5266961
  simp only [CollatzResearch.WordTrace]
  refine ⟨192101849471707297169040737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128067899647804864779360491 192101849471707297169040737)
  ·
    refine ⟨144076387103780472876780553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192101849471707297169040737 144076387103780472876780553)
    ·
      refine ⟨108057290327835354657585415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144076387103780472876780553 108057290327835354657585415)
      ·
        refine ⟨162085935491753031986378123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108057290327835354657585415 162085935491753031986378123)
        ·
          refine ⟨243128903237629547979567185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162085935491753031986378123 243128903237629547979567185)
          ·
            refine ⟨182346677428222160984675389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243128903237629547979567185 182346677428222160984675389)
            ·
              refine ⟨68380004035583310369253271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182346677428222160984675389 68380004035583310369253271)
              ·
                refine ⟨102570006053374965553879907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68380004035583310369253271 102570006053374965553879907)
                ·
                  refine ⟨153855009080062448330819861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102570006053374965553879907 153855009080062448330819861)
                  ·
                    refine ⟨7211953550627927265507181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 153855009080062448330819861 7211953550627927265507181)
                    ·
                      refine ⟨2704482581485472724565193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7211953550627927265507181 2704482581485472724565193)
                      ·
                        rfl

theorem cell23_5266961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_5266961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266961 prefixEnd_5266961 := by exact prefixLift 5266961
  have htrace : WordTrace (prefixWord ++ tailWord_5266961) baseStart_5266961 baseEnd_5266961 := by
    simpa [prefixWord, tailWord_5266961, baseEnd_5266961] using wordTrace_append hprefix tailTrace_5266961
  have hstable : (prefixWord ++ tailWord_5266961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266961).length < 2 ^ (prefixWord ++ tailWord_5266961).sum := by decide
  have hdescent : baseEnd_5266961 < baseStart_5266961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266968 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 2, 6]
def baseStart_5266968 : Nat := 118140960795 + 5266968 * 2 ^ 59
def prefixEnd_5266968 : Nat := 4983230072969 + 3 ^ 40 * 5266968 * 2
def baseEnd_5266968 : Nat := 901495391950018065725887

theorem tailTrace_5266968 : CollatzResearch.WordTrace tailWord_5266968 prefixEnd_5266968 901495391950018065725887 := by
  unfold tailWord_5266968
  simp only [CollatzResearch.WordTrace]
  refine ⟨96051052391340968682272779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128068069855121291576363705 96051052391340968682272779)
  ·
    refine ⟨144076578587011453023409169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96051052391340968682272779 144076578587011453023409169)
    ·
      refine ⟨108057433940258589767556877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144076578587011453023409169 108057433940258589767556877)
      ·
        refine ⟨40521537727596971162833829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108057433940258589767556877 40521537727596971162833829)
        ·
          refine ⟨7597788323924432093031343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40521537727596971162833829 7597788323924432093031343)
          ·
            refine ⟨11396682485886648139547015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7597788323924432093031343 11396682485886648139547015)
            ·
              refine ⟨17095023728829972209320523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11396682485886648139547015 17095023728829972209320523)
              ·
                refine ⟨25642535593244958313980785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17095023728829972209320523 25642535593244958313980785)
                ·
                  refine ⟨19231901694933718735485589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25642535593244958313980785 19231901694933718735485589)
                  ·
                    refine ⟨901495391950018065725887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19231901694933718735485589 901495391950018065725887)
                    ·
                      rfl

theorem cell23_5266968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_5266968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5266968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5266968 prefixEnd_5266968 := by exact prefixLift 5266968
  have htrace : WordTrace (prefixWord ++ tailWord_5266968) baseStart_5266968 baseEnd_5266968 := by
    simpa [prefixWord, tailWord_5266968, baseEnd_5266968] using wordTrace_append hprefix tailTrace_5266968
  have hstable : (prefixWord ++ tailWord_5266968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266968).length < 2 ^ (prefixWord ++ tailWord_5266968).sum := by decide
  have hdescent : baseEnd_5266968 < baseStart_5266968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267041 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 2, 8]
def baseStart_5267041 : Nat := 118140960795 + 5267041 * 2 ^ 59
def prefixEnd_5267041 : Nat := 4983230072969 + 3 ^ 40 * 5267041 * 2
def baseEnd_5267041 : Nat := 901507886645944137188275

theorem tailTrace_5267041 : CollatzResearch.WordTrace tailWord_5267041 prefixEnd_5267041 901507886645944137188275 := by
  unfold tailWord_5267041
  simp only [CollatzResearch.WordTrace]
  refine ⟨192104767311417470831952977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128069844874278313887968651 192104767311417470831952977)
  ·
    refine ⟨144078575483563103123964733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192104767311417470831952977 144078575483563103123964733)
    ·
      refine ⟨54029465806336163671486775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144078575483563103123964733 54029465806336163671486775)
      ·
        refine ⟨81044198709504245507230163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54029465806336163671486775 81044198709504245507230163)
        ·
          refine ⟨121566298064256368260845245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81044198709504245507230163 121566298064256368260845245)
          ·
            refine ⟨45587361774096138097816967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121566298064256368260845245 45587361774096138097816967)
            ·
              refine ⟨68381042661144207146725451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45587361774096138097816967 68381042661144207146725451)
              ·
                refine ⟨102571563991716310720088177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68381042661144207146725451 102571563991716310720088177)
                ·
                  refine ⟨76928672993787233040066133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102571563991716310720088177 76928672993787233040066133)
                  ·
                    refine ⟨901507886645944137188275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76928672993787233040066133 901507886645944137188275)
                    ·
                      rfl

theorem cell23_5267041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_5267041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267041 prefixEnd_5267041 := by exact prefixLift 5267041
  have htrace : WordTrace (prefixWord ++ tailWord_5267041) baseStart_5267041 baseEnd_5267041 := by
    simpa [prefixWord, tailWord_5267041, baseEnd_5267041] using wordTrace_append hprefix tailTrace_5267041
  have hstable : (prefixWord ++ tailWord_5267041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267041).length < 2 ^ (prefixWord ++ tailWord_5267041).sum := by decide
  have hdescent : baseEnd_5267041 < baseStart_5267041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267102 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_5267102 : Nat := 118140960795 + 5267102 * 2 ^ 59
def prefixEnd_5267102 : Nat := 4983230072969 + 3 ^ 40 * 5267102 * 2
def baseEnd_5267102 : Nat := 2704554982257756672902045

theorem tailTrace_5267102 : CollatzResearch.WordTrace tailWord_5267102 prefixEnd_5267102 2704554982257756672902045 := by
  unfold tailWord_5267102
  simp only [CollatzResearch.WordTrace]
  refine ⟨24013374020524559781240445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128071328109464318833282373 24013374020524559781240445)
  ·
    refine ⟨9005015257696709917965167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24013374020524559781240445 9005015257696709917965167)
    ·
      refine ⟨13507522886545064876947751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9005015257696709917965167 13507522886545064876947751)
      ·
        refine ⟨20261284329817597315421627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13507522886545064876947751 20261284329817597315421627)
        ·
          refine ⟨30391926494726395973132441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20261284329817597315421627 30391926494726395973132441)
          ·
            refine ⟨22793944871044796979849331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30391926494726395973132441 22793944871044796979849331)
            ·
              refine ⟨34190917306567195469773997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22793944871044796979849331 34190917306567195469773997)
              ·
                refine ⟨12821593989962698301165249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34190917306567195469773997 12821593989962698301165249)
                ·
                  refine ⟨9616195492472023725873937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12821593989962698301165249 9616195492472023725873937)
                  ·
                    refine ⟨7212146619354017794405453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9616195492472023725873937 7212146619354017794405453)
                    ·
                      refine ⟨2704554982257756672902045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7212146619354017794405453 2704554982257756672902045)
                      ·
                        rfl

theorem cell23_5267102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_5267102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267102 prefixEnd_5267102 := by exact prefixLift 5267102
  have htrace : WordTrace (prefixWord ++ tailWord_5267102) baseStart_5267102 baseEnd_5267102 := by
    simpa [prefixWord, tailWord_5267102, baseEnd_5267102] using wordTrace_append hprefix tailTrace_5267102
  have hstable : (prefixWord ++ tailWord_5267102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267102).length < 2 ^ (prefixWord ++ tailWord_5267102).sum := by decide
  have hdescent : baseEnd_5267102 < baseStart_5267102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267126 : List Nat := [5, 1, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5267126 : Nat := 118140960795 + 5267126 * 2 ^ 59
def prefixEnd_5267126 : Nat := 4983230072969 + 3 ^ 40 * 5267126 * 2
def baseEnd_5267126 : Nat := 901522435264488193000645

theorem tailTrace_5267126 : CollatzResearch.WordTrace tailWord_5267126 prefixEnd_5267126 901522435264488193000645 := by
  unfold tailWord_5267126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006741719756845646799827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128071911677406353565864821 12006741719756845646799827)
  ·
    refine ⟨18010112579635268470199741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12006741719756845646799827 18010112579635268470199741)
    ·
      refine ⟨6753792217363225676324903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18010112579635268470199741 6753792217363225676324903)
      ·
        refine ⟨10130688326044838514487355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6753792217363225676324903 10130688326044838514487355)
        ·
          refine ⟨15196032489067257771731033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10130688326044838514487355 15196032489067257771731033)
          ·
            refine ⟨11397024366800443328798275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15196032489067257771731033 11397024366800443328798275)
            ·
              refine ⟨17095536550200664993197413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11397024366800443328798275 17095536550200664993197413)
              ·
                refine ⟨3205413103162624686224515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17095536550200664993197413 3205413103162624686224515)
                ·
                  refine ⟨4808119654743937029336773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205413103162624686224515 4808119654743937029336773)
                  ·
                    refine ⟨901522435264488193000645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4808119654743937029336773 901522435264488193000645)
                    ·
                      rfl

theorem cell23_5267126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5267126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267126 prefixEnd_5267126 := by exact prefixLift 5267126
  have htrace : WordTrace (prefixWord ++ tailWord_5267126) baseStart_5267126 baseEnd_5267126 := by
    simpa [prefixWord, tailWord_5267126, baseEnd_5267126] using wordTrace_append hprefix tailTrace_5267126
  have hstable : (prefixWord ++ tailWord_5267126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267126).length < 2 ^ (prefixWord ++ tailWord_5267126).sum := by decide
  have hdescent : baseEnd_5267126 < baseStart_5267126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267149 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_5267149 : Nat := 118140960795 + 5267149 * 2 ^ 59
def prefixEnd_5267149 : Nat := 4983230072969 + 3 ^ 40 * 5267149 * 2
def baseEnd_5267149 : Nat := 2704579115848517989014329

theorem tailTrace_5267149 : CollatzResearch.WordTrace tailWord_5267149 prefixEnd_5267149 2704579115848517989014329 := by
  unfold tailWord_5267149
  simp only [CollatzResearch.WordTrace]
  refine ⟨192108706395026205276884501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128072470930017470184589667 192108706395026205276884501)
  ·
    refine ⟨9005095612266853372353961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 192108706395026205276884501 9005095612266853372353961)
    ·
      refine ⟨6753821709200140029265471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9005095612266853372353961 6753821709200140029265471)
      ·
        refine ⟨10130732563800210043898207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6753821709200140029265471 10130732563800210043898207)
        ·
          refine ⟨15196098845700315065847311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10130732563800210043898207 15196098845700315065847311)
          ·
            refine ⟨22794148268550472598770967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15196098845700315065847311 22794148268550472598770967)
            ·
              refine ⟨34191222402825708898156451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22794148268550472598770967 34191222402825708898156451)
              ·
                refine ⟨51286833604238563347234677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34191222402825708898156451 51286833604238563347234677)
                ·
                  refine ⟨4808140650397365313803251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51286833604238563347234677 4808140650397365313803251)
                  ·
                    refine ⟨7212210975596047970704877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4808140650397365313803251 7212210975596047970704877)
                    ·
                      refine ⟨2704579115848517989014329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7212210975596047970704877 2704579115848517989014329)
                      ·
                        rfl

theorem cell23_5267149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_5267149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267149 prefixEnd_5267149 := by exact prefixLift 5267149
  have htrace : WordTrace (prefixWord ++ tailWord_5267149) baseStart_5267149 baseEnd_5267149 := by
    simpa [prefixWord, tailWord_5267149, baseEnd_5267149] using wordTrace_append hprefix tailTrace_5267149
  have hstable : (prefixWord ++ tailWord_5267149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267149).length < 2 ^ (prefixWord ++ tailWord_5267149).sum := by decide
  have hdescent : baseEnd_5267149 < baseStart_5267149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267169 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 1, 5]
def baseStart_5267169 : Nat := 118140960795 + 5267169 * 2 ^ 59
def prefixEnd_5267169 : Nat := 4983230072969 + 3 ^ 40 * 5267169 * 2
def baseEnd_5267169 : Nat := 901529795153869303588079

theorem tailTrace_5267169 : CollatzResearch.WordTrace tailWord_5267169 prefixEnd_5267169 901529795153869303588079 := by
  unfold tailWord_5267169
  simp only [CollatzResearch.WordTrace]
  refine ⟨192109435854953748692612561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128072957236635832461741707 192109435854953748692612561)
  ·
    refine ⟨144082076891215311519459421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192109435854953748692612561 144082076891215311519459421)
    ·
      refine ⟨54030778834205741819797283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144082076891215311519459421 54030778834205741819797283)
      ·
        refine ⟨81046168251308612729695925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54030778834205741819797283 81046168251308612729695925)
        ·
          refine ⟨7598078273560182443408993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81046168251308612729695925 7598078273560182443408993)
          ·
            refine ⟨5698558705170136832556745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7598078273560182443408993 5698558705170136832556745)
            ·
              refine ⟨4273919028877602624417559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5698558705170136832556745 4273919028877602624417559)
              ·
                refine ⟨6410878543316403936626339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273919028877602624417559 6410878543316403936626339)
                ·
                  refine ⟨9616317814974605904939509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6410878543316403936626339 9616317814974605904939509)
                  ·
                    refine ⟨901529795153869303588079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9616317814974605904939509 901529795153869303588079)
                    ·
                      rfl

theorem cell23_5267169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_5267169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267169 prefixEnd_5267169 := by exact prefixLift 5267169
  have htrace : WordTrace (prefixWord ++ tailWord_5267169) baseStart_5267169 baseEnd_5267169 := by
    simpa [prefixWord, tailWord_5267169, baseEnd_5267169] using wordTrace_append hprefix tailTrace_5267169
  have hstable : (prefixWord ++ tailWord_5267169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267169).length < 2 ^ (prefixWord ++ tailWord_5267169).sum := by decide
  have hdescent : baseEnd_5267169 < baseStart_5267169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267172 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_5267172 : Nat := 118140960795 + 5267172 * 2 ^ 59
def prefixEnd_5267172 : Nat := 4983230072969 + 3 ^ 40 * 5267172 * 2
def baseEnd_5267172 : Nat := 2704590925903571399026723

theorem tailTrace_5267172 : CollatzResearch.WordTrace tailWord_5267172 prefixEnd_5267172 2704590925903571399026723 := by
  unfold tailWord_5267172
  simp only [CollatzResearch.WordTrace]
  refine ⟨96054772636971440102485885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128073030182628586803314513 96054772636971440102485885)
  ·
    refine ⟨36020539738864290038432207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96054772636971440102485885 36020539738864290038432207)
    ·
      refine ⟨54030809608296435057648311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36020539738864290038432207 54030809608296435057648311)
      ·
        refine ⟨81046214412444652586472467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54030809608296435057648311 81046214412444652586472467)
        ·
          refine ⟨121569321618666978879708701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81046214412444652586472467 121569321618666978879708701)
          ·
            refine ⟨45588495607000117079890763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121569321618666978879708701 45588495607000117079890763)
            ·
              refine ⟨68382743410500175619836145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45588495607000117079890763 68382743410500175619836145)
              ·
                refine ⟨51287057557875131714877109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68382743410500175619836145 51287057557875131714877109)
                ·
                  refine ⟨4808161646050793598269729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51287057557875131714877109 4808161646050793598269729)
                  ·
                    refine ⟨3606121234538095198702297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4808161646050793598269729 3606121234538095198702297)
                    ·
                      refine ⟨2704590925903571399026723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606121234538095198702297 2704590925903571399026723)
                      ·
                        rfl

theorem cell23_5267172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_5267172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267172 prefixEnd_5267172 := by exact prefixLift 5267172
  have htrace : WordTrace (prefixWord ++ tailWord_5267172) baseStart_5267172 baseEnd_5267172 := by
    simpa [prefixWord, tailWord_5267172, baseEnd_5267172] using wordTrace_append hprefix tailTrace_5267172
  have hstable : (prefixWord ++ tailWord_5267172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267172).length < 2 ^ (prefixWord ++ tailWord_5267172).sum := by decide
  have hdescent : baseEnd_5267172 < baseStart_5267172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267223 : List Nat := [1, 1, 3, 4, 2, 3, 1, 3, 1, 2, 2]
def baseStart_5267223 : Nat := 118140960795 + 5267223 * 2 ^ 59
def prefixEnd_5267223 : Nat := 4983230072969 + 3 ^ 40 * 5267223 * 2
def baseEnd_5267223 : Nat := 2704617113416950699488989

theorem tailTrace_5267223 : CollatzResearch.WordTrace tailWord_5267223 prefixEnd_5267223 2704617113416950699488989 := by
  unfold tailWord_5267223
  simp only [CollatzResearch.WordTrace]
  refine ⟨192111405396758115915078323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128074270264505410610052215 192111405396758115915078323)
  ·
    refine ⟨288167108095137173872617485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192111405396758115915078323 288167108095137173872617485)
    ·
      refine ⟨108062665535676440202231557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288167108095137173872617485 108062665535676440202231557)
      ·
        refine ⟨20261749787939332537918417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108062665535676440202231557 20261749787939332537918417)
        ·
          refine ⟨15196312340954499403438813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20261749787939332537918417 15196312340954499403438813)
          ·
            refine ⟨5698617127857937276289555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15196312340954499403438813 5698617127857937276289555)
            ·
              refine ⟨8547925691786905914434333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5698617127857937276289555 8547925691786905914434333)
              ·
                refine ⟨3205472134420089717912875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8547925691786905914434333 3205472134420089717912875)
                ·
                  refine ⟨4808208201630134576869313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205472134420089717912875 4808208201630134576869313)
                  ·
                    refine ⟨3606156151222600932651985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4808208201630134576869313 3606156151222600932651985)
                    ·
                      refine ⟨2704617113416950699488989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606156151222600932651985 2704617113416950699488989)
                      ·
                        rfl

theorem cell23_5267223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_5267223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267223 prefixEnd_5267223 := by exact prefixLift 5267223
  have htrace : WordTrace (prefixWord ++ tailWord_5267223) baseStart_5267223 baseEnd_5267223 := by
    simpa [prefixWord, tailWord_5267223, baseEnd_5267223] using wordTrace_append hprefix tailTrace_5267223
  have hstable : (prefixWord ++ tailWord_5267223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267223).length < 2 ^ (prefixWord ++ tailWord_5267223).sum := by decide
  have hdescent : baseEnd_5267223 < baseStart_5267223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267256 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 2, 1, 3]
def baseStart_5267256 : Nat := 118140960795 + 5267256 * 2 ^ 59
def prefixEnd_5267256 : Nat := 4983230072969 + 3 ^ 40 * 5267256 * 2
def baseEnd_5267256 : Nat := 2704634058278549070376337

theorem tailTrace_5267256 : CollatzResearch.WordTrace tailWord_5267256 prefixEnd_5267256 2704634058278549070376337 := by
  unfold tailWord_5267256
  simp only [CollatzResearch.WordTrace]
  refine ⟨96056304502819281275514811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128075072670425708367353081 96056304502819281275514811)
  ·
    refine ⟨144084456754228921913272217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96056304502819281275514811 144084456754228921913272217)
    ·
      refine ⟨108063342565671691434954163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144084456754228921913272217 108063342565671691434954163)
      ·
        refine ⟨162095013848507537152431245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108063342565671691434954163 162095013848507537152431245)
        ·
          refine ⟨60785630193190326432161717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162095013848507537152431245 60785630193190326432161717)
          ·
            refine ⟨5698652830611593103015161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60785630193190326432161717 5698652830611593103015161)
            ·
              refine ⟨4273989622958694827261371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5698652830611593103015161 4273989622958694827261371)
              ·
                refine ⟨6410984434438042240892057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273989622958694827261371 6410984434438042240892057)
                ·
                  refine ⟨4808238325828531680669043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6410984434438042240892057 4808238325828531680669043)
                  ·
                    refine ⟨7212357488742797521003565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4808238325828531680669043 7212357488742797521003565)
                    ·
                      refine ⟨2704634058278549070376337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7212357488742797521003565 2704634058278549070376337)
                      ·
                        rfl

theorem cell23_5267256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_5267256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267256 prefixEnd_5267256 := by exact prefixLift 5267256
  have htrace : WordTrace (prefixWord ++ tailWord_5267256) baseStart_5267256 baseEnd_5267256 := by
    simpa [prefixWord, tailWord_5267256, baseEnd_5267256] using wordTrace_append hprefix tailTrace_5267256
  have hstable : (prefixWord ++ tailWord_5267256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267256).length < 2 ^ (prefixWord ++ tailWord_5267256).sum := by decide
  have hdescent : baseEnd_5267256 < baseStart_5267256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267296 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 2, 2, 2]
def baseStart_5267296 : Nat := 118140960795 + 5267296 * 2 ^ 59
def prefixEnd_5267296 : Nat := 4983230072969 + 3 ^ 40 * 5267296 * 2
def baseEnd_5267296 : Nat := 2704654597504728913876153

theorem tailTrace_5267296 : CollatzResearch.WordTrace tailWord_5267296 prefixEnd_5267296 2704654597504728913876153 := by
  unfold tailWord_5267296
  simp only [CollatzResearch.WordTrace]
  refine ⟨96057033962746824691242871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128076045283662432921657161 96057033962746824691242871)
  ·
    refine ⟨144085550944120237036864307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96057033962746824691242871 144085550944120237036864307)
    ·
      refine ⟨216128326416180355555296461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144085550944120237036864307 216128326416180355555296461)
      ·
        refine ⟨81048122406067633333236173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216128326416180355555296461 81048122406067633333236173)
        ·
          refine ⟨30393045902275362499963565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81048122406067633333236173 30393045902275362499963565)
          ·
            refine ⟨11397392213353260937486337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30393045902275362499963565 11397392213353260937486337)
            ·
              refine ⟨8548044160014945703114753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11397392213353260937486337 8548044160014945703114753)
              ·
                refine ⟨6411033120011209277336065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8548044160014945703114753 6411033120011209277336065)
                ·
                  refine ⟨4808274840008406958002049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6411033120011209277336065 4808274840008406958002049)
                  ·
                    refine ⟨3606206130006305218501537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4808274840008406958002049 3606206130006305218501537)
                    ·
                      refine ⟨2704654597504728913876153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606206130006305218501537 2704654597504728913876153)
                      ·
                        rfl

theorem cell23_5267296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_5267296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267296 prefixEnd_5267296 := by exact prefixLift 5267296
  have htrace : WordTrace (prefixWord ++ tailWord_5267296) baseStart_5267296 baseEnd_5267296 := by
    simpa [prefixWord, tailWord_5267296, baseEnd_5267296] using wordTrace_append hprefix tailTrace_5267296
  have hstable : (prefixWord ++ tailWord_5267296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267296).length < 2 ^ (prefixWord ++ tailWord_5267296).sum := by decide
  have hdescent : baseEnd_5267296 < baseStart_5267296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267332 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_5267332 : Nat := 118140960795 + 5267332 * 2 ^ 59
def prefixEnd_5267332 : Nat := 4983230072969 + 3 ^ 40 * 5267332 * 2
def baseEnd_5267332 : Nat := 901557694269430257675329

theorem tailTrace_5267332 : CollatzResearch.WordTrace tailWord_5267332 prefixEnd_5267332 901557694269430257675329 := by
  unfold tailWord_5267332
  simp only [CollatzResearch.WordTrace]
  refine ⟨96057690476681613765398125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128076920635575485020530833 96057690476681613765398125)
  ·
    refine ⟨36021633928755605162024297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96057690476681613765398125 36021633928755605162024297)
    ·
      refine ⟨27016225446566703871518223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36021633928755605162024297 27016225446566703871518223)
      ·
        refine ⟨40524338169850055807277335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27016225446566703871518223 40524338169850055807277335)
        ·
          refine ⟨60786507254775083710916003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40524338169850055807277335 60786507254775083710916003)
          ·
            refine ⟨91179760882162625566374005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60786507254775083710916003 91179760882162625566374005)
            ·
              refine ⟨8548102582702746146847563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91179760882162625566374005 8548102582702746146847563)
              ·
                refine ⟨12822153874054119220271345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8548102582702746146847563 12822153874054119220271345)
                ·
                  refine ⟨9616615405540589415203509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12822153874054119220271345 9616615405540589415203509)
                  ·
                    refine ⟨901557694269430257675329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9616615405540589415203509 901557694269430257675329)
                    ·
                      rfl

theorem cell23_5267332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_5267332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267332 prefixEnd_5267332 := by exact prefixLift 5267332
  have htrace : WordTrace (prefixWord ++ tailWord_5267332) baseStart_5267332 baseEnd_5267332 := by
    simpa [prefixWord, tailWord_5267332, baseEnd_5267332] using wordTrace_append hprefix tailTrace_5267332
  have hstable : (prefixWord ++ tailWord_5267332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267332).length < 2 ^ (prefixWord ++ tailWord_5267332).sum := by decide
  have hdescent : baseEnd_5267332 < baseStart_5267332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267413 : List Nat := [1, 3, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_5267413 : Nat := 118140960795 + 5267413 * 2 ^ 59
def prefixEnd_5267413 : Nat := 4983230072969 + 3 ^ 40 * 5267413 * 2
def baseEnd_5267413 : Nat := 901571558247101652037705

theorem tailTrace_5267413 : CollatzResearch.WordTrace tailWord_5267413 prefixEnd_5267413 901571558247101652037705 := by
  unfold tailWord_5267413
  simp only [CollatzResearch.WordTrace]
  refine ⟨192118335266069778364494893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128078890177379852242996595 192118335266069778364494893)
  ·
    refine ⟨72044375724776166886685585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192118335266069778364494893 72044375724776166886685585)
    ·
      refine ⟨54033281793582125165014189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72044375724776166886685585 54033281793582125165014189)
      ·
        refine ⟨20262480672593296936880321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54033281793582125165014189 20262480672593296936880321)
        ·
          refine ⟨15196860504444972702660241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20262480672593296936880321 15196860504444972702660241)
          ·
            refine ⟨11397645378333729526995181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15196860504444972702660241 11397645378333729526995181)
            ·
              refine ⟨4274117016875148572623193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11397645378333729526995181 4274117016875148572623193)
              ·
                refine ⟨3205587762656361429467395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4274117016875148572623193 3205587762656361429467395)
                ·
                  refine ⟨4808381643984542144201093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205587762656361429467395 4808381643984542144201093)
                  ·
                    refine ⟨901571558247101652037705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4808381643984542144201093 901571558247101652037705)
                    ·
                      rfl

theorem cell23_5267413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_5267413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267413 prefixEnd_5267413 := by exact prefixLift 5267413
  have htrace : WordTrace (prefixWord ++ tailWord_5267413) baseStart_5267413 baseEnd_5267413 := by
    simpa [prefixWord, tailWord_5267413, baseEnd_5267413] using wordTrace_append hprefix tailTrace_5267413
  have hstable : (prefixWord ++ tailWord_5267413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267413).length < 2 ^ (prefixWord ++ tailWord_5267413).sum := by decide
  have hdescent : baseEnd_5267413 < baseStart_5267413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267426 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 6]
def baseStart_5267426 : Nat := 118140960795 + 5267426 * 2 ^ 59
def prefixEnd_5267426 : Nat := 4983230072969 + 3 ^ 40 * 5267426 * 2
def baseEnd_5267426 : Nat := 300524594443312600583395

theorem tailTrace_5267426 : CollatzResearch.WordTrace tailWord_5267426 prefixEnd_5267426 300524594443312600583395 := by
  unfold tailWord_5267426
  simp only [CollatzResearch.WordTrace]
  refine ⟨48029702353755670396179533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128079206276681787723145421 48029702353755670396179533)
  ·
    refine ⟨18011138382658376398567325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48029702353755670396179533 18011138382658376398567325)
    ·
      refine ⟨6754176893496891149462747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18011138382658376398567325 6754176893496891149462747)
      ·
        refine ⟨10131265340245336724194121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754176893496891149462747 10131265340245336724194121)
        ·
          refine ⟨7598449005184002543145591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10131265340245336724194121 7598449005184002543145591)
          ·
            refine ⟨11397673507776003814718387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7598449005184002543145591 11397673507776003814718387)
            ·
              refine ⟨17096510261664005722077581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11397673507776003814718387 17096510261664005722077581)
              ·
                refine ⟨6411191348124002145779093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17096510261664005722077581 6411191348124002145779093)
                ·
                  refine ⟨300524594443312600583395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6411191348124002145779093 300524594443312600583395)
                  ·
                    rfl

theorem cell23_5267426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_5267426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267426 prefixEnd_5267426 := by exact prefixLift 5267426
  have htrace : WordTrace (prefixWord ++ tailWord_5267426) baseStart_5267426 baseEnd_5267426 := by
    simpa [prefixWord, tailWord_5267426, baseEnd_5267426] using wordTrace_append hprefix tailTrace_5267426
  have hstable : (prefixWord ++ tailWord_5267426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267426).length < 2 ^ (prefixWord ++ tailWord_5267426).sum := by decide
  have hdescent : baseEnd_5267426 < baseStart_5267426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267435 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 5, 6]
def baseStart_5267435 : Nat := 118140960795 + 5267435 * 2 ^ 59
def prefixEnd_5267435 : Nat := 4983230072969 + 3 ^ 40 * 5267435 * 2
def baseEnd_5267435 : Nat := 901575323771901290012671

theorem tailTrace_5267435 : CollatzResearch.WordTrace tailWord_5267435 prefixEnd_5267435 901575323771901290012671 := by
  unfold tailWord_5267435
  simp only [CollatzResearch.WordTrace]
  refine ⟨192119137671990076121795759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128079425114660050747863839 192119137671990076121795759)
  ·
    refine ⟨288178706507985114182693639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192119137671990076121795759 288178706507985114182693639)
    ·
      refine ⟨432268059761977671274040459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288178706507985114182693639 432268059761977671274040459)
      ·
        refine ⟨648402089642966506911060689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432268059761977671274040459 648402089642966506911060689)
        ·
          refine ⟨486301567232224880183295517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648402089642966506911060689 486301567232224880183295517)
          ·
            refine ⟨182363087712084330068735819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 486301567232224880183295517 182363087712084330068735819)
            ·
              refine ⟨273544631568126495103103729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182363087712084330068735819 273544631568126495103103729)
              ·
                refine ⟨205158473676094871327327797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273544631568126495103103729 205158473676094871327327797)
                ·
                  refine ⟨19233606907133894186936981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205158473676094871327327797 19233606907133894186936981)
                  ·
                    refine ⟨901575323771901290012671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19233606907133894186936981 901575323771901290012671)
                    ·
                      rfl

theorem cell23_5267435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 6].length) (baseStart_5267435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267435 prefixEnd_5267435 := by exact prefixLift 5267435
  have htrace : WordTrace (prefixWord ++ tailWord_5267435) baseStart_5267435 baseEnd_5267435 := by
    simpa [prefixWord, tailWord_5267435, baseEnd_5267435] using wordTrace_append hprefix tailTrace_5267435
  have hstable : (prefixWord ++ tailWord_5267435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267435).length < 2 ^ (prefixWord ++ tailWord_5267435).sum := by decide
  have hdescent : baseEnd_5267435 < baseStart_5267435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267452 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_5267452 : Nat := 118140960795 + 5267452 * 2 ^ 59
def prefixEnd_5267452 : Nat := 4983230072969 + 3 ^ 40 * 5267452 * 2
def baseEnd_5267452 : Nat := 901578233495610101175145

theorem tailTrace_5267452 : CollatzResearch.WordTrace tailWord_5267452 prefixEnd_5267452 901578233495610101175145 := by
  unfold tailWord_5267452
  simp only [CollatzResearch.WordTrace]
  refine ⟨96059878856464244012582305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128079838475285658683443073 96059878856464244012582305)
  ·
    refine ⟨72044909142348183009436729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96059878856464244012582305 72044909142348183009436729)
    ·
      refine ⟨54033681856761137257077547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72044909142348183009436729 54033681856761137257077547)
      ·
        refine ⟨81050522785141705885616321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54033681856761137257077547 81050522785141705885616321)
        ·
          refine ⟨60787892088856279414212241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81050522785141705885616321 60787892088856279414212241)
          ·
            refine ⟨45590919066642209560659181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60787892088856279414212241 45590919066642209560659181)
            ·
              refine ⟨17096594649990828585247193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45590919066642209560659181 17096594649990828585247193)
              ·
                refine ⟨12822445987493121438935395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17096594649990828585247193 12822445987493121438935395)
                ·
                  refine ⟨19233668981239682158403093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12822445987493121438935395 19233668981239682158403093)
                  ·
                    refine ⟨901578233495610101175145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19233668981239682158403093 901578233495610101175145)
                    ·
                      rfl

theorem cell23_5267452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_5267452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267452 prefixEnd_5267452 := by exact prefixLift 5267452
  have htrace : WordTrace (prefixWord ++ tailWord_5267452) baseStart_5267452 baseEnd_5267452 := by
    simpa [prefixWord, tailWord_5267452, baseEnd_5267452] using wordTrace_append hprefix tailTrace_5267452
  have hstable : (prefixWord ++ tailWord_5267452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267452).length < 2 ^ (prefixWord ++ tailWord_5267452).sum := by decide
  have hdescent : baseEnd_5267452 < baseStart_5267452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267482 : List Nat := [3, 1, 1, 3, 1, 3, 3, 8]
def baseStart_5267482 : Nat := 118140960795 + 5267482 * 2 ^ 59
def prefixEnd_5267482 : Nat := 4983230072969 + 3 ^ 40 * 5267482 * 2
def baseEnd_5267482 : Nat := 100175929811350562450011

theorem tailTrace_5267482 : CollatzResearch.WordTrace tailWord_5267482 prefixEnd_5267482 100175929811350562450011 := by
  unfold tailWord_5267482
  simp only [CollatzResearch.WordTrace]
  refine ⟨48030212975704950787189175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128080567935213202099171133 48030212975704950787189175)
  ·
    refine ⟨72045319463557426180783763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48030212975704950787189175 72045319463557426180783763)
    ·
      refine ⟨108067979195336139271175645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72045319463557426180783763 108067979195336139271175645)
      ·
        refine ⟨40525492198251052226690867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108067979195336139271175645 40525492198251052226690867)
        ·
          refine ⟨60788238297376578340036301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40525492198251052226690867 60788238297376578340036301)
          ·
            refine ⟨22795589361516216877513613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60788238297376578340036301 22795589361516216877513613)
            ·
              refine ⟨8548346010568581329067605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22795589361516216877513613 8548346010568581329067605)
              ·
                refine ⟨100175929811350562450011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8548346010568581329067605 100175929811350562450011)
                ·
                  rfl

theorem cell23_5267482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 8].length) (baseStart_5267482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267482 prefixEnd_5267482 := by exact prefixLift 5267482
  have htrace : WordTrace (prefixWord ++ tailWord_5267482) baseStart_5267482 baseEnd_5267482 := by
    simpa [prefixWord, tailWord_5267482, baseEnd_5267482] using wordTrace_append hprefix tailTrace_5267482
  have hstable : (prefixWord ++ tailWord_5267482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267482).length < 2 ^ (prefixWord ++ tailWord_5267482).sum := by decide
  have hdescent : baseEnd_5267482 < baseStart_5267482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267509 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_5267509 : Nat := 118140960795 + 5267509 * 2 ^ 59
def prefixEnd_5267509 : Nat := 4983230072969 + 3 ^ 40 * 5267509 * 2
def baseEnd_5267509 : Nat := 2704763968884136580512673

theorem tailTrace_5267509 : CollatzResearch.WordTrace tailWord_5267509 prefixEnd_5267509 2704763968884136580512673 := by
  unfold tailWord_5267509
  simp only [CollatzResearch.WordTrace]
  refine ⟨192121836673721986759989581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128081224449147991173326387 192121836673721986759989581)
  ·
    refine ⟨72045688752645745034996093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192121836673721986759989581 72045688752645745034996093)
    ·
      refine ⟨27017133282242154388123535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72045688752645745034996093 27017133282242154388123535)
      ·
        refine ⟨40525699923363231582185303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27017133282242154388123535 40525699923363231582185303)
        ·
          refine ⟨60788549885044847373277955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40525699923363231582185303 60788549885044847373277955)
          ·
            refine ⟨91182824827567271059916933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60788549885044847373277955 91182824827567271059916933)
            ·
              refine ⟨17096779655168863323734425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91182824827567271059916933 17096779655168863323734425)
              ·
                refine ⟨12822584741376647492800819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17096779655168863323734425 12822584741376647492800819)
                ·
                  refine ⟨19233877112064971239201229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12822584741376647492800819 19233877112064971239201229)
                  ·
                    refine ⟨7212703917024364214700461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19233877112064971239201229 7212703917024364214700461)
                    ·
                      refine ⟨2704763968884136580512673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7212703917024364214700461 2704763968884136580512673)
                      ·
                        rfl

theorem cell23_5267509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_5267509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267509 prefixEnd_5267509 := by exact prefixLift 5267509
  have htrace : WordTrace (prefixWord ++ tailWord_5267509) baseStart_5267509 baseEnd_5267509 := by
    simpa [prefixWord, tailWord_5267509, baseEnd_5267509] using wordTrace_append hprefix tailTrace_5267509
  have hstable : (prefixWord ++ tailWord_5267509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267509).length < 2 ^ (prefixWord ++ tailWord_5267509).sum := by decide
  have hdescent : baseEnd_5267509 < baseStart_5267509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267532 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5267532 : Nat := 118140960795 + 5267532 * 2 ^ 59
def prefixEnd_5267532 : Nat := 4983230072969 + 3 ^ 40 * 5267532 * 2
def baseEnd_5267532 : Nat := 2704775778939189990525067

theorem tailTrace_5267532 : CollatzResearch.WordTrace tailWord_5267532 prefixEnd_5267532 2704775778939189990525067 := by
  unfold tailWord_5267532
  simp only [CollatzResearch.WordTrace]
  refine ⟨96061337776319330844038425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128081783701759107792051233 96061337776319330844038425)
  ·
    refine ⟨72046003332239498133028819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96061337776319330844038425 72046003332239498133028819)
    ·
      refine ⟨108069004998359247199543229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72046003332239498133028819 108069004998359247199543229)
      ·
        refine ⟨40525876874384717699828711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108069004998359247199543229 40525876874384717699828711)
        ·
          refine ⟨60788815311577076549743067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40525876874384717699828711 60788815311577076549743067)
          ·
            refine ⟨91183222967365614824614601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60788815311577076549743067 91183222967365614824614601)
            ·
              refine ⟨68387417225524211118460951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91183222967365614824614601 68387417225524211118460951)
              ·
                refine ⟨102581125838286316677691427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68387417225524211118460951 102581125838286316677691427)
                ·
                  refine ⟨153871688757429475016537141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102581125838286316677691427 153871688757429475016537141)
                  ·
                    refine ⟨14425470821009013282800357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153871688757429475016537141 14425470821009013282800357)
                    ·
                      refine ⟨2704775778939189990525067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14425470821009013282800357 2704775778939189990525067)
                      ·
                        rfl

theorem cell23_5267532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5267532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267532 prefixEnd_5267532 := by exact prefixLift 5267532
  have htrace : WordTrace (prefixWord ++ tailWord_5267532) baseStart_5267532 baseEnd_5267532 := by
    simpa [prefixWord, tailWord_5267532, baseEnd_5267532] using wordTrace_append hprefix tailTrace_5267532
  have hstable : (prefixWord ++ tailWord_5267532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267532).length < 2 ^ (prefixWord ++ tailWord_5267532).sum := by decide
  have hdescent : baseEnd_5267532 < baseStart_5267532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267550 : List Nat := [4, 4, 1, 1, 2, 2, 2, 7]
def baseStart_5267550 : Nat := 118140960795 + 5267550 * 2 ^ 59
def prefixEnd_5267550 : Nat := 4983230072969 + 3 ^ 40 * 5267550 * 2
def baseEnd_5267550 : Nat := 100177223021887811855555

theorem tailTrace_5267550 : CollatzResearch.WordTrace tailWord_5267550 prefixEnd_5267550 100177223021887811855555 := by
  unfold tailWord_5267550
  simp only [CollatzResearch.WordTrace]
  refine ⟨24015416508321681345279013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128082221377715633841488069 24015416508321681345279013)
  ·
    refine ⟨4502890595310315252239815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24015416508321681345279013 4502890595310315252239815)
    ·
      refine ⟨6754335892965472878359723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4502890595310315252239815 6754335892965472878359723)
      ·
        refine ⟨10131503839448209317539585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754335892965472878359723 10131503839448209317539585)
        ·
          refine ⟨7598627879586156988154689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10131503839448209317539585 7598627879586156988154689)
          ·
            refine ⟨5698970909689617741116017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7598627879586156988154689 5698970909689617741116017)
            ·
              refine ⟨4274228182267213305837013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5698970909689617741116017 4274228182267213305837013)
              ·
                refine ⟨100177223021887811855555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4274228182267213305837013 100177223021887811855555)
                ·
                  rfl

theorem cell23_5267550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_5267550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267550 prefixEnd_5267550 := by exact prefixLift 5267550
  have htrace : WordTrace (prefixWord ++ tailWord_5267550) baseStart_5267550 baseEnd_5267550 := by
    simpa [prefixWord, tailWord_5267550, baseEnd_5267550] using wordTrace_append hprefix tailTrace_5267550
  have hstable : (prefixWord ++ tailWord_5267550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267550).length < 2 ^ (prefixWord ++ tailWord_5267550).sum := by decide
  have hdescent : baseEnd_5267550 < baseStart_5267550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267566 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_5267566 : Nat := 118140960795 + 5267566 * 2 ^ 59
def prefixEnd_5267566 : Nat := 4983230072969 + 3 ^ 40 * 5267566 * 2
def baseEnd_5267566 : Nat := 2704793237281442857499911

theorem tailTrace_5267566 : CollatzResearch.WordTrace tailWord_5267566 prefixEnd_5267566 2704793237281442857499911 := by
  unfold tailWord_5267566
  simp only [CollatzResearch.WordTrace]
  refine ⟨24015489454314435686851819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128082610423010323663209701 24015489454314435686851819)
  ·
    refine ⟨36023234181471653530277729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24015489454314435686851819 36023234181471653530277729)
    ·
      refine ⟨27017425636103740147708297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36023234181471653530277729 27017425636103740147708297)
      ·
        refine ⟨20263069227077805110781223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27017425636103740147708297 20263069227077805110781223)
        ·
          refine ⟨30394603840616707666171835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20263069227077805110781223 30394603840616707666171835)
          ·
            refine ⟨45591905760925061499257753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30394603840616707666171835 45591905760925061499257753)
            ·
              refine ⟨34193929320693796124443315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45591905760925061499257753 34193929320693796124443315)
              ·
                refine ⟨51290893981040694186664973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34193929320693796124443315 51290893981040694186664973)
                ·
                  refine ⟨19234085242890260319999365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51290893981040694186664973 19234085242890260319999365)
                  ·
                    refine ⟨3606390983041923809999881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19234085242890260319999365 3606390983041923809999881)
                    ·
                      refine ⟨2704793237281442857499911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606390983041923809999881 2704793237281442857499911)
                      ·
                        rfl

theorem cell23_5267566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_5267566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267566 prefixEnd_5267566 := by exact prefixLift 5267566
  have htrace : WordTrace (prefixWord ++ tailWord_5267566) baseStart_5267566 baseEnd_5267566 := by
    simpa [prefixWord, tailWord_5267566, baseEnd_5267566] using wordTrace_append hprefix tailTrace_5267566
  have hstable : (prefixWord ++ tailWord_5267566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267566).length < 2 ^ (prefixWord ++ tailWord_5267566).sum := by decide
  have hdescent : baseEnd_5267566 < baseStart_5267566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267589 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 7]
def baseStart_5267589 : Nat := 118140960795 + 5267589 * 2 ^ 59
def prefixEnd_5267589 : Nat := 4983230072969 + 3 ^ 40 * 5267589 * 2
def baseEnd_5267589 : Nat := 300533894148499585279145

theorem tailTrace_5267589 : CollatzResearch.WordTrace tailWord_5267589 prefixEnd_5267589 300533894148499585279145 := by
  unfold tailWord_5267589
  simp only [CollatzResearch.WordTrace]
  refine ⟨192124754513432160422901821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128083169675621440281934547 192124754513432160422901821)
  ·
    refine ⟨72046782942537060158588183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192124754513432160422901821 72046782942537060158588183)
    ·
      refine ⟨108070174413805590237882275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72046782942537060158588183 108070174413805590237882275)
      ·
        refine ⟨162105261620708385356823413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108070174413805590237882275 162105261620708385356823413)
        ·
          refine ⟨15197368276941411127202195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162105261620708385356823413 15197368276941411127202195)
          ·
            refine ⟨22796052415412116690803293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15197368276941411127202195 22796052415412116690803293)
            ·
              refine ⟨8548519655779543759051235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22796052415412116690803293 8548519655779543759051235)
              ·
                refine ⟨12822779483669315638576853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8548519655779543759051235 12822779483669315638576853)
                ·
                  refine ⟨300533894148499585279145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12822779483669315638576853 300533894148499585279145)
                  ·
                    rfl

theorem cell23_5267589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_5267589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267589 prefixEnd_5267589 := by exact prefixLift 5267589
  have htrace : WordTrace (prefixWord ++ tailWord_5267589) baseStart_5267589 baseEnd_5267589 := by
    simpa [prefixWord, tailWord_5267589, baseEnd_5267589] using wordTrace_append hprefix tailTrace_5267589
  have hstable : (prefixWord ++ tailWord_5267589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267589).length < 2 ^ (prefixWord ++ tailWord_5267589).sum := by decide
  have hdescent : baseEnd_5267589 < baseStart_5267589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267604 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5267604 : Nat := 118140960795 + 5267604 * 2 ^ 59
def prefixEnd_5267604 : Nat := 4983230072969 + 3 ^ 40 * 5267604 * 2
def baseEnd_5267604 : Nat := 2704812749546313708824737

theorem tailTrace_5267604 : CollatzResearch.WordTrace tailWord_5267604 prefixEnd_5267604 2704812749546313708824737 := by
  unfold tailWord_5267604
  simp only [CollatzResearch.WordTrace]
  refine ⟨96062650804188908992348933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128083534405585211989798577 96062650804188908992348933)
  ·
    refine ⟨18011747025785420436065425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96062650804188908992348933 18011747025785420436065425)
    ·
      refine ⟨13508810269339065327049069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18011747025785420436065425 13508810269339065327049069)
      ·
        refine ⟨5065803851002149497643401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13508810269339065327049069 5065803851002149497643401)
        ·
          refine ⟨3799352888251612123232551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5065803851002149497643401 3799352888251612123232551)
          ·
            refine ⟨5699029332377418184848827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799352888251612123232551 5699029332377418184848827)
            ·
              refine ⟨8548543998566127277273241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699029332377418184848827 8548543998566127277273241)
              ·
                refine ⟨6411407998924595457954931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8548543998566127277273241 6411407998924595457954931)
                ·
                  refine ⟨9617111998386893186932397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6411407998924595457954931 9617111998386893186932397)
                  ·
                    refine ⟨3606416999395084945099649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9617111998386893186932397 3606416999395084945099649)
                    ·
                      refine ⟨2704812749546313708824737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606416999395084945099649 2704812749546313708824737)
                      ·
                        rfl

theorem cell23_5267604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5267604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267604 prefixEnd_5267604 := by exact prefixLift 5267604
  have htrace : WordTrace (prefixWord ++ tailWord_5267604) baseStart_5267604 baseEnd_5267604 := by
    simpa [prefixWord, tailWord_5267604, baseEnd_5267604] using wordTrace_append hprefix tailTrace_5267604
  have hstable : (prefixWord ++ tailWord_5267604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267604).length < 2 ^ (prefixWord ++ tailWord_5267604).sum := by decide
  have hdescent : baseEnd_5267604 < baseStart_5267604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267650 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_5267650 : Nat := 118140960795 + 5267650 * 2 ^ 59
def prefixEnd_5267650 : Nat := 4983230072969 + 3 ^ 40 * 5267650 * 2
def baseEnd_5267650 : Nat := 2704836369656420528849525

theorem tailTrace_5267650 : CollatzResearch.WordTrace tailWord_5267650 prefixEnd_5267650 2704836369656420528849525 := by
  unfold tailWord_5267650
  simp only [CollatzResearch.WordTrace]
  refine ⟨48031744841552791960218101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128084652910807445227248269 48031744841552791960218101)
  ·
    refine ⟨4502976078895574246270447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48031744841552791960218101 4502976078895574246270447)
    ·
      refine ⟨6754464118343361369405671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4502976078895574246270447 6754464118343361369405671)
      ·
        refine ⟨10131696177515042054108507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754464118343361369405671 10131696177515042054108507)
        ·
          refine ⟨15197544266272563081162761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10131696177515042054108507 15197544266272563081162761)
          ·
            refine ⟨11398158199704422310872071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15197544266272563081162761 11398158199704422310872071)
            ·
              refine ⟨17097237299556633466308107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11398158199704422310872071 17097237299556633466308107)
              ·
                refine ⟨25645855949334950199462161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17097237299556633466308107 25645855949334950199462161)
                ·
                  refine ⟨19234391962001212649596621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25645855949334950199462161 19234391962001212649596621)
                  ·
                    refine ⟨7212896985750454743598733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19234391962001212649596621 7212896985750454743598733)
                    ·
                      refine ⟨2704836369656420528849525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7212896985750454743598733 2704836369656420528849525)
                      ·
                        rfl

theorem cell23_5267650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_5267650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267650 prefixEnd_5267650 := by exact prefixLift 5267650
  have htrace : WordTrace (prefixWord ++ tailWord_5267650) baseStart_5267650 baseEnd_5267650 := by
    simpa [prefixWord, tailWord_5267650, baseEnd_5267650] using wordTrace_append hprefix tailTrace_5267650
  have hstable : (prefixWord ++ tailWord_5267650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267650).length < 2 ^ (prefixWord ++ tailWord_5267650).sum := by decide
  have hdescent : baseEnd_5267650 < baseStart_5267650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267659 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 3]
def baseStart_5267659 : Nat := 118140960795 + 5267659 * 2 ^ 59
def prefixEnd_5267659 : Nat := 4983230072969 + 3 ^ 40 * 5267659 * 2
def baseEnd_5267659 : Nat := 2704840990982310993636983

theorem tailTrace_5267659 : CollatzResearch.WordTrace tailWord_5267659 prefixEnd_5267659 2704840990982310993636983 := by
  unfold tailWord_5267659
  simp only [CollatzResearch.WordTrace]
  refine ⟨192127307623178562377950031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128084871748785708251966687 192127307623178562377950031)
  ·
    refine ⟨288190961434767843566925047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192127307623178562377950031 288190961434767843566925047)
    ·
      refine ⟨432286442152151765350387571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288190961434767843566925047 432286442152151765350387571)
      ·
        refine ⟨648429663228227648025581357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432286442152151765350387571 648429663228227648025581357)
        ·
          refine ⟨243161123710585368009593009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 648429663228227648025581357 243161123710585368009593009)
          ·
            refine ⟨182370842782939026007194757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243161123710585368009593009 182370842782939026007194757)
            ·
              refine ⟨34194533021801067376349017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182370842782939026007194757 34194533021801067376349017)
              ·
                refine ⟨25645899766350800532261763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34194533021801067376349017 25645899766350800532261763)
                ·
                  refine ⟨38468849649526200798392645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25645899766350800532261763 38468849649526200798392645)
                  ·
                    refine ⟨7212909309286162649698621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38468849649526200798392645 7212909309286162649698621)
                    ·
                      refine ⟨2704840990982310993636983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7212909309286162649698621 2704840990982310993636983)
                      ·
                        rfl

theorem cell23_5267659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 3].length) (baseStart_5267659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267659 prefixEnd_5267659 := by exact prefixLift 5267659
  have htrace : WordTrace (prefixWord ++ tailWord_5267659) baseStart_5267659 baseEnd_5267659 := by
    simpa [prefixWord, tailWord_5267659, baseEnd_5267659] using wordTrace_append hprefix tailTrace_5267659
  have hstable : (prefixWord ++ tailWord_5267659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267659).length < 2 ^ (prefixWord ++ tailWord_5267659).sum := by decide
  have hdescent : baseEnd_5267659 < baseStart_5267659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267666 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_5267666 : Nat := 118140960795 + 5267666 * 2 ^ 59
def prefixEnd_5267666 : Nat := 4983230072969 + 3 ^ 40 * 5267666 * 2
def baseEnd_5267666 : Nat := 901614861782297488749817

theorem tailTrace_5267666 : CollatzResearch.WordTrace tailWord_5267666 prefixEnd_5267666 901614861782297488749817 := by
  unfold tailWord_5267666
  simp only [CollatzResearch.WordTrace]
  refine ⟨48031890733538300643363713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128085041956102135048969901 48031890733538300643363713)
  ·
    refine ⟨36023918050153725482522785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48031890733538300643363713 36023918050153725482522785)
    ·
      refine ⟨27017938537615294111892089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36023918050153725482522785 27017938537615294111892089)
      ·
        refine ⟨20263453903211470583919067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27017938537615294111892089 20263453903211470583919067)
        ·
          refine ⟨30395180854817205875878601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20263453903211470583919067 30395180854817205875878601)
          ·
            refine ⟨22796385641112904406908951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30395180854817205875878601 22796385641112904406908951)
            ·
              refine ⟨34194578461669356610363427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22796385641112904406908951 34194578461669356610363427)
              ·
                refine ⟨51291867692504034915545141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34194578461669356610363427 51291867692504034915545141)
                ·
                  refine ⟨4808612596172253273332357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51291867692504034915545141 4808612596172253273332357)
                  ·
                    refine ⟨901614861782297488749817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4808612596172253273332357 901614861782297488749817)
                    ·
                      rfl

theorem cell23_5267666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_5267666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267666 prefixEnd_5267666 := by exact prefixLift 5267666
  have htrace : WordTrace (prefixWord ++ tailWord_5267666) baseStart_5267666 baseEnd_5267666 := by
    simpa [prefixWord, tailWord_5267666, baseEnd_5267666] using wordTrace_append hprefix tailTrace_5267666
  have hstable : (prefixWord ++ tailWord_5267666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267666).length < 2 ^ (prefixWord ++ tailWord_5267666).sum := by decide
  have hdescent : baseEnd_5267666 < baseStart_5267666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267670 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_5267670 : Nat := 118140960795 + 5267670 * 2 ^ 59
def prefixEnd_5267670 : Nat := 4983230072969 + 3 ^ 40 * 5267670 * 2
def baseEnd_5267670 : Nat := 901615546423170150199811

theorem tailTrace_5267670 : CollatzResearch.WordTrace tailWord_5267670 prefixEnd_5267670 901615546423170150199811 := by
  unfold tailWord_5267670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007981801633669453537529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128085139217425807504400309 12007981801633669453537529)
  ·
    refine ⟨9005986351225252090153147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12007981801633669453537529 9005986351225252090153147)
    ·
      refine ⟨13508979526837878135229721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9005986351225252090153147 13508979526837878135229721)
      ·
        refine ⟨10131734645128408601422291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13508979526837878135229721 10131734645128408601422291)
        ·
          refine ⟨15197601967692612902133437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10131734645128408601422291 15197601967692612902133437)
          ·
            refine ⟨5699100737884729838300039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15197601967692612902133437 5699100737884729838300039)
            ·
              refine ⟨8548651106827094757450059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699100737884729838300039 8548651106827094757450059)
              ·
                refine ⟨12822976660240642136175089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8548651106827094757450059 12822976660240642136175089)
                ·
                  refine ⟨9617232495180481602131317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12822976660240642136175089 9617232495180481602131317)
                  ·
                    refine ⟨901615546423170150199811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9617232495180481602131317 901615546423170150199811)
                    ·
                      rfl

theorem cell23_5267670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_5267670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267670 prefixEnd_5267670 := by exact prefixLift 5267670
  have htrace : WordTrace (prefixWord ++ tailWord_5267670) baseStart_5267670 baseEnd_5267670 := by
    simpa [prefixWord, tailWord_5267670, baseEnd_5267670] using wordTrace_append hprefix tailTrace_5267670
  have hstable : (prefixWord ++ tailWord_5267670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267670).length < 2 ^ (prefixWord ++ tailWord_5267670).sum := by decide
  have hdescent : baseEnd_5267670 < baseStart_5267670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267709 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_5267709 : Nat := 118140960795 + 5267709 * 2 ^ 59
def prefixEnd_5267709 : Nat := 4983230072969 + 3 ^ 40 * 5267709 * 2
def baseEnd_5267709 : Nat := 901622221671678599337251

theorem tailTrace_5267709 : CollatzResearch.WordTrace tailWord_5267709 prefixEnd_5267709 901622221671678599337251 := by
  unfold tailWord_5267709
  simp only [CollatzResearch.WordTrace]
  refine ⟨192129131272997420917270181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128086087515331613944846787 192129131272997420917270181)
  ·
    refine ⟨36024212113687016421988159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192129131272997420917270181 36024212113687016421988159)
    ·
      refine ⟨54036318170530524632982239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36024212113687016421988159 54036318170530524632982239)
      ·
        refine ⟨81054477255795786949473359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54036318170530524632982239 81054477255795786949473359)
        ·
          refine ⟨121581715883693680424210039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81054477255795786949473359 121581715883693680424210039)
          ·
            refine ⟨182372573825540520636315059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121581715883693680424210039 182372573825540520636315059)
            ·
              refine ⟨273558860738310780954472589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182372573825540520636315059 273558860738310780954472589)
              ·
                refine ⟨102584572776866542857927221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273558860738310780954472589 102584572776866542857927221)
                ·
                  refine ⟨9617303697831238392930677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102584572776866542857927221 9617303697831238392930677)
                  ·
                    refine ⟨901622221671678599337251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9617303697831238392930677 901622221671678599337251)
                    ·
                      rfl

theorem cell23_5267709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_5267709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267709 prefixEnd_5267709 := by exact prefixLift 5267709
  have htrace : WordTrace (prefixWord ++ tailWord_5267709) baseStart_5267709 baseEnd_5267709 := by
    simpa [prefixWord, tailWord_5267709, baseEnd_5267709] using wordTrace_append hprefix tailTrace_5267709
  have hstable : (prefixWord ++ tailWord_5267709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267709).length < 2 ^ (prefixWord ++ tailWord_5267709).sum := by decide
  have hdescent : baseEnd_5267709 < baseStart_5267709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267739 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 1, 6]
def baseStart_5267739 : Nat := 118140960795 + 5267739 * 2 ^ 59
def prefixEnd_5267739 : Nat := 4983230072969 + 3 ^ 40 * 5267739 * 2
def baseEnd_5267739 : Nat := 901627356478223560212205

theorem tailTrace_5267739 : CollatzResearch.WordTrace tailWord_5267739 prefixEnd_5267739 901627356478223560212205 := by
  unfold tailWord_5267739
  simp only [CollatzResearch.WordTrace]
  refine ⟨192130225462888736040862271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128086816975259157360574847 192130225462888736040862271)
  ·
    refine ⟨288195338194333104061293407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192130225462888736040862271 288195338194333104061293407)
    ·
      refine ⟨432293007291499656091940111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288195338194333104061293407 432293007291499656091940111)
      ·
        refine ⟨648439510937249484137910167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432293007291499656091940111 648439510937249484137910167)
        ·
          refine ⟨972659266405874226206865251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648439510937249484137910167 972659266405874226206865251)
          ·
            refine ⟨1458988899608811339310297877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972659266405874226206865251 1458988899608811339310297877)
            ·
              refine ⟨68390104669163031530170213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1458988899608811339310297877 68390104669163031530170213)
              ·
                refine ⟨12823144625468068411906915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68390104669163031530170213 12823144625468068411906915)
                ·
                  refine ⟨19234716938202102617860373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12823144625468068411906915 19234716938202102617860373)
                  ·
                    refine ⟨901627356478223560212205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19234716938202102617860373 901627356478223560212205)
                    ·
                      rfl

theorem cell23_5267739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 6].length) (baseStart_5267739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267739 prefixEnd_5267739 := by exact prefixLift 5267739
  have htrace : WordTrace (prefixWord ++ tailWord_5267739) baseStart_5267739 baseEnd_5267739 := by
    simpa [prefixWord, tailWord_5267739, baseEnd_5267739] using wordTrace_append hprefix tailTrace_5267739
  have hstable : (prefixWord ++ tailWord_5267739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267739).length < 2 ^ (prefixWord ++ tailWord_5267739).sum := by decide
  have hdescent : baseEnd_5267739 < baseStart_5267739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267751 : List Nat := [1, 1, 8, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5267751 : Nat := 118140960795 + 5267751 * 2 ^ 59
def prefixEnd_5267751 : Nat := 4983230072969 + 3 ^ 40 * 5267751 * 2
def baseEnd_5267751 : Nat := 901629410400841544562187

theorem tailTrace_5267751 : CollatzResearch.WordTrace tailWord_5267751 prefixEnd_5267751 901629410400841544562187 := by
  unfold tailWord_5267751
  simp only [CollatzResearch.WordTrace]
  refine ⟨192130663138845262090299107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128087108759230174726866071 192130663138845262090299107)
  ·
    refine ⟨288195994708267893135448661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192130663138845262090299107 288195994708267893135448661)
    ·
      refine ⟨3377296812987514372681039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 288195994708267893135448661 3377296812987514372681039)
      ·
        refine ⟨5065945219481271559021559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377296812987514372681039 5065945219481271559021559)
        ·
          refine ⟨7598917829221907338532339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5065945219481271559021559 7598917829221907338532339)
          ·
            refine ⟨11398376743832861007798509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7598917829221907338532339 11398376743832861007798509)
            ·
              refine ⟨4274391278937322877924441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11398376743832861007798509 4274391278937322877924441)
              ·
                refine ⟨3205793459202992158443331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4274391278937322877924441 3205793459202992158443331)
                ·
                  refine ⟨4808690188804488237664997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205793459202992158443331 4808690188804488237664997)
                  ·
                    refine ⟨901629410400841544562187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4808690188804488237664997 901629410400841544562187)
                    ·
                      rfl

theorem cell23_5267751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5267751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267751 prefixEnd_5267751 := by exact prefixLift 5267751
  have htrace : WordTrace (prefixWord ++ tailWord_5267751) baseStart_5267751 baseEnd_5267751 := by
    simpa [prefixWord, tailWord_5267751, baseEnd_5267751] using wordTrace_append hprefix tailTrace_5267751
  have hstable : (prefixWord ++ tailWord_5267751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267751).length < 2 ^ (prefixWord ++ tailWord_5267751).sum := by decide
  have hdescent : baseEnd_5267751 < baseStart_5267751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267756 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_5267756 : Nat := 118140960795 + 5267756 * 2 ^ 59
def prefixEnd_5267756 : Nat := 4983230072969 + 3 ^ 40 * 5267756 * 2
def baseEnd_5267756 : Nat := 901630266201932371374679

theorem tailTrace_5267756 : CollatzResearch.WordTrace tailWord_5267756 prefixEnd_5267756 901630266201932371374679 := by
  unfold tailWord_5267756
  simp only [CollatzResearch.WordTrace]
  refine ⟨96065422751913573972115561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128087230335884765296154081 96065422751913573972115561)
  ·
    refine ⟨72049067063935180479086671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96065422751913573972115561 72049067063935180479086671)
    ·
      refine ⟨108073600595902770718630007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72049067063935180479086671 108073600595902770718630007)
      ·
        refine ⟨162110400893854156077945011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108073600595902770718630007 162110400893854156077945011)
        ·
          refine ⟨243165601340781234116917517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162110400893854156077945011 243165601340781234116917517)
          ·
            refine ⟨91187100502792962793844069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243165601340781234116917517 91187100502792962793844069)
            ·
              refine ⟨17097581344273680523845763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91187100502792962793844069 17097581344273680523845763)
              ·
                refine ⟨25646372016410520785768645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17097581344273680523845763 25646372016410520785768645)
                ·
                  refine ⟨4808694753076972647331621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25646372016410520785768645 4808694753076972647331621)
                  ·
                    refine ⟨901630266201932371374679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4808694753076972647331621 901630266201932371374679)
                    ·
                      rfl

theorem cell23_5267756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_5267756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267756 prefixEnd_5267756 := by exact prefixLift 5267756
  have htrace : WordTrace (prefixWord ++ tailWord_5267756) baseStart_5267756 baseEnd_5267756 := by
    simpa [prefixWord, tailWord_5267756, baseEnd_5267756] using wordTrace_append hprefix tailTrace_5267756
  have hstable : (prefixWord ++ tailWord_5267756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267756).length < 2 ^ (prefixWord ++ tailWord_5267756).sum := by decide
  have hdescent : baseEnd_5267756 < baseStart_5267756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267759 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_5267759 : Nat := 118140960795 + 5267759 * 2 ^ 59
def prefixEnd_5267759 : Nat := 4983230072969 + 3 ^ 40 * 5267759 * 2
def baseEnd_5267759 : Nat := 2704892339047760602386523

theorem tailTrace_5267759 : CollatzResearch.WordTrace tailWord_5267759 prefixEnd_5267759 2704892339047760602386523 := by
  unfold tailWord_5267759
  simp only [CollatzResearch.WordTrace]
  refine ⟨192130954922816279456590331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128087303281877519637726887 192130954922816279456590331)
  ·
    refine ⟨288196432384224419184885497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192130954922816279456590331 288196432384224419184885497)
    ·
      refine ⟨216147324288168314388664123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288196432384224419184885497 216147324288168314388664123)
      ·
        refine ⟨324220986432252471582996185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216147324288168314388664123 324220986432252471582996185)
        ·
          refine ⟨243165739824189353687247139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324220986432252471582996185 243165739824189353687247139)
          ·
            refine ⟨364748609736284030530870709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243165739824189353687247139 364748609736284030530870709)
            ·
              refine ⟨34195182162776627862269129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 364748609736284030530870709 34195182162776627862269129)
              ·
                refine ⟨25646386622082470896701847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34195182162776627862269129 25646386622082470896701847)
                ·
                  refine ⟨38469579933123706345052771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25646386622082470896701847 38469579933123706345052771)
                  ·
                    refine ⟨57704369899685559517579157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38469579933123706345052771 57704369899685559517579157)
                    ·
                      refine ⟨2704892339047760602386523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57704369899685559517579157 2704892339047760602386523)
                      ·
                        rfl

theorem cell23_5267759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_5267759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267759 prefixEnd_5267759 := by exact prefixLift 5267759
  have htrace : WordTrace (prefixWord ++ tailWord_5267759) baseStart_5267759 baseEnd_5267759 := by
    simpa [prefixWord, tailWord_5267759, baseEnd_5267759] using wordTrace_append hprefix tailTrace_5267759
  have hstable : (prefixWord ++ tailWord_5267759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267759).length < 2 ^ (prefixWord ++ tailWord_5267759).sum := by decide
  have hdescent : baseEnd_5267759 < baseStart_5267759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267777 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 1, 5]
def baseStart_5267777 : Nat := 118140960795 + 5267777 * 2 ^ 59
def prefixEnd_5267777 : Nat := 4983230072969 + 3 ^ 40 * 5267777 * 2
def baseEnd_5267777 : Nat := 901633860566513843987147

theorem tailTrace_5267777 : CollatzResearch.WordTrace tailWord_5267777 prefixEnd_5267777 901633860566513843987147 := by
  unfold tailWord_5267777
  simp only [CollatzResearch.WordTrace]
  refine ⟨192131611436751068530745585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128087740957834045687163723 192131611436751068530745585)
  ·
    refine ⟨144098708577563301398059189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192131611436751068530745585 144098708577563301398059189)
    ·
      refine ⟨13509253929146559506068049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144098708577563301398059189 13509253929146559506068049)
      ·
        refine ⟨10131940446859919629551037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13509253929146559506068049 10131940446859919629551037)
        ·
          refine ⟨3799477667572469861081639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10131940446859919629551037 3799477667572469861081639)
          ·
            refine ⟨5699216501358704791622459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799477667572469861081639 5699216501358704791622459)
            ·
              refine ⟨8548824752038057187433689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699216501358704791622459 8548824752038057187433689)
              ·
                refine ⟨6411618564028542890575267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8548824752038057187433689 6411618564028542890575267)
                ·
                  refine ⟨9617427846042814335862901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6411618564028542890575267 9617427846042814335862901)
                  ·
                    refine ⟨901633860566513843987147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9617427846042814335862901 901633860566513843987147)
                    ·
                      rfl

theorem cell23_5267777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_5267777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267777 prefixEnd_5267777 := by exact prefixLift 5267777
  have htrace : WordTrace (prefixWord ++ tailWord_5267777) baseStart_5267777 baseEnd_5267777 := by
    simpa [prefixWord, tailWord_5267777, baseEnd_5267777] using wordTrace_append hprefix tailTrace_5267777
  have hstable : (prefixWord ++ tailWord_5267777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267777).length < 2 ^ (prefixWord ++ tailWord_5267777).sum := by decide
  have hdescent : baseEnd_5267777 < baseStart_5267777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267780 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5267780 : Nat := 118140960795 + 5267780 * 2 ^ 59
def prefixEnd_5267780 : Nat := 4983230072969 + 3 ^ 40 * 5267780 * 2
def baseEnd_5267780 : Nat := 2704903122141505020223927

theorem tailTrace_5267780 : CollatzResearch.WordTrace tailWord_5267780 prefixEnd_5267780 2704903122141505020223927 := by
  unfold tailWord_5267780
  simp only [CollatzResearch.WordTrace]
  refine ⟨96065860427870100021552397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128087813903826800028736529 96065860427870100021552397)
  ·
    refine ⟨36024697660451287508082149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96065860427870100021552397 36024697660451287508082149)
    ·
      refine ⟨6754630811334616407765403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36024697660451287508082149 6754630811334616407765403)
      ·
        refine ⟨10131946217001924611648105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754630811334616407765403 10131946217001924611648105)
        ·
          refine ⟨7598959662751443458736079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10131946217001924611648105 7598959662751443458736079)
          ·
            refine ⟨11398439494127165188104119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7598959662751443458736079 11398439494127165188104119)
            ·
              refine ⟨17097659241190747782156179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11398439494127165188104119 17097659241190747782156179)
              ·
                refine ⟨25646488861786121673234269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17097659241190747782156179 25646488861786121673234269)
                ·
                  refine ⟨9617433323169795627462851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25646488861786121673234269 9617433323169795627462851)
                  ·
                    refine ⟨14426149984754693441194277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9617433323169795627462851 14426149984754693441194277)
                    ·
                      refine ⟨2704903122141505020223927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14426149984754693441194277 2704903122141505020223927)
                      ·
                        rfl

theorem cell23_5267780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5267780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267780 prefixEnd_5267780 := by exact prefixLift 5267780
  have htrace : WordTrace (prefixWord ++ tailWord_5267780) baseStart_5267780 baseEnd_5267780 := by
    simpa [prefixWord, tailWord_5267780, baseEnd_5267780] using wordTrace_append hprefix tailTrace_5267780
  have hstable : (prefixWord ++ tailWord_5267780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267780).length < 2 ^ (prefixWord ++ tailWord_5267780).sum := by decide
  have hdescent : baseEnd_5267780 < baseStart_5267780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267809 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_5267809 : Nat := 118140960795 + 5267809 * 2 ^ 59
def prefixEnd_5267809 : Nat := 4983230072969 + 3 ^ 40 * 5267809 * 2
def baseEnd_5267809 : Nat := 2704918013080485406761293

theorem tailTrace_5267809 : CollatzResearch.WordTrace tailWord_5267809 prefixEnd_5267809 2704918013080485406761293 := by
  unfold tailWord_5267809
  simp only [CollatzResearch.WordTrace]
  refine ⟨192132778572635137995910481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128088519048423425330606987 192132778572635137995910481)
  ·
    refine ⟨144099583929476353496932861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192132778572635137995910481 144099583929476353496932861)
    ·
      refine ⟨54037343973553632561349823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144099583929476353496932861 54037343973553632561349823)
      ·
        refine ⟨81056015960330448842024735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54037343973553632561349823 81056015960330448842024735)
        ·
          refine ⟨121584023940495673263037103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81056015960330448842024735 121584023940495673263037103)
          ·
            refine ⟨182376035910743509894555655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121584023940495673263037103 182376035910743509894555655)
            ·
              refine ⟨273564053866115264841833483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182376035910743509894555655 273564053866115264841833483)
              ·
                refine ⟨410346080799172897262750225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273564053866115264841833483 410346080799172897262750225)
                ·
                  refine ⟨307759560599379672947062669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410346080799172897262750225 307759560599379672947062669)
                  ·
                    refine ⟨115409835224767377355148501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307759560599379672947062669 115409835224767377355148501)
                    ·
                      refine ⟨2704918013080485406761293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115409835224767377355148501 2704918013080485406761293)
                      ·
                        rfl

theorem cell23_5267809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_5267809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267809 prefixEnd_5267809 := by exact prefixLift 5267809
  have htrace : WordTrace (prefixWord ++ tailWord_5267809) baseStart_5267809 baseEnd_5267809 := by
    simpa [prefixWord, tailWord_5267809, baseEnd_5267809] using wordTrace_append hprefix tailTrace_5267809
  have hstable : (prefixWord ++ tailWord_5267809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267809).length < 2 ^ (prefixWord ++ tailWord_5267809).sum := by decide
  have hdescent : baseEnd_5267809 < baseStart_5267809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267816 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 2, 7]
def baseStart_5267816 : Nat := 118140960795 + 5267816 * 2 ^ 59
def prefixEnd_5267816 : Nat := 4983230072969 + 3 ^ 40 * 5267816 * 2
def baseEnd_5267816 : Nat := 901640535815022293124587

theorem tailTrace_5267816 : CollatzResearch.WordTrace tailWord_5267816 prefixEnd_5267816 901640535815022293124587 := by
  unfold tailWord_5267816
  simp only [CollatzResearch.WordTrace]
  refine ⟨96066516941804889095707651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128088689255739852127610201 96066516941804889095707651)
  ·
    refine ⟨144099775412707333643561477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96066516941804889095707651 144099775412707333643561477)
    ·
      refine ⟨27018707889882625058167777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144099775412707333643561477 27018707889882625058167777)
      ·
        refine ⟨20264030917411968793625833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27018707889882625058167777 20264030917411968793625833)
        ·
          refine ⟨15198023188058976595219375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20264030917411968793625833 15198023188058976595219375)
          ·
            refine ⟨22797034782088464892829063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15198023188058976595219375 22797034782088464892829063)
            ·
              refine ⟨34195552173132697339243595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22797034782088464892829063 34195552173132697339243595)
              ·
                refine ⟨51293328259699046008865393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34195552173132697339243595 51293328259699046008865393)
                ·
                  refine ⟨38469996194774284506649045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51293328259699046008865393 38469996194774284506649045)
                  ·
                    refine ⟨901640535815022293124587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38469996194774284506649045 901640535815022293124587)
                    ·
                      rfl

theorem cell23_5267816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_5267816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267816 prefixEnd_5267816 := by exact prefixLift 5267816
  have htrace : WordTrace (prefixWord ++ tailWord_5267816) baseStart_5267816 baseEnd_5267816 := by
    simpa [prefixWord, tailWord_5267816, baseEnd_5267816] using wordTrace_append hprefix tailTrace_5267816
  have hstable : (prefixWord ++ tailWord_5267816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267816).length < 2 ^ (prefixWord ++ tailWord_5267816).sum := by decide
  have hdescent : baseEnd_5267816 < baseStart_5267816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267876 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 7]
def baseStart_5267876 : Nat := 118140960795 + 5267876 * 2 ^ 59
def prefixEnd_5267876 : Nat := 4983230072969 + 3 ^ 40 * 5267876 * 2
def baseEnd_5267876 : Nat := 300550268476037404958165

theorem tailTrace_5267876 : CollatzResearch.WordTrace tailWord_5267876 prefixEnd_5267876 300550268476037404958165 := by
  unfold tailWord_5267876
  simp only [CollatzResearch.WordTrace]
  refine ⟨96067611131696204219299741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128090148175594938959066321 96067611131696204219299741)
  ·
    refine ⟨36025354174386076582237403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96067611131696204219299741 36025354174386076582237403)
    ·
      refine ⟨54038031261579114873356105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36025354174386076582237403 54038031261579114873356105)
      ·
        refine ⟨40528523446184336155017079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54038031261579114873356105 40528523446184336155017079)
        ·
          refine ⟨60792785169276504232525619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40528523446184336155017079 60792785169276504232525619)
          ·
            refine ⟨91189177753914756348788429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60792785169276504232525619 91189177753914756348788429)
            ·
              refine ⟨34195941657718033630795661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91189177753914756348788429 34195941657718033630795661)
              ·
                refine ⟨12823478121644262611548373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34195941657718033630795661 12823478121644262611548373)
                ·
                  refine ⟨300550268476037404958165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12823478121644262611548373 300550268476037404958165)
                  ·
                    rfl

theorem cell23_5267876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_5267876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267876 prefixEnd_5267876 := by exact prefixLift 5267876
  have htrace : WordTrace (prefixWord ++ tailWord_5267876) baseStart_5267876 baseEnd_5267876 := by
    simpa [prefixWord, tailWord_5267876, baseEnd_5267876] using wordTrace_append hprefix tailTrace_5267876
  have hstable : (prefixWord ++ tailWord_5267876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267876).length < 2 ^ (prefixWord ++ tailWord_5267876).sum := by decide
  have hdescent : baseEnd_5267876 < baseStart_5267876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267933 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_5267933 : Nat := 118140960795 + 5267933 * 2 ^ 59
def prefixEnd_5267933 : Nat := 4983230072969 + 3 ^ 40 * 5267933 * 2
def baseEnd_5267933 : Nat := 2704981684681642921610723

theorem tailTrace_5267933 : CollatzResearch.WordTrace tailWord_5267933 prefixEnd_5267933 2704981684681642921610723 := by
  unfold tailWord_5267933
  simp only [CollatzResearch.WordTrace]
  refine ⟨192137301224185907173424453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128091534149457271448949635 192137301224185907173424453)
  ·
    refine ⟨36025743979534857595017085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192137301224185907173424453 36025743979534857595017085)
    ·
      refine ⟨13509653992325571598131407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36025743979534857595017085 13509653992325571598131407)
      ·
        refine ⟨20264480988488357397197111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13509653992325571598131407 20264480988488357397197111)
        ·
          refine ⟨30396721482732536095795667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20264480988488357397197111 30396721482732536095795667)
          ·
            refine ⟨45595082224098804143693501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30396721482732536095795667 45595082224098804143693501)
            ·
              refine ⟨17098155834037051553885063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45595082224098804143693501 17098155834037051553885063)
              ·
                refine ⟨25647233751055577330827595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17098155834037051553885063 25647233751055577330827595)
                ·
                  refine ⟨38470850626583365996241393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25647233751055577330827595 38470850626583365996241393)
                  ·
                    refine ⟨28853137969937524497181045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38470850626583365996241393 28853137969937524497181045)
                    ·
                      refine ⟨2704981684681642921610723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28853137969937524497181045 2704981684681642921610723)
                      ·
                        rfl

theorem cell23_5267933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_5267933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267933 prefixEnd_5267933 := by exact prefixLift 5267933
  have htrace : WordTrace (prefixWord ++ tailWord_5267933) baseStart_5267933 baseEnd_5267933 := by
    simpa [prefixWord, tailWord_5267933, baseEnd_5267933] using wordTrace_append hprefix tailTrace_5267933
  have hstable : (prefixWord ++ tailWord_5267933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267933).length < 2 ^ (prefixWord ++ tailWord_5267933).sum := by decide
  have hdescent : baseEnd_5267933 < baseStart_5267933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267943 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5267943 : Nat := 118140960795 + 5267943 * 2 ^ 59
def prefixEnd_5267943 : Nat := 4983230072969 + 3 ^ 40 * 5267943 * 2
def baseEnd_5267943 : Nat := 2704986819488187882485677

theorem tailTrace_5267943 : CollatzResearch.WordTrace tailWord_5267943 prefixEnd_5267943 2704986819488187882485677 := by
  unfold tailWord_5267943
  simp only [CollatzResearch.WordTrace]
  refine ⟨192137665954149678881288483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128091777302766452587525655 192137665954149678881288483)
  ·
    refine ⟨288206498931224518321932725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192137665954149678881288483 288206498931224518321932725)
    ·
      refine ⟨27019359274802298592681193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288206498931224518321932725 27019359274802298592681193)
      ·
        refine ⟨20264519456101723944510895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27019359274802298592681193 20264519456101723944510895)
        ·
          refine ⟨30396779184152585916766343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20264519456101723944510895 30396779184152585916766343)
          ·
            refine ⟨45595168776228878875149515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30396779184152585916766343 45595168776228878875149515)
            ·
              refine ⟨68392753164343318312724273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45595168776228878875149515 68392753164343318312724273)
              ·
                refine ⟨51294564873257488734543205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68392753164343318312724273 51294564873257488734543205)
                ·
                  refine ⟨9617730913735779137726851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51294564873257488734543205 9617730913735779137726851)
                  ·
                    refine ⟨14426596370603668706590277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9617730913735779137726851 14426596370603668706590277)
                    ·
                      refine ⟨2704986819488187882485677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14426596370603668706590277 2704986819488187882485677)
                      ·
                        rfl

theorem cell23_5267943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5267943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267943 prefixEnd_5267943 := by exact prefixLift 5267943
  have htrace : WordTrace (prefixWord ++ tailWord_5267943) baseStart_5267943 baseEnd_5267943 := by
    simpa [prefixWord, tailWord_5267943, baseEnd_5267943] using wordTrace_append hprefix tailTrace_5267943
  have hstable : (prefixWord ++ tailWord_5267943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267943).length < 2 ^ (prefixWord ++ tailWord_5267943).sum := by decide
  have hdescent : baseEnd_5267943 < baseStart_5267943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267953 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 5, 4]
def baseStart_5267953 : Nat := 118140960795 + 5267953 * 2 ^ 59
def prefixEnd_5267953 : Nat := 4983230072969 + 3 ^ 40 * 5267953 * 2
def baseEnd_5267953 : Nat := 901663984764910947786877

theorem tailTrace_5267953 : CollatzResearch.WordTrace tailWord_5267953 prefixEnd_5267953 901663984764910947786877 := by
  unfold tailWord_5267953
  simp only [CollatzResearch.WordTrace]
  refine ⟨192138030684113450589152513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128092020456075633726101675 192138030684113450589152513)
  ·
    refine ⟨144103523013085087941864385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192138030684113450589152513 144103523013085087941864385)
    ·
      refine ⟨108077642259813815956398289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144103523013085087941864385 108077642259813815956398289)
      ·
        refine ⟨81058231694860361967298717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108077642259813815956398289 81058231694860361967298717)
        ·
          refine ⟨30396836885572635737737019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81058231694860361967298717 30396836885572635737737019)
          ·
            refine ⟨45595255328358953606605529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30396836885572635737737019 45595255328358953606605529)
            ·
              refine ⟨34196441496269215204954147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45595255328358953606605529 34196441496269215204954147)
              ·
                refine ⟨51294662244403822807431221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34196441496269215204954147 51294662244403822807431221)
                ·
                  refine ⟨4808874585412858388196677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51294662244403822807431221 4808874585412858388196677)
                  ·
                    refine ⟨901663984764910947786877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4808874585412858388196677 901663984764910947786877)
                    ·
                      rfl

theorem cell23_5267953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_5267953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267953 prefixEnd_5267953 := by exact prefixLift 5267953
  have htrace : WordTrace (prefixWord ++ tailWord_5267953) baseStart_5267953 baseEnd_5267953 := by
    simpa [prefixWord, tailWord_5267953, baseEnd_5267953] using wordTrace_append hprefix tailTrace_5267953
  have hstable : (prefixWord ++ tailWord_5267953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267953).length < 2 ^ (prefixWord ++ tailWord_5267953).sum := by decide
  have hdescent : baseEnd_5267953 < baseStart_5267953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267957 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5267957 : Nat := 118140960795 + 5267957 * 2 ^ 59
def prefixEnd_5267957 : Nat := 4983230072969 + 3 ^ 40 * 5267957 * 2
def baseEnd_5267957 : Nat := 901664669405783609236871

theorem tailTrace_5267957 : CollatzResearch.WordTrace tailWord_5267957 prefixEnd_5267957 901664669405783609236871 := by
  unfold tailWord_5267957
  simp only [CollatzResearch.WordTrace]
  refine ⟨192138176576098959272298125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128092117717399306181532083 192138176576098959272298125)
  ·
    refine ⟨72051816216037109727111797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192138176576098959272298125 72051816216037109727111797)
    ·
      refine ⟨6754857770253479036916731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72051816216037109727111797 6754857770253479036916731)
      ·
        refine ⟨10132286655380218555375097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754857770253479036916731 10132286655380218555375097)
        ·
          refine ⟨7599214991535163916531323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10132286655380218555375097 7599214991535163916531323)
          ·
            refine ⟨11398822487302745874796985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7599214991535163916531323 11398822487302745874796985)
            ·
              refine ⟨8549116865477059406097739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11398822487302745874796985 8549116865477059406097739)
              ·
                refine ⟨12823675298215589109146609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8549116865477059406097739 12823675298215589109146609)
                ·
                  refine ⟨9617756473661691831859957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12823675298215589109146609 9617756473661691831859957)
                  ·
                    refine ⟨901664669405783609236871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9617756473661691831859957 901664669405783609236871)
                    ·
                      rfl

theorem cell23_5267957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5267957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267957 prefixEnd_5267957 := by exact prefixLift 5267957
  have htrace : WordTrace (prefixWord ++ tailWord_5267957) baseStart_5267957 baseEnd_5267957 := by
    simpa [prefixWord, tailWord_5267957, baseEnd_5267957] using wordTrace_append hprefix tailTrace_5267957
  have hstable : (prefixWord ++ tailWord_5267957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267957).length < 2 ^ (prefixWord ++ tailWord_5267957).sum := by decide
  have hdescent : baseEnd_5267957 < baseStart_5267957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267974 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5267974 : Nat := 118140960795 + 5267974 * 2 ^ 59
def prefixEnd_5267974 : Nat := 4983230072969 + 3 ^ 40 * 5267974 * 2
def baseEnd_5267974 : Nat := 901667579129492420399345

theorem tailTrace_5267974 : CollatzResearch.WordTrace tailWord_5267974 prefixEnd_5267974 901667579129492420399345 := by
  unfold tailWord_5267974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6004337394282417849239593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128092531078024914117111317 6004337394282417849239593)
  ·
    refine ⟨4503253045711813386929695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6004337394282417849239593 4503253045711813386929695)
    ·
      refine ⟨6754879568567720080394543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4503253045711813386929695 6754879568567720080394543)
      ·
        refine ⟨10132319352851580120591815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754879568567720080394543 10132319352851580120591815)
        ·
          refine ⟨15198479029277370180887723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132319352851580120591815 15198479029277370180887723)
          ·
            refine ⟨22797718543916055271331585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15198479029277370180887723 22797718543916055271331585)
            ·
              refine ⟨17098288907937041453498689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22797718543916055271331585 17098288907937041453498689)
              ·
                refine ⟨12823716680952781090124017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17098288907937041453498689 12823716680952781090124017)
                ·
                  refine ⟨9617787510714585817593013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12823716680952781090124017 9617787510714585817593013)
                  ·
                    refine ⟨901667579129492420399345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9617787510714585817593013 901667579129492420399345)
                    ·
                      rfl

theorem cell23_5267974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5267974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267974 prefixEnd_5267974 := by exact prefixLift 5267974
  have htrace : WordTrace (prefixWord ++ tailWord_5267974) baseStart_5267974 baseEnd_5267974 := by
    simpa [prefixWord, tailWord_5267974, baseEnd_5267974] using wordTrace_append hprefix tailTrace_5267974
  have hstable : (prefixWord ++ tailWord_5267974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267974).length < 2 ^ (prefixWord ++ tailWord_5267974).sum := by decide
  have hdescent : baseEnd_5267974 < baseStart_5267974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5267980 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_5267980 : Nat := 118140960795 + 5267980 * 2 ^ 59
def prefixEnd_5267980 : Nat := 4983230072969 + 3 ^ 40 * 5267980 * 2
def baseEnd_5267980 : Nat := 2705005818272404237723007

theorem tailTrace_5267980 : CollatzResearch.WordTrace tailWord_5267980 prefixEnd_5267980 2705005818272404237723007 := by
  unfold tailWord_5267980
  simp only [CollatzResearch.WordTrace]
  refine ⟨96069507727507817100192697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128092676970010422800256929 96069507727507817100192697)
  ·
    refine ⟨72052130795630862825144523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96069507727507817100192697 72052130795630862825144523)
    ·
      refine ⟨108078196193446294237716785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72052130795630862825144523 108078196193446294237716785)
      ·
        refine ⟨81058647145084720678287589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108078196193446294237716785 81058647145084720678287589)
        ·
          refine ⟨15198496339703385127178923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81058647145084720678287589 15198496339703385127178923)
          ·
            refine ⟨22797744509555077690768385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15198496339703385127178923 22797744509555077690768385)
            ·
              refine ⟨17098308382166308268076289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22797744509555077690768385 17098308382166308268076289)
              ·
                refine ⟨12823731286624731201057217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17098308382166308268076289 12823731286624731201057217)
                ·
                  refine ⟨9617798464968548400792913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12823731286624731201057217 9617798464968548400792913)
                  ·
                    refine ⟨7213348848726411300594685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9617798464968548400792913 7213348848726411300594685)
                    ·
                      refine ⟨2705005818272404237723007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7213348848726411300594685 2705005818272404237723007)
                      ·
                        rfl

theorem cell23_5267980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_5267980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5267980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5267980 prefixEnd_5267980 := by exact prefixLift 5267980
  have htrace : WordTrace (prefixWord ++ tailWord_5267980) baseStart_5267980 baseEnd_5267980 := by
    simpa [prefixWord, tailWord_5267980, baseEnd_5267980] using wordTrace_append hprefix tailTrace_5267980
  have hstable : (prefixWord ++ tailWord_5267980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5267980).length < 2 ^ (prefixWord ++ tailWord_5267980).sum := by decide
  have hdescent : baseEnd_5267980 < baseStart_5267980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5267980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268014 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_5268014 : Nat := 118140960795 + 5268014 * 2 ^ 59
def prefixEnd_5268014 : Nat := 4983230072969 + 3 ^ 40 * 5268014 * 2
def baseEnd_5268014 : Nat := 2705023276614657104697851

theorem tailTrace_5268014 : CollatzResearch.WordTrace tailWord_5268014 prefixEnd_5268014 2705023276614657104697851 := by
  unfold tailWord_5268014
  simp only [CollatzResearch.WordTrace]
  refine ⟨24017531942111557250890387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128093503691261638671415397 24017531942111557250890387)
  ·
    refine ⟨36026297913167335876335581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24017531942111557250890387 36026297913167335876335581)
    ·
      refine ⟨13509861717437750953625843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36026297913167335876335581 13509861717437750953625843)
      ·
        refine ⟨20264792576156626430438765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13509861717437750953625843 20264792576156626430438765)
        ·
          refine ⟨7599297216058734911414537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20264792576156626430438765 7599297216058734911414537)
          ·
            refine ⟨5699472912044051183560903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7599297216058734911414537 5699472912044051183560903)
            ·
              refine ⟨8549209368066076775341355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699472912044051183560903 8549209368066076775341355)
              ·
                refine ⟨12823814052099115163012033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8549209368066076775341355 12823814052099115163012033)
                ·
                  refine ⟨9617860539074336372259025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12823814052099115163012033 9617860539074336372259025)
                  ·
                    refine ⟨7213395404305752279194269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9617860539074336372259025 7213395404305752279194269)
                    ·
                      refine ⟨2705023276614657104697851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7213395404305752279194269 2705023276614657104697851)
                      ·
                        rfl

theorem cell23_5268014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_5268014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268014 prefixEnd_5268014 := by exact prefixLift 5268014
  have htrace : WordTrace (prefixWord ++ tailWord_5268014) baseStart_5268014 baseEnd_5268014 := by
    simpa [prefixWord, tailWord_5268014, baseEnd_5268014] using wordTrace_append hprefix tailTrace_5268014
  have hstable : (prefixWord ++ tailWord_5268014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268014).length < 2 ^ (prefixWord ++ tailWord_5268014).sum := by decide
  have hdescent : baseEnd_5268014 < baseStart_5268014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
